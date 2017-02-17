---------------------------------------------------------------------------
-- FILE    : remote_access.adb
-- SUBJECT : Package providing AWS support for Thumper.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin and Ian Schulze
--
-- This package contains the necessary callbacks for Thumper's embedded web server.
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Ada.Text_IO;
with AWS.Messages;
with AWS.MIME;      use AWS.MIME;
with AWS.Response;
with AWS.Server;    use AWS.Server;
with AWS.Status;    use AWS.Status;
with AWS.Utils;     use AWS.Utils;

with Data_Storage;       use Data_Storage;
with Hermes.OID;         use Hermes.OID;
with Serial_Generator;   use Serial_Generator;
with Timestamp_Messages; use Timestamp_Messages;

package body Remote_Access is

   -- Server declaration
   Web_Server : AWS.Server.HTTP;

   -- TODO (SECURITY): Make sure the URI does not contain any ".." elements.
   -- NOTE: AWS might already be doing this.
   function To_File_Name(URI : String) return String
     with Pre => URI'Length > 0
   is
      -- TODO: Make the base URI configurable.
      Base_URI : constant String := "../../../TestHTML";
   begin
      if URI(URI'Last) = '/' then
         return Base_URI & URI & "index.html";
      else
         return Base_URI & URI;
      end if;
   end To_File_Name;


   function Service(Request : AWS.Status.Data) return AWS.Response.Data is
      URI : constant String := AWS.Status.URI(Request);
      File_Name : constant String := To_File_Name(URI);

      HTML_File_Head: constant String := "<html><head>";
      HTML_Body: constant String := "<body>";
      HTML_File_End: constant String := "</body></html>";

      Count_File_Begin: constant String :=
        "<title>Count of time stamps</title></head><body>The count is ";
      Count_File_End: constant String := "!</body></html>";
      Result_File_Begin: constant String := "<title>Timestamp:</title>";
      Stamp_File_Begin: constant String :=
        "<html><head><title>Timestamp</title></head><body>The timestamp is ";

      Hash : Hermes.Octet_Array(1 .. Hash_Size);
      Generalized_Time : Hermes.Octet_Array(1 .. 14) := (others => 0);

      function To_Hex(Byte : Hermes.Octet) return String is
         use type Hermes.Octet;
         Result : String (1 .. 2);
         Lookup : array (Hermes.Octet range 0 .. 15) of Character :=
           ('0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F');
      begin
         Result(1) := Lookup(Byte / 16);
         Result(2) := Lookup(Byte rem 16);
         return Result;
      end;

      function Hash_Conversion(Raw_Hash : Hermes.Octet_Array) return String is
         Workspace : String (1 .. (2*Hash_Size));
      begin
         for I in Raw_Hash'Range loop
            Workspace(2*(I - Raw_Hash'First) + 1 .. 2*(I - Raw_Hash'First) + 2) :=
              To_Hex(Raw_Hash(I));
         end loop;
         return Workspace;
      end;

   begin  -- Service

      -- TODO: Log requests and other information somehwere. Remove dependency on Ada.Text_IO.
      Ada.Text_IO.Put_Line("Requested URI: " & URI);

      if URI = "/count.html" then
         return AWS.Response.Build
           (Text_HTML, Count_File_Begin & Count_Type'Image(Timestamp_Count) & Count_File_End);

      elsif URI = "/submit.html" then
         Ada.Text_IO.Put_Line(Parameter(Request, "SerialNumber"));
         -- TODO: It would probably be better to use AWS's templating mechanism.
         return AWS.Response.Build
           (Text_HTML,
            HTML_File_Head &
              Result_File_Begin &
              HTML_Body &
              "Serial number is: " &
              Parameter(Request, "SerialNumber") &
              HTML_File_End);

      elsif URI = "/serialtest.html" then
         declare
            Timestamps : Timestamp_Array :=
              Timestamp_Retrieve(Serial_Number_Type'Value(Parameter(Request, "SerialNumber")));
         begin
            Hash := Timestamps(1).Hashed_Message;
            Generalized_Time := Timestamps(1).Generalized_Time;
         end;
         return AWS.Response.Build
           (Text_HTML,
            HTML_File_Head &
              Result_File_Begin &
              HTML_Body &
              "Hash is: " &
              Hash_Conversion(Hash) &
              HTML_File_End);

      elsif AWS.Utils.Is_Regular_File(File_Name) then
         return AWS.Response.File
           (Content_Type => Content_Type(File_Name), Filename => File_Name);

      else
         return AWS.Response.Acknowledge(AWS.Messages.S404, "<p>Not found: " & URI & "</p>");
      end if;
   end Service;


   procedure Initialize is
   begin
      -- Basic logger
      -- TODO: Use a real logger.
      Ada.Text_IO.Put_Line("**** AWS Started! ****");

      -- Start the server
      AWS.Server.Start(Web_Server, "Web_Server", Service'Access, Port => 8000);
      return;
   end Initialize;


   procedure Shutdown is
   begin
      -- Log Shutdown
      -- TODO: Use a real logger.
      Ada.Text_IO.Put_Line("**** AWS Going Down!! ****");

      -- Shutdown the server
      AWS.Server.Shutdown(Web_Server);
      return;
   end Shutdown;

end Remote_Access;
