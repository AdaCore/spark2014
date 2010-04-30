------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with GNAT.IO;

package body Assert is

   procedure Assertion_Failed
     (Message : String;
      File    : String   := GNAT.Source_Info.File;
      Line    : Positive := GNAT.Source_Info.Line)
   is
   begin
      GNAT.IO.Put ("Assertion ");
      GNAT.IO.Put (Message);
      GNAT.IO.Put (" failed at ");
      GNAT.IO.Put (File);
      GNAT.IO.Put (":");
      GNAT.IO.Put (Line);
      GNAT.IO.New_Line;

      raise Program_Error;
   end Assertion_Failed;

   procedure C_Assertion_Failed
     (Message : System.Address;
      File    : System.Address;
      Line    : Interfaces.C.int)
   is
      function Strlen (S : System.Address) return Natural;
      pragma Import (Intrinsic, Strlen, "__builtin_strlen");

      subtype Message_T is String (1 .. Strlen (Message));
      Message_S : Message_T;
      for Message_S'Address use Message;
      pragma Import (Ada, Message_S);

      subtype File_T is String (1 .. Strlen (File));
      File_S : File_T;
      for File_S'Address use File;
      pragma Import (Ada, File_S);

   begin
      Assertion_Failed
        (Message => Message_S, File => File_S, Line => Positive (Line));
   end C_Assertion_Failed;

end Assert;
