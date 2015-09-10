---------------------------------------------------------------------------
-- FILE    : client_spark_boundary.adb
-- SUBJECT : Body of a package enclosing the SPARK portion of the client.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package body Client_SPARK_Boundary is

   procedure Fetch_Timestamp
     (Document_File_Name : in String; Timestamp_File_Name : in String) is
   begin
      -- Read the document and compute its hash.
      -- Call Client_Timestamp_Maker.Create_Timestamp
      -- Save the resulting times time stamp (if the above was successful).
      raise Program_Error with "Client_SPARK_Boundary.Fetch_Timestamp not implemented";
   end Fetch_Timestamp;


   function Check_Timestamp
     (Document_File_Name : String; Timestamp_File_Name : String) return Boolean is
   begin
      raise Program_Error with "Client_SPARK_Boundary.Check_Timestamp not implemented";
      return False;
   end Check_Timestamp;


end Client_SPARK_Boundary;
