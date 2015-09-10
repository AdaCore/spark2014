---------------------------------------------------------------------------
-- FILE    : client_spark_boundary.ads
-- SUBJECT : Specification of a package enclosing the SPARK portion of the client.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package Client_SPARK_Boundary is

   -- TODO: Add SPARK aspects!

   -- This procedure obtains a time stamp for a document and stores it.
   procedure Fetch_Timestamp
     (Document_File_Name : in String; Timestamp_File_Name : in String);

   -- This function returns True if the given time stamp is valid for the specified document.
   function Check_Timestamp
     (Document_File_Name : String; Timestamp_File_Name : String) return Boolean;

end Client_SPARK_Boundary;
