----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

with UDP_DNS_Package,
     TCP_DNS_Package,
     Spark_Ada_Command_Line,
     SPARK.Text_IO,
     DNS_Table_Pkg,
     Zone_File_Io;

procedure Spark_Dns_Main
  with Global  => (Input  => Spark_Ada_Command_Line.State,
                   Output => (TCP_DNS_Package.Startup_Suspension,
                              UDP_DNS_Package.Startup_Suspension),
                   In_Out => DNS_Table_Pkg.DNS_Table),
       Depends => (DNS_Table_Pkg.DNS_Table =>+ Spark_Ada_Command_Line.State,
                   (TCP_DNS_Package.Startup_Suspension,
                    UDP_DNS_Package.Startup_Suspension) => null)
is
   Success : Boolean;
--   Error : constant String := "Error--please shut down and correct zone file";
--   Good : constant String := "Correct zone file";
   pragma Priority(0);
   ZoneFile : SPARK.Text_IO.File_type;
begin
   Spark_Ada_Command_Line.Create_File_From_Argument (1, ZoneFile);
   Zone_File_IO.ProcessZoneFile (ZoneFile, Success);

   if not Success then
      Spark_Ada_Command_Line.Exit_With_Status (Spark_Ada_Command_Line.Failure);
   end if;
   TCP_DNS_Package.Initialization_Done;
   UDP_DNS_Package.Initialization_Done;
end Spark_Dns_Main;
