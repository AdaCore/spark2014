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

with Spark.Text_IO,
     DNS_Table_Pkg;

package Zone_File_IO is
   procedure ProcessZoneFile
     (ZoneFile : in out Spark.Text_IO.File_Type;
      Success  :    out Boolean)
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => ((DNS_Table_Pkg.DNS_Table,
                     Success,
                     ZoneFile) => (DNS_Table_Pkg.DNS_Table, ZoneFile));
end Zone_File_IO;
