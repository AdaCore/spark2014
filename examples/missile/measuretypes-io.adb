-- I/O for measuretypes
--
-- $Log: measuretypes-io.adb,v $
-- Revision 1.1  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
--
with measuretypes;
package body Measuretypes.io is
   function Millirad(r : in measuretypes.millirad) return String
   is
   begin
      return measuretypes.millirad'image(r);
   end Millirad;

end Measuretypes.io;
