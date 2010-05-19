-- Trig for angles
--
-- $Log: measuretypes-angle_ops-trig.adb,v $
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/07 19:35:55  adi
-- Initial revision
--
--
with Ada.Numerics.Generic_Elementary_functions;
package body Measuretypes.Angle_Ops.trig is

   type Trig_Float is digits 4;

   package Math_Fns is new
     Ada.Numerics.Generic_Elementary_Functions(Trig_Float);

   function Arctan2(X, Y : Measuretypes.Meter)
                   return Measuretypes.Angle_Degrees
   is
      -- Normalise x and y
      Na, Nx, Ny : Trig_Float;
      Ans : Measuretypes.Angle_Degrees;
   begin
      if X = 0 and Y = 0 then
         Ans := 0;
      else
         Nx := Trig_Float(X);
         Ny := Trig_Float(Y);
         Na := Math_Fns.Arctan(X => Nx, Y => Ny);
         Ans := Measuretypes.Angle_Degrees(Na);
      end if;
      return Ans;
   end Arctan2;

end Measuretypes.Angle_Ops.trig;

