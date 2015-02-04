procedure Shift_Range is

   type Ta is mod 2 ** 16;

   function Shift_Right (Left : Ta; Right : Natural) return Ta;
   pragma Import (Intrinsic, Shift_Right);

   type Tb is range 0 .. 255;

   function F (X : Ta) return Tb
      with Global => null;
   --  add a global annotation to avoid inlining of subprogram

   function F (X : Ta) return Tb is
   begin
      return Tb (Shift_Right (X, 8)); --@RANGE_CHECK:PASS
   end F;

   X : Ta := 0;
   Y : Tb := F (X);
begin
   null;
end Shift_Range;
