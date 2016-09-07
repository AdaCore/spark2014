procedure Main with SPARK_Mode is
   type T_Float32 is digits 6 range -3.40282E+38 .. 3.40282E+38;

   subtype Angle is T_Float32 range 0.0 .. 360.0;

   function T (X : T_Float32) return T_Float32
   is
   begin
      return 3.0 * X;
   end T;

   A : Angle;
begin
   A := T (180.0);
end Main;
