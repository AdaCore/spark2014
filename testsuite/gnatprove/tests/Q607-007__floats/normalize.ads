package Normalize
with SPARK_Mode
is

   type T_Float32 is digits 6  range -3.40282E+38 .. 3.40282E+38;

   C : constant := 360.0;
   subtype T1 is T_Float32 range -720.0 .. 720.0;
   subtype T2 is T_Float32 range -3.0 .. 2.0;

   function M01 (X : in T1) return T2;
   function M02 (X : in T1) return T2;
   function M03 (X : in T1) return T2;
   function M11 (X : in T1) return T2;
   function M12 (X : in T1) return T2;
   function M13 (X : in T1) return T2;
   function M21 (X : in T1) return T2;
   function M22 (X : in T1) return T2;
   function M23 (X : in T1) return T2;
   function M31 (X : in T1) return T2;
   function M32 (X : in T1) return T2;
   function M33 (X : in T1) return T2;
   function M41 (X : in T1) return T2;
   function M42 (X : in T1) return T2;
   function M43 (X : in T1) return T2;

end Normalize;
