package Numerics
with SPARK_Mode => On
is
   type T_Base_Float is digits 6 with Size => 32;

   -- Redefinition of float to allow the Ada check to detect overflow
   type T_Float is new T_Base_Float range T_Base_Float'First .. T_Base_Float'Last;

   -- Redefinition of basic operator to suppress overflow check by SPARK and CodePeer
   function "+" (Left : T_Float; Right : T_Float) return T_Float is (T_Float (T_Base_Float (Left) + T_Base_Float (Right))) with Inline, Pre => True;
   pragma Annotate (GNATprove, Intentional, "overflow check might fail", "suppress overflow checks in SPARK analysis");

   function "-" (Left : T_Float; Right : T_Float) return T_Float is (T_Float (T_Base_Float (Left) - T_Base_Float (Right))) with Inline, Pre => True;
   pragma Annotate (GNATprove, Intentional, "overflow check might fail", "suppress overflow checks in SPARK analysis");

   function "*" (Left : T_Float; Right : T_Float) return T_Float is (T_Float (T_Base_Float (Left) * T_Base_Float (Right))) with Inline, Pre => True;

   function "/" (Left : T_Float; Right : T_Float) return T_Float is (T_Float (T_Base_Float (Left) / T_Base_Float (Right))) with Inline, Pre => Right /= 0.0;

end Numerics;
