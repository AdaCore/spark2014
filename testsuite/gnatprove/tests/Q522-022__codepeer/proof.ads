--with Types; use Types;

package Proof
with SPARK_Mode
is

   type T_Float32 is digits 6;

   function Equal (X1      : in T_Float32;
                   X2      : in T_Float32) return Boolean is
     (abs(X1 - X2) < 4.0E-6)
   with Pre => (X1 <= T_Float32'Last / 2.0) and then
     (X1 >= - T_Float32'Last / 2.0) and then
     (X2 <= T_Float32'Last / 2.0) and then
     (X2 >= - T_Float32'Last / 2.0);

   C_SGS_STEP_VEL : constant T_Float32 := 1.612903E-02;

   subtype T_X1 is T_Float32 range -1.612903E-02 .. 1.612903E-02;
   subtype T_X2 is T_Float32 range -C_SGS_STEP_VEL .. +C_SGS_STEP_VEL;

   subtype T_Y is T_Float32 range -180.0 .. 180.0;

   subtype T_Z is T_Float32 range -0.5 .. 0.5;

   procedure F1 (X : in     T_X1;
                 Y : in     T_Y;
                 Z : in out T_Z);

   procedure F2 (X : in     T_X2;
                 Y : in     T_Y;
                 Z : in out T_Z);

end Proof;
