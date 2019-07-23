with Types; use Types;

package Nonlinear with
  SPARK_Mode
is
   --  from J506-016 (industrial user)
   procedure Scale (X, Y, Z : Natural_32; Res : out Natural_32);
   procedure Unsigned_Scale (X, Y, Z : Unsigned_32; Res : out Unsigned_32);

   --  from M118-036 (example for teaching)
   procedure Divide (X, Y : Positive_32; Res : out Positive_32);

   --  from M328-009 (example for teaching)
   procedure Power (X : Natural);

   --  from NA05-006 (example for teaching)
   procedure Mult (X, Y : Integer; Res : out Integer);

   --  from NB26-002 (industrial user)
   procedure Mult_Protect (X, Y, Z : Natural_32; Res : out Integer_32);

end Nonlinear;
