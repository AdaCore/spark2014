with Q;

package body P with SPARK_Mode, Refined_State => (S => R) is
   R : Q.T;
   procedure Flip is null with Refined_Global => (In_Out => R), SPARK_Mode => Off;
end;
