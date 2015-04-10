pragma SPARK_Mode (On);

package body Inits_Pragma with
  Refined_State => (S => X)
is
   X : Integer := 10;
end Inits_Pragma;
