package body Q
  with Refined_State => (State => A)
is
   pragma SPARK_Mode (Off);
   A : Integer;
   procedure Dummy is null;
end;
