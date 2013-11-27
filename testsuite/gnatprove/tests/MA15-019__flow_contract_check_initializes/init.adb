package body Init
  with SPARK_Mode,
       Refined_State => (State => (B, C, D))
is
   C : Integer := A;  --  OK
   D : Integer := B;  --  OK

   function Sum_State return Integer is (B + C + D)
     with Refined_Global => (B, C, D);

   function Sum_All return Integer is (A + B + C + D)
     with Refined_Global => (A, B, C, D);
end Init;
