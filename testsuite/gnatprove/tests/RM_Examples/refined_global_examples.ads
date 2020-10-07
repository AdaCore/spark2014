package Refined_Global_Examples
  with SPARK_Mode,
       Abstract_State => State
is
   procedure P1_1 (I : in Integer)
     with Global => (In_Out => State);

   procedure P1_2 (I : in Integer)
     with Global => (In_Out => State);

   procedure P1_3 (Result : out Integer)
     with Global => (Input => State);

   procedure P1_4 (I : in Integer)
     with Global => (Output => State);

end Refined_Global_Examples;
