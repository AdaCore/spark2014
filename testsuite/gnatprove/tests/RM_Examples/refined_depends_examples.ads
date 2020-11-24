package Refined_Depends_Examples
  with SPARK_Mode,
       Abstract_State => State
is
   procedure P1_1 (I : in Integer)
     with Global  => (In_Out => State),
          Depends => (State =>+ I);

   procedure P1_2 (I : in Integer)
     with Global  => (In_Out => State),
          Depends => (State =>+ I);

   procedure P1_3 (Result : out Integer)
     with Global  => (Input => State),
          Depends => (Result => State);

   procedure P1_4 (I : in Integer)
     with Global  => (Output => State),
          Depends => (State => I);

end Refined_Depends_Examples;
