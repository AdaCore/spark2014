package Depends_Illegal_2
  with SPARK_Mode,
       Abstract_State => A
is
   procedure P1 (Par1 : in Natural);

   procedure P2
     with Global  => (Output => A),
          Depends => (A => null);
end Depends_Illegal_2;
