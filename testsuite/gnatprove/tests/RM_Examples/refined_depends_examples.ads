package Refined_Depends_Examples
  with SPARK_Mode,
       Abstract_State => (S1, S2),
       Initializes    => (S1, V1)
is
   V1 : Integer := 0;  -- Visible state variables

   procedure P1_1 (I : in Integer)
     with Global  => (In_Out => S1),
          Depends => (S1 =>+ I);

   procedure P1_2 (I : in Integer)
     with Global  => (In_Out => S1),
          Depends => (S1 =>+ I);

   procedure P1_3 (Result : out Integer)
     with Global  => (Input => S1),
          Depends => (Result => S1);

   procedure P1_4 (I : in Integer)
     with Global  => (Output => S1),
          Depends => (S1 => I);

   procedure P2
     with Global  => (Input  => V1,
                      In_Out => S2),
          Depends => (S2 =>+ V1);

   procedure P3 (J : in Integer)
     with Global  => (Output => V1),
          Depends => (V1 => J);

   procedure P4
     with Global  => (Input => (S1, V1),
                      In_Out => S2),
          Depends => (S2 =>+ (S1, V1));
end Refined_Depends_Examples;
