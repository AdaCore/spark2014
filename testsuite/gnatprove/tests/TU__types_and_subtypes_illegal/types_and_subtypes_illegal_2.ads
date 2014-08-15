package Types_And_Subtypes_Illegal_2
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => (State, A)
is
   A : constant Integer := 0;

   function Get_A return Integer
     with Global => A;

   procedure Increase (X : in out Integer)
     with Depends => (X =>+ (A, State));
end Types_And_Subtypes_Illegal_2;
