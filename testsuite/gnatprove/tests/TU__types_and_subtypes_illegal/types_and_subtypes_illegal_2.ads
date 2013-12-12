package Types_And_Subtypes_Illegal_2
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => (State, A)
is
   --  TU: 3. Constants, including those implicitly declared through a
   --  non-preelaborable subtype declaration shall not be denoted in
   --  Global, Depends, Initializes or Refined_State aspects. [This means
   --  that non-preelaborable subtypes are not taken into account in
   --  determining and checking dependency relations.]
   A : constant Integer := 0;

   function Get_A return Integer
     with Global => A;

   procedure Increase (X : in out Integer)
     with Depends => (X =>+ (A, State));
end Types_And_Subtypes_Illegal_2;
