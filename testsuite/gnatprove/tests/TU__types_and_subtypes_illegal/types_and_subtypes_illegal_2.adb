package body Types_And_Subtypes_Illegal_2
  with Refined_State => (State => B)
is
   B : constant Integer := 0;

   function Get_A return Integer is (A);

   procedure Increase (X : in out Integer)
     with Refined_Depends => (X =>+ (A, B))
   is
   begin
      X := X + A + B;
   end Increase;
end Types_And_Subtypes_Illegal_2;
