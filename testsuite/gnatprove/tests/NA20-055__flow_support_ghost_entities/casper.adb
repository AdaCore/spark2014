package body Casper is
   procedure Ghost_Proc (Par : out Integer) is
   begin
      Par := G1 + G2;  --  This is legal.
   end Ghost_Proc;

   procedure P (Par : out Integer) is
      Tmp : Integer := G2 + 1  --  This is not ineffective.
        with Ghost;
   begin
      pragma Assert (Tmp > G2);
      Par := G1;
      Ghost_G1 := G2;  --  This is fine provided G2 is Input
   end P;

   package body Nested_Ghost_Package
     with Refined_State => (Nested_State => Nested_Hidden_Var)
   is
      Nested_Hidden_Var : Integer := 5;

      function Is_OK (Par : Integer) return Boolean is
        (Par < Nested_Hidden_Var)
        with Refined_Global => Nested_Hidden_Var;
   end Nested_Ghost_Package;
end Casper;
