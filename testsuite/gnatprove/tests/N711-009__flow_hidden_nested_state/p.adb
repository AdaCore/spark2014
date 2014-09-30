package body P
  with Refined_State => (State => G)
is
   G : Integer := 0;

   package Nest
     --  with Abstract_State => Nested_State
   is
      function Foo return Integer;
   private
      Pr_Var : Integer := 0;
   end Nest;

   package body Nest
     --  with Refined_State => (Nested_State => GN)
   is
      GN : Integer := 0;

      function Foo return Integer is (GN + Pr_Var);
   end Nest;

   function Add (X, Y : Integer) return Integer is
   begin
      pragma Assert (G = 0 + Nest.Foo);
      return X + Y;
   end Add;
end P;
