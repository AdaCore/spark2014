package body Nested_Pkg
  with Refined_State => (Foobar => Z.State)
is


   function G return Boolean is (True);

   package Z
     with Abstract_State => State,
          Initializes    => State
   is

      function H return Boolean with Global => State;
   end Z;

   package body Z
     with Refined_State => (State => (Foo, Bar))
   is
      Foo : Boolean := False;
      Bar : Boolean := True;

      function H return Boolean is (Bar) with Refined_Global => Bar;
   end Z;

   package X is
      function F return Boolean;

      procedure Wibble
        with Global => Z.State,
             Pre    => G and Z.H;
   end X;

   package body X is
      function F return Boolean is (True);

      procedure Wibble is
      begin
         --  precondition. g body is visible
         --  precondition. h spec is visible
         null;
      end Wibble;

      procedure Test
        with Global => Z.State
      is
      begin
         pragma Assert (F);  --  body visible

         pragma Assert (G);  --  body visible

         Wibble;             --  body visible
      end Test;

   end X;

   procedure Test
     with Global => Z.State
   is
   begin
      pragma Assert (X.F);   --  spec visible

      pragma Assert (G);     --  body visible

      X.Wibble;              --  spec visible
   end Test;

end Nested_Pkg;
