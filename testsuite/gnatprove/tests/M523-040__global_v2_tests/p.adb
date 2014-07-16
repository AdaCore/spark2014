package body P
  with Refined_State => (State => (G, Nest.Nested_State))
is
   G : Integer := 5;

   package Nest
     with Abstract_State => Nested_State
   is
      function Foo return Integer;

      procedure Nest_Initialize;
   end Nest;

   package body Nest
     with Refined_State => (Nested_State => GN)
   is
      GN : Integer;

      function Foo return Integer is
      begin
         return 2 * (GN + 1) - 2;
      end Foo;

      procedure Nest_Initialize is
      begin
         GN := 5;
      end Nest_Initialize;
   end Nest;

   function Add (X, Y : Integer) return Integer is
   begin

      pragma Assert (G = Nest.Foo);
      return X + Y;
   end Add;

   procedure Initialize is
   begin
      Nest.Nest_Initialize;
   end Initialize;
end P;
