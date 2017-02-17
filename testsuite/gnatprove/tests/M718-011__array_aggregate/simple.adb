package body Simple is

   function Foo (Init_Val : Integer) return Array_1D is
      Arr : Array_1D := Array_1D'(others => Init_Val + 1);
   begin
      Arr(1) := 10;
      return Arr;
   end Foo;

end Simple;
