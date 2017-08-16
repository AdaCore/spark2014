procedure P (X : out Integer) is
   package Nested
     with Abstract_State => State
   is
      function Foo return Integer
        with Pre => True;
   end Nested;

   package body Nested
     with Refined_State => (State => (Const, Hidden))
   is
      Hidden : Integer          := 0;
      Const  : constant Integer := Hidden;

      function Foo return Integer is (Hidden + Const);
   end Nested;
begin
   X := Nested.Foo;
end P;
