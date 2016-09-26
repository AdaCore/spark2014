procedure P (X : out Integer) with Global => null is
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

--  P531-027 regression: the global annotation pm P should not be necessary
