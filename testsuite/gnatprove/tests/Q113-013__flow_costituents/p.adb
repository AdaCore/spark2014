package body P with Refined_State => (State => (Nested1.X, Nested1.Nested_Nested1.X, Nested2.X))
is
   package Nested1
     with Initializes => X
   is
      X : Integer;

      package Nested_Nested1
        with Initializes => X
      is
         X : Integer;
      end Nested_Nested1;
   end Nested1;

   package Nested2
     with Initializes => X
   is
      X : Integer;
   end Nested2;

   procedure Foo is null;
end P;
