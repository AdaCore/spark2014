package Foo with Elaborate_Body
is
   type Base_T is tagged record
      A : Boolean;
   end record;
   type Derived_T is new Base_T with record
      B : Boolean;
   end record;
end Foo;
