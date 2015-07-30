package Types
  with SPARK_Mode => On
is
   -- Types to support other test cases.

   type S1 is range 1 .. 10; -- no default value

   type S2 is range 1 .. 10
     with Default_Value => 3;

   type Colour is (Red, Green, Blue)
     with Default_Value => Green;

   type FR is record -- both fields default initialized
      F1 : S2;
      F2 : Colour;
   end record;

   type AR is array (S1) of Integer
     with Default_Component_Value => 5;

end Types;
