package body Test.Child.User
is

   function Text (Index : Range_Type) return Integer
   is (Elems (Index).Pos);

end Test.Child.User;
