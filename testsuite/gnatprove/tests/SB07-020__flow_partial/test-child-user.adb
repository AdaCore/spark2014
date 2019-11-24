package body Test.Child.User
is

   procedure Set (Index : Range_Type; Value : Integer)
   is
   begin
      Elems (Index).Pos := Value;
   end Set;

end Test.Child.User;
