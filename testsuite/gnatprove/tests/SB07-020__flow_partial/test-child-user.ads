generic
package Test.Child.User
with
   Abstract_State => null
is

   procedure Set (Index : Range_Type; Value : Integer)
   with
      Pre => Kind (Index) and then Used (Index);

end Test.Child.User;
