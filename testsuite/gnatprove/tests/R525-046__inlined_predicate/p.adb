with Ada.Dispatching;

procedure P is

   function Foo return Boolean is
   begin
      Ada.Dispatching.Yield;
      return True;
   end Foo;

   type T is record
      Dummy : Integer := 0;
   end record
   with Dynamic_Predicate => Foo or else T.Dummy = 0;

   X : T;

begin
   null;
end P;
