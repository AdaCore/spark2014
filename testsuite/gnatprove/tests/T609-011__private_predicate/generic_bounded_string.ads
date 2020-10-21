package Generic_Bounded_String is

   type A is private;

   subtype B is A
   with Dynamic_Predicate => True;

private

   type A is record
      Dummy : Integer;
   end record;

end Generic_Bounded_String;
