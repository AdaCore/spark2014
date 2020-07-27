package Generic_Bounded_String is

   type Bounded_String_Base is private;

   subtype Bounded_String is Bounded_String_Base
   with Dynamic_Predicate => True;

private

   type Bounded_String_Base is record
      Dummy : Integer;
   end record;

end Generic_Bounded_String;
