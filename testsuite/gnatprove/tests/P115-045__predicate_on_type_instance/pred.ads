package Pred is

  type A_Type is private;

  subtype A_Subtype is A_Type with Dynamic_Predicate => False;
  --  This type, when used to instantiate a generic package will yield a type
  --  whose object delarations do NOT raise an exception; I think this is
  --  wrong.

private
  type A_Type is record
     Dummy: Integer := 0;
  end record;
end Pred;
