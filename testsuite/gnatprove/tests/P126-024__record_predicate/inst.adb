procedure Inst is

  type A_Subtype is null record
    with Dynamic_Predicate => False;

  X : A_Subtype;

begin
   null;
end;
