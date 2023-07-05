procedure Inst is

  type A_Subtype is null record
    with Dynamic_Predicate => False;

  X : A_Subtype; --@PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL

begin
   null;
end;
