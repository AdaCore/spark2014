procedure P is

   type T_Bool is new Boolean with Predicate => True;
   type T_Int  is new Integer with Predicate => True;
   type T_Rec1 is null record with Predicate => True;
   type T_Rec2 is record
      C : Integer;
   end record with Predicate => True;

   B  : T_Bool;
   J  : T_Int;
   R1 : T_Rec1;
   R2 : T_Rec2;

begin
   null;
end;
