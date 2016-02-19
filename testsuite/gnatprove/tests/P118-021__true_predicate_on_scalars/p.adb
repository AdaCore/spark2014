procedure P is

   type T_Bool is new Boolean with Predicate => True;
   type T_Int  is new Integer with Predicate => True;

   B : T_Bool;
   J : T_Int;

begin
   null;
end;
