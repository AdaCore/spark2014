package P is

   task type TT;

   function Not_Reall_True return Boolean is (False);

   subtype S is TT with Dynamic_Predicate => Not_Reall_True;

   T : S;

end;
