procedure Rep_Clause is
begin
   type T is range 1 .. 10;
   X : Boolean;
   for T'Size use 7;
end Rep_Clause;
