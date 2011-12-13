procedure Pack is
   type E is (A, B);
   type Ar is array (Boolean) of E;

   X : constant Ar := (True => A, False => B);
begin
   null;
end Pack;
