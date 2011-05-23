package Subar is
   type One_Twenty is range 1 .. 20;
   subtype One_Ten is One_Twenty range 1 .. 10;

   type A is array (One_Ten) of One_Twenty;

   -- simple subtype
   subtype B is A;

   type C is array (One_Ten) of One_Ten;
   type D is array (One_Twenty) of One_Twenty;
   type E is array (One_Twenty) of One_Ten;

   procedure F (X : A)
      with Pre => (X (1) = 1);

end Subar;
