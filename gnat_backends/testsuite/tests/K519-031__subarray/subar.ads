package Subar is
   type One_Twenty is range 1 .. 20;
   subtype One_Ten is One_Twenty range 1 .. 10;

   type A is array (One_Ten) of One_Twenty;

   type C is array (Integer range <>) of One_Ten;

   -- simple subtype
   subtype B is A;

   --  subtype of unconstrained type, without additional bounds
   subtype D is C;
   --  subtype of unconstrained type, with additional bounds
   subtype E is C (Integer range 1..10);

   procedure F (X : A)
      with Pre => (X (1) = 1);

   procedure G (X : C)
      with Pre => (X (X'First) = 1);

end Subar;
