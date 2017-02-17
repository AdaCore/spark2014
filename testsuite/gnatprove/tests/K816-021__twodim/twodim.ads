package Twodim is

   type One_Ten is range 1 .. 10;
   type One_Twenty is range 1 .. 20;

   type Matrix is array(One_Ten, One_Twenty) of Integer;

   type Any_Matrix is array (Integer range <>, Integer range <>) of Integer;

   function F (M : Matrix; I : One_Ten; K : One_Twenty) return Integer
      with Pre => (M (I,K) = 0);

end Twodim;
