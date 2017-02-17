package Constr is
   type One_Ten_Vect is array(Integer range 1..10) of Integer;

   procedure Incr_Ar (X : in out One_Ten_Vect)
      with Pre => (X(1) = 0),
           Post => (X(1) = 1);
end Constr;
