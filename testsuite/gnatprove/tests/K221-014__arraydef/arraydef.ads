package Arraydef is
   type MyInt is range 1 .. 10;
   type One_Ten_Vect is array(MyInt) of Integer;

   procedure Incr_Ar (X : in out One_Ten_Vect);
end Arraydef;
