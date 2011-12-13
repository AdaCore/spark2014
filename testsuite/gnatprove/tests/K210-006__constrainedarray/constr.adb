package body Constr is
   procedure Incr_Ar (X : in out One_Ten_Vect)
   is
   begin
      for I in 1 .. 10 loop
         X (I) := X(I) + 1;
      end loop;
   end Incr_Ar;
end Constr;
