package body Arraydef is
   procedure Incr_Ar (X : in out One_Ten_Vect)
   is
   begin
      for I in X'Range loop
         X (I) := X(I) + 1;
      end loop;
   end Incr_Ar;
end Arraydef;
