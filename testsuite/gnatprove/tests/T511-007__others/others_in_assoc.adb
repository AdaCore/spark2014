procedure Others_In_Assoc with SPARK_Mode is
   type My_Array is array (Positive range <>) of Integer;
   function Id (X : Integer) return Integer is (X);
   function No (X : Integer) return Integer is (X) with
     Pre => False;
   A : constant My_Array (1 .. 0) := (for I in others => No (I));
   C : constant My_Array (1 .. 4) := (for I in others => I + Id (I));
begin
   null;
end Others_In_Assoc;
