package P
   with SPARK_Mode
is

   type Vect is array (Natural range <>) of Integer;

   procedure Swap(V: in out Vect; I, J : Natural)
     with
       Pre  => I in V'Range and J in V'Range,
       Post => V = V'Old'Update (I => V'Old(J), J => V'Old(I));

end P;
