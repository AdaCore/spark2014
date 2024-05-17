package P_Initial is

   subtype Index is Integer range 1 .. 10;
   type Table is array (Index range <>) of Integer;

   function Is_Sorted (T : Table) return Boolean is
     (for all J in T'Range =>
        (if J /= T'Last then T(J) <= T(J+1)));

   function Is_Sorted_Alt (T : Table) return Boolean is
     (for all J in T'Range =>
        (for all K in T'Range =>
           (if J <= K then T(J) <= T(K))));

end P_Initial;
