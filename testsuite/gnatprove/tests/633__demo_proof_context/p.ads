package P is

   subtype Index is Integer;
   type Table is array (Index range <>) of Integer;

   function Is_Sorted (T : Table) return Boolean is
     (for all J in T'Range =>
        (if J /= T'Last then T(J) <= T(J+1)))
   with Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   procedure Lemma_Prove_Sorted_Alt (T : Table)
   with
     Ghost,
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre  => Is_Sorted (T),
     Post => Is_Sorted_Alt (T);

   function Is_Sorted_Alt (T : Table) return Boolean is
     (for all J in T'Range =>
        (for all K in T'Range =>
           (if J <= K then T(J) <= T(K))))
   with Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

end P;
