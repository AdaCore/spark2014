package body Find
  with SPARK_Mode
is

   function Find_Slot (Table        : Table_T;
                       Search_Start : Ident_T) return Opt_Ident_T
   is
      Free_Slot : Opt_Ident_T;
   begin

      Free_Slot := Null_Ident;

      -- Start looking from Search_Start.

      for Slot in Ident_T range
        Search_Start .. Ident_T'Last
      loop
         exit when Free_Slot /= Null_Ident;

         --  So far (until and including Slot -1) the search criterion (an
         --  empty slot) is not fulfilled.
         pragma Loop_Invariant
           (Free_Slot = Null_Ident and
              (for all J in Search_Start .. Slot -1 =>
                 Table (J).Exists));

         if not Table (Slot).Exists then
            Free_Slot := Slot;
         end if;

      end loop;

      --  Wrap round to the beginning.

      for Slot in Ident_T range
        Ident_T'First .. Search_Start - 1
      loop
         exit when Free_Slot /= Null_Ident;

         --  So far (until and including Slot -1) the search criterion (an
         --  empty slot) is not fulfilled.
         pragma Loop_Invariant
           (Free_Slot = Null_Ident and
           (for all J in Ident_T'First .. Slot -1 =>
                 Table (J).Exists));

         if not Table (Slot).Exists then
            Free_Slot := Slot;
         end if;

     end loop;

     return Free_Slot;

   end Find_Slot;

end Find;
