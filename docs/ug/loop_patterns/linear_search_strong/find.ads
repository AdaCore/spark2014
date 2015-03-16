with Table_Types; use Table_Types;
package Find
  with SPARK_Mode
is

   function Find_Slot (Table        : Table_T;
                       Search_Start : Ident_T) return Opt_Ident_T with
             --  The found slot fulfills the search criterion (not exists).
     Post => (if Find_Slot'Result in Ident_T then
                not Table (Find_Slot'Result). Exists) and
             --  Full functional description:
             --  Either the slot is the first found in the first loop ...
             (if Find_Slot'Result in Search_Start .. Ident_T'Last then
                (for all J in Search_Start .. Find_Slot'Result -1 =>
                   Table (J).Exists)
             --  ... or the first occurrence is found in the second loop...
             elsif Find_Slot'Result in Ident_T'First .. Search_Start -1 then
               (for all J in Search_Start .. Ident_T'Last =>
                  Table (J).Exists) and
               (for all J in Ident_T'First .. Find_Slot'Result -1 =>
                  Table (J).Exists)
             --  ... or there was no empty slot.
             else Find_Slot'Result = Null_Ident and
                  (for all J in Ident_T => Table (J).Exists));

end Find;
