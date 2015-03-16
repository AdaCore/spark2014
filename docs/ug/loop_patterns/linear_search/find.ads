with Table_Types; use Table_Types;
package Find
  with SPARK_Mode
is

   function Find_Slot (Table        : Table_T;
                       Search_Start : Ident_T) return Opt_Ident_T with
             --  The found slot fulfills the search criterion (not exists).
     Post => (if Find_Slot'Result in Ident_T then
                not Table (Find_Slot'Result). Exists);

end Find;
