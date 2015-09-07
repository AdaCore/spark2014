package Searchers
  with SPARK_Mode => On
is
   subtype Index_Type is Positive range 1 .. 100;
   type Array_Type is array(Index_Type) of Integer;

   procedure Binary_Search (Search_Item : in  Integer;
                            Items       : in  Array_Type;
                            Found       : out Boolean;
                            Result      : out Index_Type)
      with
         Pre =>
            (for all J in Items'Range =>
               (for all K in J + 1 .. Items'Last => Items(J) <= Items(K)));
end Searchers;
