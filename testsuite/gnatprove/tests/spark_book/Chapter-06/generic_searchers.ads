pragma SPARK_Mode(On);
package Generic_Searchers is

   generic
      type Element_Type is private;
      type Index_Type   is range <>;
      type Array_Type   is array(Index_Type) of Element_Type;
      with function "<"(L, R : Element_Type) return Boolean is <>;
   procedure Binary_Search (Search_Item : in  Element_Type;
                            Items       : in  Array_Type;
                            Found       : out Boolean;
                            Result      : out Index_Type)
     with
       Pre  => (for all J in Items'Range =>
                 (for all K in J + 1 .. Items'Last => Items (J) < Items (K))),
       Post => (if Found then
                   Search_Item = Items (Result)
                else
                   (for all J in Items'Range => Items (J) /= Search_Item));

end Generic_Searchers;
