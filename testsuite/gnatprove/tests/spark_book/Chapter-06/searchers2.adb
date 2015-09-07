package body Searchers2
  with SPARK_Mode => On
is

   procedure Binary_Search (Search_Item : in  Integer;
                            Items       : in  Array_Type;
                            Found       : out Boolean;
                            Result      : out Index_Type) is

      Low_Index  : Index_Type := Items'First;
      Mid_Index  : Index_Type;
      High_Index : Index_Type := Items'Last;
   begin
      Found  := False;
      Result := Items'First;  -- Initialize Result to "not found" case.

      -- If the item is out of range, it is not found.
      if Search_Item < Items(Low_Index) or Items(High_Index) < Search_Item then
         return;
      end if;

      loop
         Mid_Index := (Low_Index + High_Index) / 2;
         if Search_Item = Items(Mid_Index) then
            Found  := True;
            Result := Mid_Index;
            return;
         end if;

         exit when Low_Index = High_Index;

         pragma Loop_Invariant
           (Search_Item in Items(Low_Index) .. Items(High_Index));

         if Items(Mid_Index) < Search_Item then
            Low_Index := Mid_Index;
         else
            High_Index := Mid_Index;
         end if;

      end loop;
   end Binary_Search;

end Searchers2;
