with Loop_Types; use Loop_Types;

package P with
  SPARK_Mode
is
   function All_Smaller_Than_Max
     (L : access constant List_Cell; Max : Component_T) return Boolean
   is (L = null or else
         (L.Value <= Max and then All_Smaller_Than_Max (L.Next, Max)))
   with
     Annotate => (GNATprove, Always_Return),
     Subprogram_Variant => (Structural => L);

   function Search_List_Max
     (L : not null access List_Cell) return not null access List_Cell
   with
     Post => All_Smaller_Than_Max (L, Search_List_Max'Result.Value);
end P;
