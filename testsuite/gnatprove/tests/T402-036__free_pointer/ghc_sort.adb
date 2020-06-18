pragma SPARK_Mode;
with Ada.Unchecked_Deallocation;

package body GHC_Sort is

   type Int_Array_List_Cell (L : Natural);
   type Int_Array_List is access Int_Array_List_Cell;
   type Int_Array_List_Cell (L : Natural) is record
      Value : Int_Array (1 .. L);
      Next  : Int_Array_List;
   end record;

   procedure Free is new Ada.Unchecked_Deallocation (Int_Array_List_Cell, Int_Array_List);

   procedure Merge_By_Two (L : in out Int_Array_List) is
   begin
      if L = null or else L.Next = null then
         return;
      else
         declare
            New_L : constant Int_Array_List :=
              new Int_Array_List_Cell'
                (L.L + L.Next.L, L.Value & L.Next.Value, L.Next.Next);
         begin
            Free (L.Next);
            Free (L);
            L := New_L;
            Merge_By_Two (L.Next);
         end;
      end if;
   end Merge_By_Two;

   function Sort (S : Int_Array) return Int_Array is
      L : Int_Array_List;
   begin
      return (if L = null then S else L.Value);
   end Sort;

end GHC_Sort;
