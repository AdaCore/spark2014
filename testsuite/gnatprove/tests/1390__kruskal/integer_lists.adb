with Ada.Unchecked_Deallocation;

package body Integer_Lists with SPARK_Mode is

   procedure Free is new Ada.Unchecked_Deallocation (Cell, List);

   ----------
   -- Copy --
   ----------

   function Copy (L : access constant Cell) return List is
   begin
      if L = null then
         return null;
      else
         return new Cell'(Value => L.Value, Next => Copy (L.Next));
      end if;
   end Copy;

   ----------
   -- Push --
   ----------



   --procedure Push (L : in out List; E : Integer) is
   --begin
      --  L (the old list) is "moved" into the Next field of the new
      --  cell, then the New_Arr pointer becomes the list.
     -- L := new Cell'(Value => E, Next => L);
      --end Push;

   --having a procedure prevents me from having a strong post condition on  push unless adding ghost code so I used a function
   --to guarantee solid post conditions

function Push (L : List; Item : Integer) return List is
     (new Cell'(Value => Item, Next => Copy(L)));


   --  Last_elem is defined as an expression function in the spec.

   ---------
   -- Pop --
   ---------

   procedure Pop (L : in out List) is
      Tmp : List := L;     --  move L -> Tmp ; L becomes inaccessible
   begin
      L := Tmp.Next;       --  move Tmp.Next -> L ; Tmp no longer owns the tail
      Free (Tmp);          --  frees the only head cell (no leak)
   end Pop;

   ---------------
   -- Free_List --
   ---------------

   procedure Free_List (L : in out List) is
   begin
      if L /= null then
         Free_List (L.Next);
         Free (L);
      end if;
   end Free_List;

end Integer_Lists;
