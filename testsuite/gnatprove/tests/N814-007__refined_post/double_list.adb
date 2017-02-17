package body Double_List
with
  Refined_State => (Internal_List => (Memory, Count, Free_List, Free))
is

   type List_Node is
      record
         Value    : Element_Type;
         Next     : Index_Type;
         Previous : Index_Type;
      end record;

   type Node_Array is array (Index_Type) of List_Node;
   type Free_Array is array (Index_Type) of Index_Type;

   Memory    : Node_Array;  -- Holds the list nodes.
   Count     : Index_Type;  -- Number of items on the list.
   Free_List : Free_Array;  -- Maps available nodes.
   Free      : Index_Type;  -- Points at the head of the free list.

   procedure Clear
      with
         Refined_Global => (Output => (Memory, Count, Free_List, Free)),
         Refined_Depends => ((Memory, Count, Free_List, Free) => null),
         Refined_Post => Count = 0
   is
   begin
      -- Make sure the entire array has some appropriate initial value.
      Memory := (others => (Default_Element, 0, 0));
      Count := 0;

      -- Prepare the free list.
      Free_List := (others => 0);
      Free := 1;
      for Index in Index_Type range 1 .. Index_Type'Last - 1 loop
         Free_List (Index) := Index + 1;
      end loop;
   end Clear;


   procedure Insert_Before (It     : in Iterator;
                            Item   : in Element_Type;
                            Status : out Status_Type)
      with
         Refined_Global => (Input => Free_List,
                            In_Out => (Memory, Count, Free)),
         Refined_Depends => (Memory =>+ (Count, It, Item, Free),
                             (Count, Status) => Count,
                              Free           =>+ (Count, Free_List))
   is
      New_Pointer : Index_Type;
   begin
      if Count = Max_Size then
         Status := Insufficient_Space;
      else
         Status := Success;

         -- Get an item from the free list.
         New_Pointer := Free;
         Free        := Free_List(Free);

         -- Fill in the fields and link the new item into the list.
         Memory(New_Pointer) := (Item, It.Pointer, Memory(It.Pointer).Previous);
         Memory(Memory(It.Pointer).Previous).Next := New_Pointer;
         Memory(It.Pointer).Previous := New_Pointer;

         -- Adjust count.
         Count := Count + 1;
      end if;
   end Insert_Before;


   function Back return Iterator is
   begin
      return (Pointer => 0);
   end Back;


   --function Size return Natural is (Count)
   --  with
   --    Refined_Global => (Input => Count);

   function Size return Natural
     with
       Refined_Global => (Input => Count),
       Refined_Post => Size'Result = Count
   is
   begin
      return Count;
   end Size;

begin
   -- Clear the list at package elaboration time.
   Clear;
end Double_List;

