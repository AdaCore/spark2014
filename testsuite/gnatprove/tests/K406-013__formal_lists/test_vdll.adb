with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers;
use Ada.Containers;

procedure test_vdll is 
   package VDLL is new Formal_Doubly_Linked_Lists
     (Element_Type => Integer);
   use VDLL;
   L1 :  List (3);
   L2 :  List (3);
   L3 :  List (3);
   L4 :  List (5);
   C :  Cursor;

   Ko : exception;

   function Test_Element
     (Container :  List;
      Position  :  Cursor;
      Result    : Integer) return Boolean
   is
      (Element (Container, Position) = Result);

begin
   --  Has_Element of an empty list
   pragma Assert (not Has_Element (L1, First (L1)));

   --  Has_Element of first
   Insert (Container => L1,
           Before    =>  No_Element,
           New_Item  => 1);
   pragma Assert (Has_Element (L1, First (L1)));

   --  Has_Element of a copy
   L2 :=  Copy (L1, 3);
   pragma Assert (Has_Element (L2, First (L1)));

   --  Has_Element of inserted Element after Insertion
   Append (Container => L2,
           New_Item  => 2);
   pragma Assert (Has_Element (L2, Next (L2, First (L1))));
   pragma Assert (Test_Element (L2, Next (L2, First (L1)), 2));

   --  Has_Element of inserted Element before Insertion
   pragma Assert (not Has_Element (L1, Next (L2, First (L1))));

   --  Has_Element of deleted Element after deletion
   Append (Container => L2, New_Item => 3);
   L1 :=  Copy (Source   => L2, Capacity => 3);
   C :=  Next (L2, First (L2));
   Delete (Container => L2, Position  => C);
   pragma Assert (not Has_Element (L2, Next (L1, First (L1))));

   --  Has_Element of a copy
   L1 :=  Copy (L2, 3);
   pragma Assert (Has_Element (L1, Next (L2, First (L2))));
   pragma Assert (Test_Element (L1, Next (L2, First (L2)), 3));

   Append (Container => L1, New_Item => 4);

   --  Find in range
   pragma Assert (Find (L1, 3, No_Element) =  Next (L1, First (L1)));
   pragma Assert (Find (L1, 4, No_Element) =  Last (L1));
   pragma Assert (Find (L1, 3, No_Element) =  Previous (L1, Last (L1)));

   --  Find out of range
   pragma Assert (Find (L1, 1, Next (L1, First (L1))) =  No_Element);

   --  Length of Left
   L3 :=  Left (Container => L1,
                Position  =>  Next (L1, Next (L1, First (L1))));
   pragma Assert (Length (L3) = 2);

   --  Has_Element of Left in range
   pragma Assert (Has_Element (L3, First (L3)));
   pragma Assert (Test_Element (L3, First (L3), 1));
   pragma Assert (Has_Element (L3, Next (L3, First (L3))));
   pragma Assert (Test_Element (L3, Next (L3, First (L3)), 3));

   --  Has_Element of Left out of range
   pragma Assert (not Has_Element (L3, Next (L1, Next (L3, First (L3)))));

   --  Find of Left in range
   pragma Assert (Find (L3, 3, No_Element) =  Next (L3, First (L3)));
   pragma Assert (Find (L3, 3, No_Element) = Last (L3));
   pragma Assert (Find (L3, 1, No_Element) =  First (L3));
   pragma Assert (Find (L3, 1, No_Element) = Previous (L3, Last (L3)));

   --  Find of Left out of range
   pragma Assert (Find (L3, 1, Next (L3, First (L3))) =  No_Element);

   --  Find of Left invalid
   declare
      E : Cursor;
      pragma Unreferenced (E);
   begin
      --  Precondition should not be provable
      E := Find (L3, 3, Next (L1, Next (L3, First (L3))));
   end;

   --   Copy of Left : Length
   L4 :=  Copy (Left (L1, Next (L1, First (L1))), 5);
   pragma Assert (Length (L4) = 1);

   --  Copy of Left : Has_Element in range
   pragma Assert (Has_Element (L4, First (L4)));
   pragma Assert (Test_Element (L4, First (L4), 1));

   --  Copy of Left : Has_Element out of range
   pragma Assert (not Has_Element (L4, Next (L1, First (L4))));

   --  Copy of Left : Find in range
   pragma Assert (Find (L4, 1, No_Element) =  First (L4));

   --  Copy of Left : Find invalid
   declare
      E : Cursor;
      pragma Unreferenced (E);
   begin
      --  Precondition should not be provable
      E := Find (L4, 3, Next (L1, First (L4)));
   end;

   --  Deleting a cursor after the cut doesn't change Left
   L2 :=  Copy (L1, 3);
   Delete_Last (L2);
   pragma Assert (Strict_Equal (Left (L2, Next (L2, First (L2))),
                         Left (L1, Next (L1, First (L1)))));

   --  Length of Right
   L3 :=  Right (Container => L1, Position  =>  Next (L1, First (L1)));
   pragma Assert (Length (L3) = 2);

   --  Has_Element of Right in range
   pragma Assert (Has_Element (L3, First (L3)));
   pragma Assert (Test_Element (L3, First (L3), 3));
   pragma Assert (Has_Element (L3, Next (L3, First (L3))));
   pragma Assert (Test_Element (L3, Next (L3, First (L3)), 4));

   --  Has_Element of Right out of range
   pragma Assert (not Has_Element (L3, First (L1)));

   --  Find of Right in range
   pragma Assert (Find (L3, 4, No_Element) =  Next (L3, First (L3)));

   --  Find of Right out of range
   pragma Assert (Find (L3, 3, Next (L3, First (L3))) =  No_Element);

   --  Find of Right invalid
   declare
      E : Cursor;
      pragma Unreferenced (E);
   begin
      --  Precondition should not be provable
      E := Find (L3, 3, First (L1));
   end;

   --  Copy of Right : Length
   L4 :=  Copy (Right (L1, Next (L1, Next (L1, First (L1)))), 5);
   pragma Assert (Length (L4) = 1);

   --  Copy of Right : Has_Element in range
   pragma Assert (Has_Element (L4, First (L4)));
   pragma Assert (Test_Element (L4, First (L4), 4));

   --  Copy of Right : Has_Element out of range
   pragma Assert (not Has_Element (L4, Next (L1, First (L1))));

   --  Copy of Right : Find in range
   pragma Assert (Find (L4, 4, No_Element) =  First (L4));

   --  Copy of Right : Find invalid
   declare
      E : Cursor;
      pragma Unreferenced (E);
   begin
      --  Precondition should not be provable
      E := Find (L4, 3, Previous (L1, First (L4)));
   end;

   --  Deleting a cursor before the cut doesn't change Right
   L2 :=  Copy (L1, 3);
   Delete_First (L2);
   pragma Assert (Strict_Equal (Right (L2, First (L2)),
                     Right (L1, Next (L1, First (L1)))));

   Clear (L1);

   for E in 1 .. 3 loop
      Append (L1, E);
   end loop;

   Move (Target => L2, Source => L1);

   declare
      E : Integer;
   begin
      --  Precondition should not be provable
      E := First_Element (L1);
   end;

   declare
      E : Integer;
   begin
      --  Precondition should not be provable
      E := Last_Element (L1);
   end;

end test_vdll;
