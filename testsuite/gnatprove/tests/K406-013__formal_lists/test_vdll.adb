with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers;
use Ada.Containers;
with Formal_Container; use Formal_Container;

procedure test_vdll with SPARK_Mode is
   pragma Ghost;
   use VDLL;
   L1 :  List (3);
   L2 :  List (3);
   L3 :  List (3);
   L4 :  List (5);
   C :  Cursor;

   function Test_Element
     (Container :  List;
      Position  :  Cursor;
      Result    : Integer) return Boolean
   is
     (Element (Container, Position) = Result)
   with Pre => Has_Element (Container, Position);

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

   --  Length of First_To_Previous
   L3 := L1;
   Delete_Last (Container => L3);
   pragma Assert (Length (L3) = 2);

   --  Has_Element of First_To_Previous in range
   pragma Assert (Has_Element (L3, First (L3)));
   pragma Assert (Test_Element (L3, First (L3), 1));
   pragma Assert (Has_Element (L3, Next (L3, First (L3))));
   pragma Assert (Test_Element (L3, Next (L3, First (L3)), 3));

   --  Has_Element of First_To_Previous out of range
   pragma Assert (not Has_Element (L3, Next (L1, Next (L3, First (L3)))));

   --  Find of First_To_Previous in range
   pragma Assert (Find (L3, 3, No_Element) =  Next (L3, First (L3)));
   pragma Assert (Find (L3, 3, No_Element) = Last (L3));
   pragma Assert (Find (L3, 1, No_Element) =  First (L3));
   pragma Assert (Find (L3, 1, No_Element) = Previous (L3, Last (L3)));

   --  Find of First_To_Previous out of range
   pragma Assert (Find (L3, 1, Next (L3, First (L3))) =  No_Element);

   --  Find of First_To_Previous invalid
   declare
      E : Cursor;
      pragma Unreferenced (E);
   begin
      --  Precondition should not be provable
      E := Find (L3, 3,                      -- @PRECONDITION:FAIL
                 Next (L1,
                       Next (L3,
                     First (L3))));
      pragma Assert_And_Cut (True);
   end;

   --   Copy of First_To_Previous : Length
   L4 := Copy (L1, L4.Capacity);
   Delete_Last (Container => L4, Count => 2);

   --  Copy of First_To_Previous : Has_Element in range
   pragma Assert (Has_Element (L4, First (L4)));
   pragma Assert (Test_Element (L4, First (L4), 1));

   --  Copy of First_To_Previous : Has_Element out of range
   pragma Assert (not Has_Element (L4, Next (L1, First (L4))));

   --  Copy of First_To_Previous : Find in range
   pragma Assert (Find (L4, 1, No_Element) =  First (L4));

   --  Copy of First_To_Previous : Find invalid
   declare
      E : Cursor;
      pragma Unreferenced (E);
   begin
      --  Precondition should not be provable
      E := Find (L4, 3,               -- @PRECONDITION:FAIL
                 Next (L1,
                       First (L4)));
      pragma Assert_And_Cut (True);
   end;

   --  Deleting a cursor after the cut doesn't change First_To_Previous
   L2 :=  Copy (L1, 3);
   Delete_Last (L2);

   --  Length of Current_To_Last
   L3 := L1;
   Delete_First (Container => L3);
   pragma Assert (Length (L3) = 2);

   --  Has_Element of Current_To_Last in range
   pragma Assert (Has_Element (L3, First (L3)));
   pragma Assert (Test_Element (L3, First (L3), 3));
   pragma Assert (Has_Element (L3, Next (L3, First (L3))));
   pragma Assert (Test_Element (L3, Next (L3, First (L3)), 4));

   --  Has_Element of Current_To_Last out of range
   pragma Assert (not Has_Element (L3, First (L1)));

   --  Find of Current_To_Last in range
   pragma Assert (Find (L3, 4, No_Element) =  Next (L3, First (L3)));

   --  Find of Current_To_Last out of range
   pragma Assert (Find (L3, 3, Next (L3, First (L3))) =  No_Element);

   --  Find of Current_To_Last invalid
   declare
      E : Cursor;
      pragma Unreferenced (E);
   begin
      --  Precondition should not be provable
      E := Find (L3, 3,         -- @PRECONDITION:FAIL
                 First (L1));
      pragma Assert_And_Cut (True);
   end;

   --  Copy of Current_To_Last : Length
   L4 :=  Copy (L1, L4.Capacity);
   Delete_First (L4, 2);
   pragma Assert (Length (L4) = 1);

   --  Copy of Current_To_Last : Has_Element in range
   pragma Assert (Has_Element (L4, First (L4)));
   pragma Assert (Test_Element (L4, First (L4), 4));

   --  Copy of Current_To_Last : Has_Element out of range
   pragma Assert (not Has_Element (L4, Next (L1, First (L1))));

   --  Copy of Current_To_Last : Find in range
   pragma Assert (Find (L4, 4, No_Element) =  First (L4));

   --  Copy of Current_To_Last : Find invalid
   declare
      E : Cursor;
      pragma Unreferenced (E);
   begin
      --  Precondition should not be provable
      E := Find (L4, 3,                    -- @PRECONDITION:FAIL
                 Previous (L1,
                           First (L4)));
      pragma Assert_And_Cut (True);
   end;

   Clear (L1);

   for E in 1 .. 3 loop
      pragma Loop_Invariant (Length (L1) = Count_Type (E - 1));
      Append (L1, E);
   end loop;

   Move (Target => L2, Source => L1);

   declare
      E : Integer;
   begin
      --  Precondition should not be provable
      E := First_Element (L1);   -- @PRECONDITION:FAIL
      pragma Assert_And_Cut (True);
   end;

   declare
      E : Integer;
   begin
      --  Precondition should not be provable
      E := Last_Element (L1);  -- @PRECONDITION:FAIL
      pragma Assert_And_Cut (True);
   end;

end test_vdll;
