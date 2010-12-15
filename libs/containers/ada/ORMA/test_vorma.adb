with Ada.Text_IO;
with Ada.Containers.Formal_Ordered_Maps;
with Ada.Containers;
use Ada.Containers;

procedure test_vorma is

   package VORMA is new Formal_Ordered_Maps
     (Key_Type => Integer,
      Element_Type => Integer);
   use VORMA;
   L1 :  Map (3);
   L2 :  Map (3);
   L3 :  Map (3);
   L4 :  Map (5);
   C1 :  Cursor;
   C2 :  Cursor;

   procedure Test_Element (Container :  Map; Position :  Cursor;
                           EResult : Integer; KResult : Integer;
                           Debug_Msg : String);

   procedure Test_Element (Container :  Map; Position :  Cursor;
                           EResult : Integer; KResult : Integer;
                           Debug_Msg : String) is
   begin
      if  Element (Container, Position) = EResult then
         Ada.Text_IO.Put_Line ("OK");
         if  Key (Container, Position) = KResult then
            Ada.Text_IO.Put_Line ("OK");
         else
            Ada.Text_IO.Put (Debug_Msg);
            Ada.Text_IO.Put_Line (" Key => KO ???");
         end if;
      else
         Ada.Text_IO.Put (Debug_Msg);
         Ada.Text_IO.Put_Line (" Element => KO ???");
      end if;
   end Test_Element;

begin

   Ada.Text_IO.Put_Line ("PLAIN :");

   --  Has_Element of first
   Insert (Container => L1,
           New_Item  => 3,
           Key => 1);
   if  Has_Element (L1, First (L1)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L1, First (L1), 3, 1, "Has_Element of first");
   else
      Ada.Text_IO.Put_Line ("Has_Element of first => KO ???");
   end if;

   --  Has_Element of a copy
   L2 :=  Copy (L1, 3);
   if  Has_Element (L2, First (L1)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L2, First (L1), 3, 1, "Has_Element of a copy");
   else
      Ada.Text_IO.Put_Line ("Has_Element of a copy => KO ???");
   end if;

   --  Has_Element of inserted Element after Insertion
   Insert (Container => L1,
           New_Item  => 4,
           Key => 2);
   if  Has_Element (L1, Next (L1, First (L1))) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L1, First (L1), 3, 1,
                    "Has_Element of inserted Element after Insertion");
      Test_Element (L1, Next (L1, First (L1)), 4, 2,
                    "Has_Element of inserted Element after Insertion");
   else
      Ada.Text_IO.Put_Line
        ("Has_Element of inserted Element after Insertion => KO ???");
   end if;

   --  Has_Element of inserted Element before Insertion
   if  Has_Element (L2, Next (L1, First (L1))) then
      Ada.Text_IO.Put_Line
        ("Has_Element of inserted Element before Insertion => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Has_Element of deleted Element after deletion
   Insert (Container => L1, New_Item => 2, Key => 3);
   C1 :=  First (L1);
   C2 :=  First (L1);
   Delete (Container => L1, Position  => C1);
   if  Has_Element (L1, C2) then
      Ada.Text_IO.Put_Line
        ("Has_Element of deleted Element after deletion => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Has_Element of a copy
   L2 :=  Copy (L1, 3);
   if  Has_Element (L2, Next (L1, First (L1))) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L2, Next (L1, First (L1)), 2, 3, "Has_Element of a copy");
   else
      Ada.Text_IO.Put_Line ("Has_Element of a copy => KO ???");
   end if;

   Insert (Container => L1, New_Item => 1, Key => 4);

   --  Find
   if  Find (L1, 4) /=  Next (L1, Next (L1, First (L1)))
     or Find (L1, 4) /= Last (L1) then
      Ada.Text_IO.Put_Line ("Find 1 => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;
   if  Find (L1, 3) /=  Next (L1, First (L1))
     or Find (L1, 3) /= Previous (L1, Last (L1)) then
      Ada.Text_IO.Put_Line ("Find 2 => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   Ada.Text_IO.Put_Line ("LEFT :");

   --  Length of Left
   L3 :=  Left (Container => L1,
                Position  =>  Next (L1, Next (L1, First (L1))));
   if  Length (L3) = 2 then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line ("Length of Left => KO ???");
   end if;

   --  Has_Element of Left in range
   if  Has_Element (L3, First (L3)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L3, First (L3), 4, 2, "Has_Element of Left in range 1");
   else
      Ada.Text_IO.Put_Line ("Has_Element of Left in range 1 => KO ???");
   end if;
   if  Has_Element (L3, Next (L1, First (L3))) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L3, Next (L3, First (L3)), 2, 3,
                    "Has_Element of Left in range 2");
   else
      Ada.Text_IO.Put_Line ("Has_Element of Left in range 2 => KO ???");
   end if;

   --  Has_Element of Left out of range
   if  Has_Element (L3, Next (L1, Next (L3, First (L3)))) then
      Ada.Text_IO.Put_Line ("Has_Element of Left out of range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Find of Left in range
   if  Find (L3, 3) /=  Next (L3, First (L3))
     or Find (L3, 3) /=  Last (L3) then
      Ada.Text_IO.Put_Line ("Find of Left in range 1 => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;
   if  Find (L3, 2) /=  First (L3)
     or Find (L3, 2) /=  Previous (L3, Last (L3)) then
      Ada.Text_IO.Put_Line ("Find of Left in range 2 => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Find of Left out of range
   if  Find (L3, 4) /=  No_Element then
      Ada.Text_IO.Put_Line ("Find of Left out of range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Copy of Left : Length
   L4 :=  Copy (Left (L1, Next (L1, First (L1))), 5);
   if  Length (L4) = 1 then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line ("Copy of Left : Length => KO ???");
   end if;

   --  Copy of Left : Has_Element in range
   if  Has_Element (L4, First (L4)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L4, First (L1), 4, 2,
                    "Copy of Left : Has_Element in range");
   else
      Ada.Text_IO.Put_Line ("Copy of Left : Has_Element in range => KO ???");
   end if;

   --  Copy of Left : Has_Element out of range
   if  Has_Element (L4, Next (L1, First (L4))) then
      Ada.Text_IO.Put_Line
        ("Copy of Left : Has_Element out of range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Copy of Left : Find in range
   if  Find (L4, 2) /=  First (L4) then
      Ada.Text_IO.Put_Line ("Copy of Left : Find in range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Copy of Left : Find out of range
   if  Find (L4, 3) /=  No_Element or Find (L4, 4) /=  No_Element then
      Ada.Text_IO.Put_Line ("Copy of Left : Find out of range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Deleting a cursor after the cut doesn't change Left
   L2 :=  Copy (L1, 3);
   Delete (L2, 4);
   if  Strict_Equal (Left (L2, Last (L2)),
                     Left (L1, Previous (L1, Last (L1)))) then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line
        ("Deleting a cursor after the cut doesn't change Left 1 => KO ???");
   end if;
   if  Strict_Equal (L2,  Left (L1, Last (L1))) then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line
        ("Deleting a cursor after the cut doesn't change Left 2 => KO ???");
   end if;

   if  "=" (L3, Copy (L3, 3)) then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line ("Equivalent => KO ???");
   end if;

   if  Overlap (L3, L4) then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line ("Overlap => KO ???");
   end if;

   Ada.Text_IO.Put_Line ("RIGHT :");

   --  Length of Right
   L3 :=  Right (Container => L1, Position  =>  Next (L1, First (L1)));
   if  Length (L3) = 2 then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line ("Length of Right => KO ???");
   end if;

   --  Has_Element of Right in range
   if  Has_Element (L3, First (L3)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L3, Next (L1, First (L1)), 2, 3,
                    "Has_Element of Right in range 1");
   else
      Ada.Text_IO.Put_Line ("Has_Element of Right in range 1 => KO ???");
   end if;
   if  Has_Element (L3, Next (L3, First (L3))) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L3, Next (L3, First (L3)), 1, 4,
                    "Has_Element of Right in range 2");
   else
      Ada.Text_IO.Put_Line ("Has_Element of Right in range 2 => KO ???");
   end if;

   --  Has_Element of Right out of range
   if  Has_Element (L3, First (L1)) then
      Ada.Text_IO.Put_Line ("Has_Element of Right out of range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Find of Right in range
   if  Find (L3, 4) /=  Next (L3, First (L3)) or
     Find (L3, 4) /=  Last (L3) then
      Ada.Text_IO.Put_Line ("Find of Right in range 1 => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;
   if  Find (L3, 3) /=  First (L3)
     or Find (L3, 3) /=  Previous (L3, Last (L3)) then
      Ada.Text_IO.Put_Line ("Find of Right in range 2 => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Find of Right out of range
   if  Find (L3, 1) /=  No_Element or Find (L3, 2) /=  No_Element then
      Ada.Text_IO.Put_Line ("Find of Right out of range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Copy of Right : Length
   L4 :=  Copy (Right (L1, Next (L1, Next (L1, First (L1)))), 5);
   if  Length (L4) = 1 then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line ("Copy of Right : Length => KO ???");
   end if;

   --  Copy of Right : Has_Element in range
   if  Has_Element (L4, First (L4)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L4, Last (L1), 1, 4,
                    "Copy of Right : Has_Element in range");
   else
      Ada.Text_IO.Put_Line ("Copy of Right : Has_Element in range => KO ???");
   end if;

   --  Copy of Right : Has_Element out of range
   if  Has_Element (L4, Next (L1, First (L1))) then
      Ada.Text_IO.Put_Line
        ("Copy of Right : Has_Element out of range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Copy of Right : Find in range
   if  Find (L4, 4) /=  First (L4) then
      Ada.Text_IO.Put_Line ("Copy of Right : Find in range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Copy of Right : Find out of range
   if  Find (L4, 2) /=  No_Element or Find (L4, 3) /=  No_Element then
      Ada.Text_IO.Put_Line ("Copy of Right : Find out of range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Deleting a cursor before the cut doesn't change Right
   L2 :=  Copy (L1, 3);
   Delete (L2, 2);
   if  Strict_Equal (Right (L2, First (L2)),
                     Right (L1, Next (L1, First (L1)))) then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line
        ("Deleting a cursor before the cut doesn't change Right => KO ???");
   end if;

   if  "=" (L3, Copy (L3, 3)) then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line ("Equivalent => KO ???");
   end if;

   if  Overlap (L3, L4) then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line ("Overlap => KO ???");
   end if;

end test_vorma;
