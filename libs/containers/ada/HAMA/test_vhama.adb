with Ada.Text_IO;
with Ada.Containers;
use Ada.Containers;
with Ada.Containers.Formal_Hashed_Maps;

procedure test_vhama is

   function Hash (Element : Integer) return Hash_Type;
   function Equivalent_Keys (Element1 : Integer; Element2 : Integer)
                             return Boolean;

   function Hash (Element : Integer) return Hash_Type is
   begin
      return Hash_Type (Element);
   end Hash;

   function Equivalent_Keys (Element1 : Integer; Element2 : Integer)
                             return Boolean is
   begin
      return Element1 = Element2;
   end Equivalent_Keys;

   package VHAMA is new Formal_Hashed_Maps
     (Element_Type => Integer,
      Key_Type => Integer,
      Hash => Hash,
      Equivalent_Keys => Equivalent_Keys);
   use VHAMA;
   L1 :  Map (3, 2);
   L2 :  Map (3, 2);
   L3 :  Map (3, 2);
   L4 :  Map (5, 2);
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
          Key => 3,
          New_Item  => 1);
   if  Has_Element (L1, First (L1)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L1, First (L1), 1, 3, "Has_Element of first");
   else
      Ada.Text_IO.Put_Line ("Has_Element of first => KO ???");
   end if;

   --  Has_Element of a copy
   L2 :=  Copy (L1, 3);
   if  Has_Element (L2, First (L1)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L2, First (L1), 1, 3, "Has_Element of a copy");
   else
      Ada.Text_IO.Put_Line ("Has_Element of a copy => KO ???");
   end if;

   --  Has_Element of inserted Element after Insertion
   Insert (Container => L1,
          Key => 1,
          New_Item  => 2);
   if  Has_Element (L1, Next (L1, First (L1))) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L1, First (L1), 2, 1,
                    "Has_Element of inserted Element after Insertion");
      Test_Element (L1, Next (L1, First (L1)), 1, 3,
                    "Has_Element of inserted Element after Insertion");
   else
      Ada.Text_IO.Put_Line
        ("Has_Element of inserted Element after Insertion => KO ???");
   end if;

   --  Has_Element of inserted Element before Insertion
   if  Has_Element (L2, First (L1)) then
      Ada.Text_IO.Put_Line
        ("Has_Element of inserted Element before Insertion => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Has_Element of deleted Element after deletion
   Insert (Container => L1, New_Item => 3, Key => 2);
   C1 :=  Next (L1, First (L1));
   C2 :=  Next (L1, First (L1));
   Delete (Container => L1, Position  => C1);
   if  Has_Element (L1, C2) then
      Ada.Text_IO.Put_Line
        ("Has_Element of deleted Element after deletion => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Has_Element of a copy
   L2 :=  Copy (L1, 3);
   if  Has_Element (L2, First (L1)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L2, First (L2), 3, 2, "Has_Element of a copy");
   else
      Ada.Text_IO.Put_Line ("Has_Element of a copy => KO ???");
   end if;

   Insert (Container => L1, New_Item => 4, Key => 5);

   --  Find
   if  Find (L1, 3) /=  Next (L1, Next (L1, First (L1))) then
      Ada.Text_IO.Put_Line ("Find => KO ???");
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
      Test_Element (L3, First (L3), 3, 2, "Has_Element of Left in range 1");
   else
      Ada.Text_IO.Put_Line ("Has_Element of Left in range 1 => KO ???");
   end if;
   if  Has_Element (L3, Next (L3, First (L3))) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L3, Next (L3, First (L3)), 4, 5,
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
   if  Find (L3, 5) /=  Next (L3, First (L3)) then
      Ada.Text_IO.Put_Line ("Find of Left in range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Find of Left out of range
   if  Find (L3, 3) /=  No_Element then
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
      Test_Element (L4, First (L4), 3, 2,
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
   if  Find (L4, 5) /=  No_Element then
      Ada.Text_IO.Put_Line ("Copy of Left : Find out of range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Deleting a cursor after the cut doesn't change Left
   L2 :=  Copy (L1, 3);
   Delete (L2, 3);
   if  Strict_Equal (Left (L2, Next (L2, First (L2))),
                     Left (L1, Next (L1, First (L1)))) then
      Ada.Text_IO.Put_Line ("OK");
   else
      Ada.Text_IO.Put_Line
        ("Deleting a cursor after the cut doesn't change Left => KO ???");
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
      Test_Element (L3, First (L3), 4, 5, "Has_Element of Right in range 1");
   else
      Ada.Text_IO.Put_Line ("Has_Element of Right in range 1 => KO ???");
   end if;
   if  Has_Element (L3, Next (L3, First (L3))) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L3, Next (L3, First (L3)), 1, 3,
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
   if  Find (L3, 3) /=  Next (L3, First (L3)) then
      Ada.Text_IO.Put_Line ("Find of Right in range 1 => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;
   if  Find (L3, 5) /=  First (L3) then
      Ada.Text_IO.Put_Line ("Find of Right in range 2 => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Find of Right out of range
   if  Find (L3, 2) /=  No_Element then
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

   L2 :=  Right (L1, Next (L1, Next (L1, First (L1))));

   --  Copy of Right : Has_Element in range
   if  Has_Element (L4, First (L4)) then
      Ada.Text_IO.Put_Line ("OK");
      Test_Element (L4, First (L4), 1, 3,
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
   if  Find (L4, 3) /=  First (L4) then
      Ada.Text_IO.Put_Line ("Copy of Right : Find in range => KO ???");
   else
      Ada.Text_IO.Put_Line ("OK");
   end if;

   --  Copy of Right : Find out of range
   if  Find (L4, 5) /=  No_Element then
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

end test_vhama;
