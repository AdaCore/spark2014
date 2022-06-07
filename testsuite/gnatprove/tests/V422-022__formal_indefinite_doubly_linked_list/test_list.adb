with Ada.Containers; use Ada.Containers;
with Ada.Text_IO; use Ada.Text_IO;

with Ada.Containers.Functional_Vectors;

package body Test_List with SPARK_Mode => On is

   use Test_List.M;
   use Test_List.S;
   use Test_List.M.Formal_Model;

   procedure Run is
      L, K : List;
      C, D : Cursor;
   begin
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Last (L);
      C := Next (L, C);
      C := Previous (L, C);

      Append (L, 10);
      Append (L, 9, 4);
      Delete_Last (L);
      pragma Assert (Length (L) > 3);
      Delete_Last (L, 3);
      pragma Assert (Length (L) <= 3);
      Delete_Last (L, 3);

      Prepend (L, 10);
      Prepend (L, 9, 4);
      Delete_First (L);
      pragma Assert (Length (L) > 3);
      Delete_First (L, 3);
      pragma Assert (Length (L) <= 3);
      Delete_First (L, 3);

      pragma Assert_And_Cut (C = No_Element and Length (L) = 0);
      Insert (L, C, 8);
      Insert (L, C, 7, 4);

      pragma Assert (not Is_Empty (L));
      C := First (L);
      Previous (L, C);
      C := Last (L);
      Next (L, C);
      C := Last (L);
      pragma Assert (C /= No_Element and C /= First (L));
      Previous (L, C);
      pragma Assert (C /= No_Element and C /= Last (L));
      Next (L, C);
      D := Previous (L, C);

      pragma Assert (C /= No_Element);
      Insert (L, C, 10);
      Insert (L, C, 9, 4);

      K := Copy (L);

      C := Next (L, D);
      Delete (L, D, 0);
      D := Previous (L, C);
      Delete (L, D);
      D := Next (L, C);
      pragma Assert
        (M.Formal_Model.P.Get (M.Formal_Model.Positions (L), D) + 3 < Length (L));
      Delete (L, D, 3);
      D := Next (L, C);
      pragma Assert
        (M.Formal_Model.P.Get (M.Formal_Model.Positions (L), D) + 3 >= Length (L));
      Delete (L, D, 3);

      Clear (L);
      C := No_Element;

      pragma Assert_And_Cut (C = No_Element and Length (L) = 0 and Length (K) = 10);
      Insert (L, C, 8, D);
      Insert (L, C, 7, D, 4);

      C := Previous (L, Last (L));

      pragma Assert (C /= No_Element);
      Insert (L, C, 10, D);
      Insert (L, C, 9, D, 4);
      Insert (L, C, 8, D, 0);

      pragma Assert (Length (L) = 10);


      Replace_Element (L, C, 16);
      Replace_Element (L, Next (L, C), 16);

      pragma Assert (Find (L, 16) = C);
      pragma Assert (Reverse_Find (L, 16) = Next (L, C));
      pragma Assert (Find (L, 15) = No_Element);
      pragma Assert (Reverse_Find (L, 15) = No_Element);

      Reverse_Elements (L);
      Swap (L, First (L), Last (L));
      Swap_Links (L, First (L), Last (L));

      pragma Assert (Length (L) = 10);
      Delete_Last (L, 5);
      Delete_First (K, 5);
      Splice (L, No_Element, K);

      pragma Assert (Length (L) = 10);

      Assign (K, L);

      Delete_Last (L, 0);
      Delete_Last (L, 5);
      Delete_First (L, 0);
      Delete_First (K, 5);
      C := Previous (L, Last (L));
      pragma Assert (C /= No_Element);
      Splice (L, C, K);

      pragma Assert (Length (L) = 10);

      Assign (K, L);
      Delete_Last (K);
      C := First (L);
      Splice (K, No_Element, L, C);
      Splice (L, First (L), K, C);

      pragma Assert_And_Cut (Length (L) = 10);

      pragma Assume (not Is_Sorted (L));
      Assign (K, L);

      Sort (L);
      Delete_Last (L, 5);
      Delete_First (K, 5);
      Merge (L, K);

      pragma Assert (Length (L) = 10);

      Sort (L);
      Assign (K, L);
      Delete_Last (L, 5);
      Delete_First (K, 5);
      Merge (L, K);
      pragma Assert (Is_Sorted (L));
   end Run;

   procedure Large_Run
   is
      L, K : List;
      C, D : Cursor;

   begin
      --  Test "="

      --  When the two lists are exactly the same

      Append (L, 1);
      Append (K, 1);
      Append (L, 3);
      Append (K, 3);

      pragma Assert (L = K);

      --  Mix the indexes

      Clear (L);
      Clear (K);

      Append (L, 1);
      Append (L, 3);

      Append (K, 3);
      Prepend (K, 1); --  The cell 1 will be at index 2

      pragma Assert (L = K);

      --  Test for Clear

      pragma Assert (not Is_Empty (L));
      Clear (L);
      pragma Assert (Is_Empty (L));

      -- Test Assign

      declare
         S : List;
      begin
         Append (L, 9, 10);

         Assign (S, L);

         pragma Assert (S = L);
      end;

      --  Test Move

      declare
         S : List;
      begin
         Append (L, 9, 10);
         Assign (K, L);

         Move (S, L);

         pragma Assert (S = K);
         pragma Assert (Is_Empty (L));
      end;

      --  Test Resize

      Clear (L);
      pragma Assert (Is_Empty (L));
      Append (L, 9, 99);
      pragma Assert (Length (L) = 99);
      Assign (K, L);
      pragma Assert (M.Formal_Model.M.Range_Equal
                       (Model (L),
                        Model (K),
                        1,
                        99));

      Append (L, 10, 20);
      pragma Assert (M.Formal_Model.M.Range_Equal
                       (Model (L),
                        Model (K),
                        1,
                        99));

      pragma Assert (M.Formal_Model.M.Constant_Range
                       (Model (L),
                        100,
                        119,
                        10));

      --  Check equal

      pragma Assert (L = L);
      Assign (K, L);

      Replace_Element (K, First (K), 1);

      pragma Assert (L /= K);

      Append (K, 1);
      pragma Assert (L /= K);

      --  Adjust empty list

      Clear (L);
      K := L;

      pragma Assert (Is_Empty (K));

      --  Constant ref

      Append (L, 1);
      C := First (L);

      pragma Assert (Element (L, C) = 1);
      pragma Assert (First_Element (L) = 1);

      declare
         N : access constant Natural := Constant_Reference (L, C);
      begin
         pragma Assert (N.all = 1);
      end;

      --  Reference

      declare
         New_List : aliased List := L;
      begin
         declare
            Access_List : access List := New_List'Access;
            N : access Natural := Reference (Access_List, C);
         begin
            pragma Assert (N.all = 1);
            N.all := 2;
         end;

         pragma Assert (First_Element (New_List) = 2);
      end;

      pragma Assert (First_Element (L) = 1);

      --  Contains

      pragma Assert (Contains (L, 1));
      pragma Assert (not Contains (L, 2));

      --  Has Element at No_Element

      pragma Assert (Has_Element (L, No_Element) = False);

      --  Copy an empty list

      K := Copy (K);

      pragma Assert (Is_Empty (K));

      --  Find in an empty list

      pragma Assert (Find (K, 1, No_Element) = No_Element);

      --  Test Last_Element

      Append (L, 5);
      Append (L, 7);

      pragma Assert (Last_Element (L) = 7);

      --  Test Move

      --  Move nothing

      Move (L, K);

      pragma Assert (Is_Empty (L));

      L := Empty_List;
      Append (L, 1);
      Append (K, 5, 110);

      pragma Assert (Test_List.M.Formal_Model.M.Constant_Range (Model (K), 1, 110, 5));
      Move (L, K);

      pragma Assert (Test_List.M.Formal_Model.M.Constant_Range (Model (L), 1, 110, 5));
      pragma Assert (Length (L) = 110);

      --  Splice

      Clear (L);
      Append (L, 1, 4);

      C := First (L);
      Next (L, C);

      Insert (L, C, 2);

      C := First (L);
      Next (L, C);

      pragma Assert (Test_List.M.Formal_Model.Element (Test_List.M.Formal_Model.Model (L), 2) = 2);

      Splice (L, No_Element, C);

      pragma Assert (Test_List.M.Formal_Model.Element (Test_List.M.Formal_Model.Model (L), 2) = 1);
      pragma Assert (Last_Element (L) = 2);

      Clear (L);
      Append (L, 1, 2);

      Prepend (L, 2);
      Append (L, 3);

      C := First (L);
      D := Last (L);
      Splice (L, C, D);

      pragma Assert (Last_Element (L) = 1);
      pragma Assert (First_Element (L) = 3);

      Clear (L);
      Append (L, 1, 2);

      Prepend (L, 2);
      Append (L, 3);

      C := First (L);
      D := Last (L);
      Previous (L, D);
      Splice (L, C, D);

      pragma Assert (Last_Element (L) = 3);
      pragma Assert (First_Element (L) = 1);

      Clear (L);
      Append (l, 1);
      Append (l, 2);
      Append (l, 3);
      Append (l, 4);

      D := First (L);
      C := Last (L);
      Previous (L, C);

      Splice (L, C, D);

      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 1) = 2);
      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 2) = 1);
      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 3) = 3);
      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 4) = 4);

      Clear (L);
      Append (l, 1);
      Append (l, 2);
      Append (l, 3);
      Append (l, 4);

      C := First (L);
      Next (L, C);
      D := Last (L);
      Previous (L, D);

      Splice (L, C, D);

      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 1) = 1);
      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 2) = 3);
      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 3) = 2);
      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 4) = 4);

      --  Swap_Links

      pragma Assert (Element (L, C) = 2);
      pragma Assert (Element (L, D) = 3);

      Swap_Links (L, C, D);
      Swap_Links (L, C, D);

      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 1) = 1);
      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 2) = 3);
      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 3) = 2);
      pragma Assert (Test_List.M.Formal_Model.M.Get (Model (L), 4) = 4);

   end Large_Run;

end Test_List;
