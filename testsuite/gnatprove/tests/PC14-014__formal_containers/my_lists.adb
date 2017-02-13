with Ada.Containers; use Ada.Containers;

package body My_Lists with SPARK_Mode is
   procedure Test_List with SPARK_Mode is
      use My_Lists.M;
      use My_Lists.S;
      L, K : List (10);
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

      pragma Check (Proof_Only, False);
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

      pragma Check (Proof_Only, False);
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

      pragma Check (Proof_Only, False);
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
      pragma Check (Proof_Only, False);
   end Test_List;
end My_Lists;
