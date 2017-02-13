with Ada.Containers; use Ada.Containers;

package body My_Vectors with SPARK_Mode is
   procedure Test_Vectors with SPARK_Mode is
      use My_Vectors.V;
      use My_Vectors.S;
      L, K : Vector (1);
      C    : Natural := No_Index;
   begin
      pragma Assert (Is_Empty (L));
      Append (L, 10);
      Append (L, 9, 4);
      Delete_Last (L);
      pragma Assert (Length (L) > 3);
      Delete_Last (L, 3);
      pragma Assert (Length (L) <= 3);
      Delete_Last (L, 3);

      Clear (L);

      Prepend (L, 10);
      Prepend (L, 9, 4);
      Delete_First (L);
      pragma Assert (Length (L) > 3);
      Delete_First (L, 3);
      pragma Assert (Length (L) <= 3);
      Delete_First (L, 3);

      Clear (L);

      C := 1;
      Insert (L, C, 8);
      Insert (L, C, 7, 4);

      pragma Assert (not Is_Empty (L));
      C := Last_Index (L) - 1;

      pragma Assert (C /= No_Index);
      Insert (L, C, 10);
      Insert (L, C, 9, 4);

      declare
         I : Vector := Copy (L);
      begin
         Move (K, I);
      end;

      Delete (L, C, 0);
      Delete (L, C);
      pragma Assert (C + 3 < Last_Index (L));
      Delete (L, C, 3);
      pragma Assert (C + 3 >= Last_Index (L));
      Delete (L, C, 3);

      Clear (L);
      C := 1;

      Delete_First (K, 5);
      Insert (K, C, L);
      Insert (L, C, K);
      Insert (L, C, K);

      C := Last_Index (K) - 1;

      pragma Assert (C /= No_Index);
      Delete_Last (L, 5);
      Insert (K, C, L);

      Clear (L);
      C := 1;

      Insert (L, C, 8);
      Insert (L, C, 7, 4);

      C := Last_Index (L) - 1;

      pragma Assert (C /= No_Index);
      Insert (L, C, 10);
      Insert (L, C, 9, 4);
      Insert (L, C, 8, 0);

      Replace_Element (L, C, 16);
      Replace_Element (L, C + 1, 16);

      pragma Assert (Find_Index (L, 16) = C);
      pragma Assert (Reverse_Find_Index (L, 16) = C + 1);
      pragma Assert (Find_Index (L, 15) = No_Index);
      pragma Assert (Reverse_Find_Index (L, 15) = No_Index);

      Reverse_Elements (L);
      Swap (L, 1, Last_Index (L));

      pragma Assert_And_Cut (Length (L) = 10 and not Is_Sorted (L));
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

      Clear (L);
      pragma Check (Proof_Only, False);
   end Test_Vectors;
end My_Vectors;
