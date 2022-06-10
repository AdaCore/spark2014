with Ada.Containers; use Ada.Containers;

with Ada.Text_IO;
use Ada.Text_IO;

package body Test_Vectors with SPARK_Mode is

   procedure Run is
      use Test_Vectors.V;
      use Test_Vectors.S;
      use Test_Vectors.V.Formal_Model;
      L, K : Vector;
      C    : Natural := No_Index;

   begin
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
      pragma Assert (Length (L) = 1);
      Insert (L, C, 7, 4);
      pragma Assert (Length (L) = 5);
      pragma Assert (not (Length (L) = 0));

      pragma Assert (not Is_Empty (L));
      C := Last_Index (L) - 1;

      pragma Assert (C /= No_Index);
      Insert (L, C, 10);
      Insert (L, C, 9, 4);

      declare
         I : Vector := Copy (L);
      begin
         Move (K, I);
         pragma Assert (Is_Empty (I));
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
      Clear (L);

      Append (L, 1);
      Append (L, 2);
      Append (L, 3);

      pragma Assert (Element (L, 1) = 1);
      pragma Assert (Element (L, 2) = 2);
      pragma Assert (Element (L, 3) = 3);

      Append (L, 4);

      Delete (L, 2, 2);

      pragma Assert (Length (L) = 2);
      pragma Assert (Element (L, 1) = 1);
      pragma Assert (Element (L, 2) = 4);

      L := To_Vector (4, 3);

      pragma Assert (Length (L) = 3);
      pragma Assert (Element (L, 1) = 4);
      pragma Assert (Element (L, 2) = 4);
      pragma Assert (Element (L, 3) = 4);

      --  Append enought element for the vector to resize

      Clear (L);

      Append (L, 5, 99);
      pragma Assert (Length (L) = 99);

      Insert (L, 51, 6, 10);
      pragma Assert (M.Constant_Range (Model (L),
                                       1,
                                       50,
                                       5));

      pragma Assert (M.Constant_Range (Model (L),
                                       51,
                                       60,
                                       6));

      pragma Assert (M.Constant_Range (Model (L),
                                       61,
                                       109,
                                       5));

      L := Empty_Vector;
      Append (L, 4, 200);
   end Run;

   procedure Large_Run is
      use Test_Vectors.V;
      use Test_Vectors.S;
      use Test_Vectors.V.Formal_Model;
      L, K : Vector;
      C    : Natural := No_Index;
   begin

      --  Test "="

      Append (L, 4);
      Append (L, 0);
      Append (L, 3);

      Append (K, 4);
      Append (K, 0);
      Append (K, 3);

      pragma Assert (L = L);
      pragma Assert (L = K);

      Append (L, 4);
      pragma Assert (L /= K);

      Append (K, 5);
      pragma Assert (L /= K);

      --  Contains

      pragma Assert (Contains (L, 4));
      pragma Assert (not Contains (L, 10));

      --  Delete Last

      pragma Assert (Length (L) = 4);
      pragma Assert (Last_Element (L) = 4);

      Delete_Last (L);

      pragma Assert (Length (L) = 3);
      pragma Assert (V.Formal_Model.M.Range_Equal (Model (L), Model (K), 1, 3));

      Delete_Last (L, 0);
      pragma Assert (Length (L) = 3);

      Delete_Last (L, 3);
      pragma Assert (Length (L) = 0);

      --  Delete First

      pragma Assert (Length (K) = 4);
      L := K;

      Delete_First (L);
      pragma Assert (Length (L) = 3);
      pragma Assert (V.Formal_Model.M.Range_Shifted (Model (L), Model (K), 1, 3, 1));

      Delete_First (L, 0);
      pragma Assert (Length (L) = 3);
      pragma Assert (V.Formal_Model.M.Range_Shifted (Model (L), Model (K), 1, 3, 1));

      --  First Element

      --  L : [0, 4, 5]
      --  K : [4, 0, 4, 5]

      pragma Assert (First_Element (L) = 0);
      pragma Assert (First_Element (K) = 4);

      --  Sort & Merge

      Clear (L);
      Append (L, 6);
      Append (L, 10);
      Append (L, 1);
      Append (L, 8);

      pragma Assert (Length (L) = 4);

      Clear (K);
      Append (K, 7);
      Append (K, 4);
      Append (K, 2);
      Append (K, 5);
      Append (K, 9);
      Append (K, 3);

      pragma Assert (Length (K) = 6);

      Sort (L);
      pragma Assert (S.Formal_Model.M_Elements_Sorted (Model (L)));
      pragma Assert (Length (L) = 4);
      pragma Assert (S.Formal_Model.M_Elements_Sorted (Model (L)) = Is_Sorted (L));
      pragma Assert (Is_Sorted (L));

      Sort (K);
      pragma Assert (Length (K) = 6);
      pragma Assert (Is_Sorted (K));

      Merge (L, K);

      pragma Assert (Length (L) = 10);
      pragma Assert (Is_Sorted (L));

      --  Empty vectors

      Merge (L, K);
      pragma Assert (Length (L) = 10);
      pragma Assert (Is_Sorted (L));
      pragma Assert (Is_Empty (K));

      Merge (K, L);
      pragma Assert (Length (K) = 10);
      pragma Assert (Is_Sorted (K));
      pragma Assert (Is_Empty (L));

      --  Merge with Left vector smaller

      Clear (L);
      Clear (K);

      Append (L, 1);
      Append (L, 2);
      Append (L, 3);

      Append (K, 4);

      pragma Assert (Is_Sorted (L));
      pragma Assert (Is_Sorted (K));

      Merge (K, L);

      pragma Assert (Is_Sorted (K));
      pragma Assert (Is_Empty (L));

      --  First Index

      pragma Assert (First_Element (K) = Element (K, First_Index (K)));

      --  Has Element

      pragma Assert (Length (K) = 4);
      for J in 1 .. 4 loop
         pragma Assert (Has_Element (K, J));
      end loop;
      pragma Assert (not Has_Element (K, 5));

      --  Prepend a vector

      Append (L, 5);

      Prepend (K, L);

      pragma Assert (First_Element (K) = First_Element (L));

      --  Reverse Element

      Clear (L);
      Reverse_Elements (L);

      --  Delete nothing

      Append (L, 1, 5);
      Delete (L, 1, 0);
      pragma Assert (Length (L) = 5);

      --  Reverse Find

      Insert (L, 2, 3);
      C := Reverse_Find_Index (L, 3, 4);
      pragma Assert (C = 2);

      L := Empty_Vector;
      C := Reverse_Find_Index (L, 2);
      pragma Assert (C = No_Index);
   end Large_Run;

   procedure Index_Negative is
      type Negative_Index_Type is range -10 .. 10;

      --  package Vecs is new Vec (Negative_Index_Type, Natural);
      package Vecs is new SPARK.Containers.Formal.Unbounded_Vectors
        (Negative_Index_Type, Natural);
      use Vecs;

      V : Vector;

   begin
      Append (V, 3, 4);
      Insert (V, -7, 3);

      Delete_Last (V);
      pragma Assert (Last_Element (V) = 3);
   end Index_Negative;
end Test_Vectors;
