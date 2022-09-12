package body Test_Set with SPARK_Mode is

   procedure Test_Set_Pos with Pre => True, SPARK_Mode is
      use Test_Set.M;
      L, K : Set (10, Default_Modulus (10));
      C    : Cursor;
      B    : Boolean;
   begin
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Next (L, C);
      pragma Assert (not Contains (L, 2));
      Insert (L, 1);
      Insert (L, 2);
      Insert (L, 1, C, B);
      pragma Assert (not B);

      Replace_Element (L, C, 1);
      Replace (L, 1);
      Formal_Model.Lift_Abstraction_Level (L);

      pragma Assert (Contains (L, 1));
      Assign (K, L);
      pragma Assert (Contains (K, 1));
      Move (L, K);
      pragma Assert (Contains (L, 1));
      Assign (K, L);

      pragma Assert (Contains (L, 1));
      Include (L, 1);
      pragma Assert (not Contains (L, 3));
      Include (L, 3);

      Delete (L, 2);

      pragma Assert (not Is_Subset (K, L));
      pragma Assert (Overlap (K, L));
      pragma Assert (not Equivalent_Sets (K, L));
      pragma Assert (not (K = L));
      declare
         M : Set := K and L;
         use Formal_Model;
      begin
         Assign (M, K);
         pragma Assert ((M and L) = (K and L));
         Intersection (M, L);
      end;
      declare
         M : Set := K or L;
      begin
         Assign (M, K);
         pragma Assert ((M or L) = (K or L));
         pragma Assert (Equivalent_Sets (M and L, K and L));
         Union (M, L);
      end;
      declare
         M : Set := K - L;
      begin
         Assign (M, K);
         pragma Assert ((M - L) = (K - L));
         Difference (M, L);
      end;
      declare
         M : Set := K xor L;
      begin
         Assign (M, K);
         pragma Assert ((M xor L) = (K xor L));
         Symmetric_Difference (M, L);
      end;

      C := Find (L, 3);
      Delete (L, C);
      pragma Assert (not Contains (L, 3));
      C := Find (L, 3);
      Exclude (L, 2);
      pragma Assert (Contains (L, 1));
      Exclude (L, 1);
      pragma Assert (Length (L) = 0);
      pragma Check (Proof_Only, False);
   end Test_Set_Pos;

   procedure Test_Set_Rec with Pre => True, SPARK_Mode is
      use Test_Set.N;
      use Test_Set.G;
      L, K : Set (10, Default_Modulus (10));
      C    : Cursor;
      B    : Boolean;
   begin
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Next (L, C);

      Insert (L, (F => 1, G => 1));
      Insert (L, (F => 2, G => 2));
      Insert (L, (F => 1, G => 1), C, B);
      pragma Assert (not Contains (L, (F => 3, G => 4)));
      pragma Assert (not B);

      Replace_Element (L, C, (F => 1, G => 2));
      Replace (L, (F => 1, G => 1));
      N.Formal_Model.Lift_Abstraction_Level (L);

      Assign (K, L);
      Move (L, K);

      pragma Assert (Contains (L, (F => 1, G => 1)));
      Include (L, (F => 1, G => 1));
      pragma Assert (not Contains (L, (F => 3, G => 3)));
      Include (L, (F => 3, G => 3));

      Assign (K, L);

      Delete (L, My_Rec'(F => 3, G => 3));
      C := Find (L, (F => 2, G => 2));
      Delete (L, C);
      pragma Assert (not Contains (L, (F => 2, G => 2)));
      C := Find (L, (F => 2, G => 2));
      Exclude (L, (F => 2, G => 2));
      pragma Assert (Contains (L, (F => 1, G => 1)));
      Exclude (L, (F => 1, G => 1));
      pragma Assert (Length (L) = 0);

      Replace (K, 1, (F => 1, G => 1));
      Delete (K, 3);
      C := Find (K, 2);
      pragma Assert (Contains (K, 2));
      Delete (K, C);
      pragma Assert (not Contains (K, 2));
      C := Find (K, 2);
      Exclude (K, 2);
      pragma Assert (Contains (K, 1));
      Exclude (K, 1);
      pragma Assert (Length (K) = 0);
      pragma Check (Proof_Only, False);
   end Test_Set_Rec;

   procedure Test_Set_Rec_2 with Pre => True, SPARK_Mode is
      use Test_Set.N;
      L, K : Set (10, Default_Modulus (10));
      C    : Cursor;
      B    : Boolean;
   begin
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Next (L, C);

      Insert (L, (F => 1, G => 1));
      Insert (L, (F => 2, G => 2));
      Insert (L, (F => 1, G => 2), C, B);
      pragma Assert (not Contains (L, (F => 3, G => 4)));
      pragma Assert (not B);

      Replace_Element (L, C, (F => 1, G => 2));
      Replace (L, (F => 1, G => 3));
      Formal_Model.Lift_Abstraction_Level (L);

      Assign (K, L);
      Move (L, K);

      pragma Assert (Contains (L, (F => 1, G => 4)));
      Include (L, (F => 1, G => 3));
      pragma Assert (not Contains (L, (F => 3, G => 4)));
      Include (L, (F => 3, G => 3));

      Delete (L, My_Rec'(F => 3, G => 5));
      C := Find (L, (F => 2, G => 4));
      Delete (L, C);
      pragma Assert (not Contains (L, (F => 2, G => 5)));
      C := Find (L, (F => 2, G => 6));
      Exclude (L, (F => 2, G => 7));
      pragma Assert (Contains (L, (F => 1, G => 8)));
      Exclude (L, (F => 1, G => 9));
      pragma Assert (Length (L) = 0);
      pragma Check (Proof_Only, False);
   end Test_Set_Rec_2;

   procedure Run_Test is
   begin
      Test_Set_Pos;
      Test_Set_Rec;
      Test_Set_Rec_2;
   end Run_Test;

   procedure Large_Test
   is
      use Test_Set.M;
      use Formal_Model;
      L, K : Set (10, Default_Modulus (10));
      C, D : Cursor;
      B    : Boolean;
   begin

      --  Copy
      pragma Assert (not Contains (L, 1));
      pragma Assert (not Contains (L, 2));
      pragma Assert (not Contains (L, 4));
      pragma Assert (not Contains (L, 5));

      Insert (L, 4);
      Insert (L, 5);
      C := First (L);
      D := Next (L, C);

      K := Copy (L);
      pragma Assert (Model (K) = Model (L));
      pragma Assert (Element (L, C) = Element (K, C));
      pragma Assert (Element (L, D) = Element (K, D));
      pragma Assert (not Contains (K, 1));
      pragma Assert (not Contains (K, 2));
      pragma Assert (K = L);
      pragma Assert (L = K);
      pragma Assert (Length (L) = Length (K));

      --  Difference

      Insert (K, 1);
      Insert (K, 2);

      Difference (K, L);

      pragma Assert (Overlap (L, K) = False);
      pragma Assert (Contains (K, 1));
      pragma Assert (Contains (K, 2));
      pragma Assert (Length (K) = 2);

      declare
         S : Set (0, 0) := Empty_Set;
      begin
         S := Empty_Set;
         Difference (K, S);

         pragma Assert (Length (K) = 2);

         S := Difference (S, K);
      end;

      --  Empty_Set

      Clear (K);

      pragma Assert_And_Cut (Is_Empty (K));

      Insert (K, 1);
      pragma Assert (Contains (K, 1));

      --  Equivalent_Sets

      Clear (K);
      Clear (L);
      pragma Assert_And_Cut (Is_Empty (L) and Is_Empty (K));

      --  Put 2 elements in the same bucket

      pragma Assert (not Contains (L, 1));
      pragma Assert (not Contains (L, 54));
      pragma Assert (not Contains (K, 1));
      pragma Assert (not Contains (K, 54));

      Insert (L, 1);
      Insert (L, 54);

      Insert (K, 54);
      Insert (k, 1);

      pragma Assert (Equivalent_Sets (L, K));

      --  Exclude

      Exclude (L, 2);

      --  Force Resize;

      Clear (L);
      pragma Assert_And_Cut (Is_Empty (L));
      pragma Assert (for all J in 1 .. 7 => not Contains (L, J));
      for Idx in 1 .. 5 loop
         pragma Loop_Invariant (for all J in Idx .. 7 => not Contains (L, J));
         pragma Loop_Invariant (Length (L) = Count_Type (Idx) - 1);

         Insert (L, Idx);
         pragma Assert (for all J in Idx + 1 .. 7 => not Contains (L, J));
      end loop;

      pragma Assert (not Contains (L, 6));
      Insert (L, 6);

      --  Has_Element

      C := Find (L, 6);
      D := Find (L, 7);
      pragma Assert (not Contains (L, 7));
      pragma Assert (D = No_Element);
      pragma Assert (Has_Element (L, C));
      pragma Assert (not Has_Element (L, D));

      --  Intersection

      Clear (L);
      Clear (K);

      pragma Assert_And_Cut (Is_Empty (L) and Is_Empty (K));
      pragma Assert (not Contains (L, 2));

      Insert (L, 1);
      Insert (L, 2);

      Intersection (L, K);

      pragma Assert_And_Cut (Is_Empty (L) and Is_Empty (K));
      pragma Assert (not Contains (L, 1));
      pragma Assert (not Contains (L, 2));

      pragma Assert (Model (L) = Formal_Model.M.Empty_Set);

      Insert (L, 1);
      Insert (L, 2);

      Intersection (K, L);

      pragma Assert (Is_Empty (K));

      --  Is_Subset

      pragma Assert (not Contains (K, 1));
      pragma Assert (not Contains (K, 2));
      pragma Assert (Model (K) <= Model (L));

      Insert (K, 1);
      pragma Assert (Is_Subset (K, L));

      Insert (K, 2);
      pragma Assert (Contains (L, 2));
      pragma Assert (Is_Subset (L, K));

      --  Next

      C := First (L);
      pragma Assert (Element (L, C) = 1 or Element (L, C) = 2);
      Next (L, C);
      pragma Assert (Element (L, C) = 1 or Element (L, C) = 2);

      --  Symmetric Difference

      Clear (L);

      Symmetric_Difference (L, K);
      pragma Assert (L = K);

      Clear (L);
      Assign (L, Symmetric_Difference (L, K));
      pragma Assert (L = K);

      Clear (L);

      Symmetric_Difference (K, L);
      pragma Assert (Length (K) = 2);

      Assign (K, Symmetric_Difference (K, L));
      pragma Assert (Length (K) = 2);

      --  To_Set

      --  To_Set use by default 1 as modulus. Assign allow to use anther one

      Assign (L, To_Set (4));

      --  Union

      Union (L, K);

      pragma Assert (Contains (L, 1));
      pragma Assert (Contains (L, 2));
      pragma Assert (Contains (L, 4));

      declare
         S : Set (10, Default_Modulus (10));
      begin
         Union (L, S);
         pragma Assert (Contains (L, 4));
         pragma Assert (Length (L) = 3);

         Union (S, L);
         pragma Assert (Contains (S, 4));
         pragma Assert (Length (S) = 3);
      end;



      pragma Check (Proof_Only, False);
   end Large_Test;
end Test_Set;
