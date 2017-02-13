with Ada.Containers; use Ada.Containers;

package body My_Sets with SPARK_Mode is
   procedure Test_Set_Pos with Pre => True is
      use My_Sets.M;
      L, K : Set (10, Default_Modulus (10));
      C    : Cursor;
      B    : Boolean;
   begin
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Next (L, C);

      Insert (L, 1);
      Insert (L, 2);
      Insert (L, 1, C, B);
      pragma Assert (not B);

      Replace_Element (L, C, 1);
      Replace (L, 1);
      Formal_Model.Lift_Abstraction_Level (L);

      Assign (K, L);
      Move (L, K);
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
         pragma Assume (M.Capacity >= Length (K));
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
         pragma Assume (M.Capacity >= Length (K));
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

   procedure Test_Set_Rec with Pre => True is
      use My_Sets.N;
      use My_Sets.G;
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

   procedure Test_Set_Rec_2 with Pre => True is
      use My_Sets.N;
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

   procedure Test_Set is
   begin
      Test_Set_Pos;
      Test_Set_Rec;
      Test_Set_Rec_2;
   end Test_Set;
end My_Sets;
