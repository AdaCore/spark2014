with Ada.Containers; use Ada.Containers;

package body Test_Set with SPARK_Mode is

   procedure Test_Set_Pos with Pre => True is
      use Test_Set.M;
      L, K : Set (10);
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
      Insert (L, 4);

      pragma Assert (Formal_Model.P.Get (Formal_Model.Positions (L), Floor (L, 1)) = 1);
      pragma Assert (Formal_Model.P.Get (Formal_Model.Positions (L), Floor (L, 3)) = 2);
      pragma Assert (Floor (L, 0) = No_Element);
      pragma Assert (Formal_Model.P.Get (Formal_Model.Positions (L), Ceiling (L, 1)) = 1);
      pragma Assert (Formal_Model.P.Get (Formal_Model.Positions (L), Ceiling (L, 3)) = 3);
      pragma Assert (Ceiling (L, 5) = No_Element);

      pragma Assert (not Contains (L, 3));
      Include (L, 3);
      Insert (L, 5);
      pragma Assert (Contains (L, 2));

      Delete (L, 2);

      pragma Assert (not Is_Subset (K, L));
      pragma Assert (Overlap (K, L));
      pragma Assert (not Equivalent_Sets (K, L));
      pragma Assert (not (K = L));
      declare
         M : Set := K and L;
         A : Set := M;

      begin
         Assign (M, K);
         declare
            B : Set := M and L;
            C : Set := K and L;
         begin
            pragma Assert ((M and L) = (K and L));
            Intersection (M, L);
         end;
      end;
      declare
         M : Set := K or L;
      begin
         Assign (M, K);
         pragma Assert ((M or L) = (K or L));
         pragma Assert (Equivalent_Sets (M and L, K and L));
         Union (M, L);
         null;
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

      Delete_First (L);
      Delete_Last (L);

      C := Find (L, 3);
      Delete (L, C);
      pragma Assert (not Contains (L, 3));
      C := Find (L, 3);
      Exclude (L, 2);
      pragma Assert (Contains (L, 4));
      Exclude (L, 4);
      pragma Assert (Length (L) = 0);
      pragma Check (Proof_Only, False);
   end Test_Set_Pos;

   procedure Test_Set_Rec with Pre => True is
      use Test_Set.N;
      use Test_Set.G;
      L, K : Set (10);
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
      pragma Assert (not Contains (L, (F => 4, G => 4)));
      Include (L, (F => 4, G => 4));

      Assign (K, L);

      Delete (L, My_Rec'(F => 4, G => 4));
      C := Find (L, (F => 2, G => 2));
      Delete (L, C);
      pragma Assert (not Contains (L, (F => 2, G => 2)));
      C := Find (L, (F => 2, G => 2));
      Exclude (L, (F => 2, G => 2));
      pragma Assert (Contains (L, (F => 1, G => 1)));
      Exclude (L, (F => 1, G => 1));
      pragma Assert (Length (L) = 0);

      Replace (K, 1, (F => 1, G => 1));
      Delete (K, 4);
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
      use Test_Set.N;
      L, K : Set (10);
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

   procedure Test_Ordered_Set is
   begin
      null;
      Test_Set_Pos;
      Test_Set_Rec;
      Test_Set_Rec_2;
   end Test_Ordered_Set;

   procedure Large_Test is
   use Test_Set.M;
   L, K : Set (10);
   C    : Cursor;
   Val  : Natural;

   begin
      --  Test "=" between sets

      pragma Assert (L = k);

      Insert (K, 3);
      Insert (K, 6);

      Insert (L, 6);
      Insert (L, 3);

      pragma Assert (L = K);

      Insert (L, 2);

      pragma Assert (L /= K);

      Insert (K, 1);

      pragma Assert (L /= K);

      --  Test Copy

      K := Copy (L);
      pragma Assert (l = K);

      Assign (L, Empty_Set);
      K := Copy (L);
      pragma Assert (L = K);
      pragma Assert (Is_Empty (K));

      --  Delete

      Insert (L, 3);
      Insert (L, 4);
      C := Find (L, 3);
      Delete (L, C);
      pragma Assert (not Contains (L, 3));
      pragma Assert (Contains (L, 4));
      pragma Assert (Length (L) = 1);

      --  Delete First

      Insert (L, 5);
      Val := First_Element (L);

      pragma Assert (Contains (L, Val));
      Delete_First (L);
      pragma Assert (not Contains (L, Val));

      --  Delete Last

      Insert (L, 10);
      Val := Last_Element (L);

      pragma Assert (Contains (L, Val));
      Delete_Last (L);
      pragma Assert (not Contains (L, Val));

      --  Difference

      Clear (L);
      Clear (K);
      pragma Assert (not Contains (L, 2));
      pragma Assert (not Contains (L, 3));
      pragma Assert (not Contains (K, 1));

      Insert (L, 1);
      Insert (L, 2);
      Insert (L, 3);

      Insert (K, 2);
      Insert (K, 1);

      declare
         S : Set := Difference (L, K);
      begin
         pragma Assert (Length (S) = 1);
         pragma Assert (Contains (S, 3));

         Difference (L, K);
         pragma Assert (S = L);
      end;

      --  Exclude

      Exclude (L, 1);
      pragma Assert (Length (L) = 1);
      pragma Assert (not Contains (L, 1));

      K := L;
      Exclude (L, 1);
      pragma Assert (L = K);

      --  Ceilling

      Clear (L);
      Insert (L, 1);
      Insert (L, 2);
      Insert (L, 4);

      C := Ceiling (L, 3);
      pragma Assert (C = Last (L));

      C := Floor (L, 3);
      pragma Assert (C = Previous (L, Last (L)));

      --  Next

      C := First (L);
      pragma Assert (Element (L, C) = 1);

      C := Next (L, C);
      pragma Assert (Element (L, C) = 2);

      Next (L, C);
      pragma Assert (Element (L, C) = 4);

      --  Previous

      C := Previous (L, C);
      pragma Assert (Element (L, C) = 2);

      Previous (L, C);
      pragma Assert (Element (L, C) = 1);

      --  Replace

      K := L;
      pragma Assert (Element (L, First (L)) = 1);
      Replace_Element (L, First (L), 3);

      --  Intersection

      Clear (L);
      Clear (K);

      Insert (L, 1);
      Insert (L, 3);

      Insert (K, 2);
      Insert (K, 1);

      declare
         S : Set := Intersection (K, L);
      begin
         pragma Assert (Contains (S, 1));
         pragma Assert (Length (S) = 1);

         Intersection (K, L);
         pragma Assert (K = S);
      end;

      pragma Check (Proof_Only, False);
   end Large_Test;

   procedure Large_Test_Key is
      use N;
      use N.Formal_Model;
      use G;
      L, K : Set (50);
      C    : Cursor;
   begin

      Insert (L, (F => 1, G => 2));

      pragma Assert (Contains (L, 1));
      pragma Assert (not Contains (L, 2));

      Insert (L, (F => 2, G => 3));
      Insert (L, (F => 3, G => 4));
      Insert (L, (F => 5, G => 6));

      --  Ceilling & Floor

      C := Ceiling (L, 4);
      pragma Assert (C = Last (L));

      C := Floor (L, 4);
      pragma Assert (C = Previous (L, Last (L)));

      --  Delete

      K := L;
      Delete (L, 3);
      pragma Assert (G.Formal_Model.M_Included_Except (N.Formal_Model.Model (K), N.Formal_Model.Model (L), 3));
      pragma Assert (N.Formal_Model.M."<=" (N.Formal_Model.Model (L), N.Formal_Model.Model (K)));

      --  Element

      pragma Assert (G.Element (L, 2) = (F => 2, G => 3));

      --  Exclude

      L := K;

      Exclude (L, 10);
      pragma Assert (L = K);

      Exclude (L, 2);
      pragma Assert (G.Formal_Model.M_Included_Except (N.Formal_Model.Model (K), N.Formal_Model.Model (L), 2));
      pragma Assert (N.Formal_Model.M."<=" (N.Formal_Model.Model (L), N.Formal_Model.Model (K)));

      --  Key

      pragma Assert (Key (L, Last (L)) = 5);

      --  Replace

      Clear (L);
      Insert (L, (F => 1, G => 1));
      Insert (L, (F => 2, G => 2));
      Insert (L, (F => 3, G => 3));

      pragma Assert (G.Contains (L, 2));

      G.Replace (L, 2, (F => 4, G => 4));

      pragma Check (Proof_Only, False);
   end Large_Test_Key;
end Test_Set;
