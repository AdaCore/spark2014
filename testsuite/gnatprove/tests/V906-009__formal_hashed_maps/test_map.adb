with SPARK.Containers; use SPARK.Containers;

package body Test_Map with SPARK_Mode is
   procedure Test_Map_Pos with Pre => True is
      use Test_Map.M;
      L, K : Map (10, Default_Modulus (10));
      C    : Cursor;
      B    : Boolean;
   begin
      --  Clear (L);
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Next (L, C);

      Insert (L, 1, 1);
      Insert (L, 2, 2);
      Insert (L, 1, 3, C, B);
      pragma Assert (not B);
      pragma Assert (Element (L, C) = 1);

      Replace_Element (L, C, 3);
      Replace (L, 1, 1);
      Formal_Model.Lift_Abstraction_Level (L);

      Assign (K, L);
      Move (L, K);

      pragma Assert (Contains (L, 1));
      Include (L, 1, 3);
      pragma Assert (not Contains (L, 3));
      Include (L, 3, 3);

      Delete (L, 3);
      C := Find (L, 2);
      Delete (L, C);
      pragma Assert (not Contains (L, 2));
      C := Find (L, 2);
      Exclude (L, 2);
      pragma Assert (Contains (L, 1));
      Exclude (L, 1);
      pragma Assert (Length (L) = 0);
      pragma Check (Proof_Only, False);
   end Test_Map_Pos;

   procedure Test_Map_Rec with Pre => True is
      use Test_Map.N;
      L, K : Map (10, Default_Modulus (10));
      C    : Cursor;
      B    : Boolean;
   begin
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Next (L, C);

      Insert (L, (F => 1, G => 1), 1);
      Insert (L, (F => 2, G => 2), 2);
      pragma Assert (Element (L, My_Rec'(F => 2, G => 4)) = 2);
      Insert (L, (F => 1, G => 1), 3, C, B);
      pragma Assert (not Contains (L, (F => 3, G => 4)));
      pragma Assert (not B);
      pragma Assert (Element (L, C) = 1);

      Replace_Element (L, C, 3);
      Replace (L, (F => 1, G => 1), 1);
      Formal_Model.Lift_Abstraction_Level (L);

      Assign (K, L);
      Move (L, K);

      pragma Assert (Contains (L, (F => 1, G => 1)));
      Include (L, (F => 1, G => 1), 3);
      pragma Assert (not Contains (L, (F => 3, G => 3)));
      Include (L, (F => 3, G => 3), 3);

      Delete (L, My_Rec'(F => 3, G => 3));
      C := Find (L, (F => 2, G => 2));
      Delete (L, C);
      pragma Assert (not Contains (L, (F => 2, G => 2)));
      C := Find (L, (F => 2, G => 2));
      Exclude (L, (F => 2, G => 2));
      pragma Assert (Contains (L, (F => 1, G => 1)));
      Exclude (L, (F => 1, G => 1));
      pragma Assert (Length (L) = 0);
      pragma Check (Proof_Only, False);
   end Test_Map_Rec;

   procedure Test_Map_Rec_2 with Pre => True is
      use Test_Map.N;
      L, K : Map (10, Default_Modulus (10));
      C    : Cursor;
      B    : Boolean;
   begin
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Next (L, C);

      Insert (L, (F => 1, G => 1), 1);
      Insert (L, (F => 2, G => 2), 2);
      Insert (L, (F => 1, G => 2), 3, C, B);
      pragma Assert (not Contains (L, (F => 3, G => 4)));
      pragma Assert (not B);
      pragma Assert (Element (L, C) = 1);

      Replace_Element (L, C, 3);
      Replace (L, (F => 1, G => 2), 1);
      Formal_Model.Lift_Abstraction_Level (L);

      Assign (K, L);
      Move (L, K);

      pragma Assert (Contains (L, (F => 1, G => 4)));
      Include (L, (F => 1, G => 3), 3);
      pragma Assert (not Contains (L, (F => 3, G => 4)));
      Include (L, (F => 3, G => 3), 3);

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
   end Test_Map_Rec_2;

   procedure Run_Test is
   begin
      Test_Map_Pos;
      Test_Map_Rec;
      Test_Map_Rec_2;
   end Run_Test;

   procedure Large_Test is
      use Test_Map.M;
      use Formal_Model;
      L, K : Map (10, Default_Modulus (10));
      C    : Cursor;

   begin

      -- Test equal

      pragma Assert (L = K);

      Insert (L, 3, 4);

      pragma Assert (L /= K);

      Insert (L, 4, 6);

      pragma Assert (not Contains (K, 4));
      Insert (K, 3, 4);
      Insert (K, 4, 6);

      pragma Assert (L = K);

      pragma Assert (for all E of L => E = 3 or E = 4);

      Insert (L, 5, 6);
      Insert (K, 6, 7);

      pragma Assert (L /= K);

      Insert (L, 6, 7);
      Insert (K, 5, 8);

      pragma Assert (L /= K);

      -- Assign

      Clear (K);
      Assign (L, K);
      pragma Assert (Is_Empty (L));

      --  Copy

      Insert (L, 1, 1);
      Insert (L, 3, 4);

      K := Copy (K);
      pragma Assert (Is_Empty (K));
      K := Copy (L);
      pragma Assert (K = L);
      pragma Assert (L = K);

      --  Exclude

      Exclude (K, 1);
      pragma Assert (Length (K) = 1);
      pragma Assert (Element (K, 3) = 4);

      --  Has_Element

      C := First (K);
      pragma Assert (Has_Element (K, C));
      Next (K, C);
      pragma Assert (not Has_Element (K, C));

      --  Key

      C := First (K);
      pragma Assert (Key (K, C) = 3);

      --  Find

      Insert (K, 2, 4);
      Insert (K, 1, 6);
      pragma Assert (Length (K) = 3);

      declare
         Tmp_Map : Map := K;
      begin
         Move (L, K);
         pragma Assert (Is_Empty (K));
         pragma Assert (L = Tmp_Map);
      end;

      --  Next

      --  Length (L) = 3

      C := First (L);
      pragma Assert (C /= No_Element);
      C := Next (L, C);
      pragma Assert (C /= No_Element);
      C := Next (L, C);
      pragma Assert (C /= No_Element);
      C := Next (L, C);
      pragma Assert (C = No_Element);

      --  Replace

      C := Find (L, 1);
      pragma Assert (Element (L, 1) = 6);
      pragma Assert (Element (L, C) = 6);

      Replace (L, 1, 2);
      pragma Assert (Element (L, 1) = 2);
      pragma Assert (Element (L, C) = 2);

      --  Force Resize

      Clear (K);
      pragma Assert_And_Cut (Is_Empty (K));
      pragma Assert ((for all Idx in 1 .. 7 => not Contains (K, Idx)));
      for J in 1 .. 6 loop
         Insert (K, J, J);

         pragma Loop_Invariant (Length (K) = Count_Type (J));
         pragma Loop_Invariant ((for all Idx in J + 1 .. 7 =>
                                  not Contains (K, Idx)));
      end loop;

      Insert (K, 7, 7);
      pragma Check (Proof_Only, False);
   end Large_Test;

end Test_Map;
