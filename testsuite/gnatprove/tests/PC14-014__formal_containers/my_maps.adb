with Ada.Containers; use Ada.Containers;

package body My_Maps with SPARK_Mode is
   procedure Test_Map_Pos with Pre => True is
      use My_Maps.M;
      L, K : Map (10, Default_Modulus (10));
      C    : Cursor;
      B    : Boolean;
   begin
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
      use My_Maps.N;
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
      use My_Maps.N;
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

   procedure Test_Map is
   begin
      Test_Map_Pos;
      Test_Map_Rec;
      Test_Map_Rec_2;
   end Test_Map;
end My_Maps;
