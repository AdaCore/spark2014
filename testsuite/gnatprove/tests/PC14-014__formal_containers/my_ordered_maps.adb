with Ada.Containers; use Ada.Containers;

package body My_Ordered_Maps with SPARK_Mode is
   procedure Test_Map_Pos with Pre => True is
      use My_Ordered_Maps.M;
      L, K : Map (10);
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
      Insert (L, 4, 4);

      pragma Assert (Formal_Model.P.Get (Formal_Model.Positions (L), Floor (L, 1)) = 1);
      pragma Assert (Formal_Model.P.Get (Formal_Model.Positions (L), Floor (L, 3)) = 2);
      pragma Assert (Floor (L, 0) = No_Element);
      pragma Assert (Formal_Model.P.Get (Formal_Model.Positions (L), Ceiling (L, 1)) = 1);
      pragma Assert (Formal_Model.P.Get (Formal_Model.Positions (L), Ceiling (L, 3)) = 3);
      pragma Assert (Ceiling (L, 5) = No_Element);

      pragma Assert (not Contains (L, 3));
      Include (L, 3, 3);
      Insert (L, 5, 5);
      pragma Assert (Contains (L, 2));

      Delete_First (L);

      Delete_Last (L);
      Delete (L, 3);
      C := Find (L, 2);
      Delete (L, C);
      pragma Assert (not Contains (L, 2));
      C := Find (L, 2);
      Exclude (L, 2);
      pragma Assert (Contains (L, 4));
      Exclude (L, 4);
      pragma Assert (Length (L) = 0);
      Delete_First (L);
      Delete_Last (L);
      pragma Check (Proof_Only, False);
   end Test_Map_Pos;

   procedure Test_Map_Rec with Pre => True is
      use My_Ordered_Maps.N;
      L, K : Map (10);
      C    : Cursor;
      B    : Boolean;
   begin
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Next (L, C);

      Insert (L, (F => 1, G => 1), 1);
      Insert (L, (F => 2, G => 2), 2);
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
      pragma Assert (C /= No_Element);
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
      use My_Ordered_Maps.N;
      L, K : Map (10);
      C    : Cursor;
      B    : Boolean;
   begin
      pragma Assert (Is_Empty (L));
      C := First (L);
      C := Next (L, C);

      Insert (L, (F => 1, G => 1), 1);
      Insert (L, (F => 2, G => 2), 2);
      pragma Assert (Element (L, My_Rec'(F => 2, G => 4)) = 2);
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
      pragma Assert (C /= No_Element);
      Delete (L, C);
      pragma Assert (not Contains (L, (F => 2, G => 5)));
      C := Find (L, (F => 2, G => 6));
      Exclude (L, (F => 2, G => 7));
      pragma Assert (Contains (L, (F => 1, G => 8)));
      Exclude (L, (F => 1, G => 9));
      pragma Assert (Length (L) = 0);
      pragma Check (Proof_Only, False);
   end Test_Map_Rec_2;

   procedure Test_Ordered_Map is
   begin
      Test_Map_Pos;
      Test_Map_Rec;
      Test_Map_Rec_2;
   end Test_Ordered_Map;
end My_Ordered_Maps;
