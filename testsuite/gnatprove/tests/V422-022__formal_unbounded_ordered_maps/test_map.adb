with Ada.Containers; use Ada.Containers;
with Ada.Unchecked_Deallocation;

package body Test_Map with SPARK_Mode is

   procedure Test_Map_Pos with Pre => True is
      use Test_Map.M;
      L, K : Map;
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
      use Test_Map.N;
      L, K : Map;
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
      use Test_Map.N;
      L, K : Map;
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

   procedure Large_Test is
      use Test_Map.M;
      use Test_Map.M.Formal_Model;
      L, K : Map;
      C    : Cursor;

   begin

      --  "="

      pragma Assert (L = K);

      Insert (L, 1, 4);
      Insert (L, 4, 5);

      Insert (K, 1, 4);
      Insert (K, 4, 5);

      pragma Assert (L = K);

      Insert (L, 2, 1);
      pragma Assert (K /= L);

      Insert (K, 2, 2);
      pragma Assert (L /= K);

      --  Clear

      Clear (K);
      pragma Assert (Length (K) = 0);

      --  Constant reference

      C := First (L);
      Next (L, C);
      declare
         E : not null access constant Integer :=  Constant_Reference (L, C);
      begin
         pragma Assert (E.all = Element (L, C));
      end;

      pragma Assert (Constant_Reference (L, 1).all = 4);

      --  Copy

      declare
         Ca : Cursor := Find (L, 1);
         Cb : Cursor := Find (L, 4);
         Cc : Cursor := Find (L, 2);

      begin
         Clear (K);
         pragma Assert (K /= L);
         K := Copy (L);
         pragma Assert (K = L);
         pragma Assert (Element (L, Ca) = Element (K, Ca));
         pragma Assert (Element (L, Cb) = Element (K, Cb));
         pragma Assert (Element (L, Cc) = Element (K, Cc));
      end;

      --  Find (Formal)

      C := Find (L, 4);
      pragma Assert (Find (Keys (L), 4) = P.Get (Positions (L), C));

      --  First_Element

      Insert (L, 0, 9);
      pragma Assert (Formal_Model.K.Get (Keys (L), Formal_Model.K.First) = 0);
      pragma Assert (First_Element (L) = 9);

      --  First_Key

      pragma Assert (First_Key (L) = 0);

      --  Key

      pragma Assert (Key (L, Find (L, 1)) = 1);

      --  Last and Last_Element

      pragma Assert (Last_Element (L) = 5);
      pragma Assert (Last_Key (L) = 4);
      pragma Assert (Formal_Model.K.Get (Keys (L), Formal_Model.K.Last (Keys (L))) = 4);
      pragma Assert (Formal_Model.M.Get (Model (L), 4) = 5);

      --  Force Resize

      Clear (L);
      Clear (K);

      pragma Assert_And_Cut (Is_Empty (L) and Is_Empty (K));

      pragma Assert (for all J in 1 .. 101 => not Contains (L, J));
      for Idx in 1 .. 101 loop


         Insert (L, Idx, Idx);

         pragma Loop_Invariant (for all J in Idx + 1 .. 101 => not Contains (L, J));
         pragma Loop_Invariant (Length (L) = Count_Type (Idx));

         pragma Loop_Invariant (for all J of Keys (L) => J <= Idx);

         pragma Loop_Invariant (if Idx = 1
                                then Key (L, Last (L)) = 1
                                else Key (L, Last (L)) = Idx
                                       and then Key (L, Previous (L, Last (L))) = Idx - 1);

         pragma Loop_Invariant (Key (L, First (L)) = 1);
      end loop;

      --  Previous

      C := Last (L);
      pragma Assert (Key (L, C) = 101);
      Previous (L, C);
      pragma Assert (Key (L, C) = 100);

      C := First (L);
      pragma Assert (Key (L, C) = 1);
      Previous (L, C);
      pragma Assert (C = No_Element);
      Previous (L, C);
      pragma Assert (C = No_Element);

      --  Reference

      declare
         S : Map;
      begin
         Insert (S, 1, 4);
         Insert (S, 2, 5);

         declare
            Ref : access Integer := Reference (S, 2);
         begin
            pragma Assert (Ref.all = 5);

            Ref.all := 6;
         end;
         pragma Assert (Element (S, 2) = 6);

         C := Find (S, 2);

         declare
            Ref : access Integer := Reference (S, C);
         begin
            pragma Assert (Ref.all = 6);

            Ref.all := 7;
         end;

         pragma Assert (Element (S, C) = 7);
      end;
      pragma Check (Proof_Only, False);
   end Large_Test;
end Test_Map;
