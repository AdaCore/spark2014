pragma Check_Policy (Only_For_Proof, Ignore);

package body Indefinite_Unbounded_Tagged with
  SPARK_Mode
is
   function F (X : Integer) return T'Class is (T'Class(T'(C => X)));

   function Lt (Left, Right : T'Class) return Boolean is (T(Left).C < T(Right).C);
   package Sort is new Generic_Sorting ("<" => Lt);

   procedure Test is
      V : Vector (2);
   begin
      Clear (V);
      pragma Assert (Is_Empty (V));
      pragma Assert (V = Empty_Vector);

      Append (V, F(1));
      Append (V, F(2));
      Append (V, F(3));
      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 3);
      pragma Assert (Element (V, 1) = F(1));
      pragma Assert (Element (V, 2) = F(2));
      pragma Assert (Element (V, 3) = F(3));

      Reserve_Capacity (V, 10);

      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 3);
      pragma Assert (Capacity (V) >= 10);

      declare
         W : Vector := Copy (V);
      begin
         pragma Assert (not Is_Empty (W));
         pragma Assert (Length (W) = 3);
         pragma Assert (Element (W, 1) = F(1));
         pragma Assert (Element (W, 2) = F(2));
         pragma Assert (Element (W, 3) = F(3));

         Append (W, V);
         pragma Assert (not Is_Empty (W));
         pragma Assert (Length (W) = 6);
         pragma Assert (Element (W, 1) = F(1));
         pragma Assert (Element (W, 2) = F(2));
         pragma Assert (Element (W, 3) = F(3));
         pragma Assert (Element (W, 4) = F(1));
         pragma Assert (Element (W, 5) = F(2));
         pragma Assert (Element (W, 6) = F(3));

         Assign (W, Empty_Vector);
         pragma Assert (Is_Empty (W));
         pragma Assert (W = Empty_Vector);
      end;

      Replace_Element (V, 2, F(4));
      pragma Assert (Element (V, 1) = F(1));
      pragma Assert (Element (V, 2) = F(4));
      pragma Assert (Element (V, 3) = F(3));

      Swap (V, 1, 3);
      pragma Assert (Element (V, 1) = F(3));
      pragma Assert (Element (V, 2) = F(4));
      pragma Assert (Element (V, 3) = F(1));

      Delete_Last (V);
      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 2);
      pragma Assert (Element (V, 1) = F(3));
      pragma Assert (Element (V, 2) = F(4));

      Reverse_Elements (V);
      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 2);
      pragma Assert (Element (V, 1) = F(4));
      pragma Assert (Element (V, 2) = F(3));

      pragma Assert (First_Index (V) = 1);
      pragma Assert (Last_Index (V) = 2);
      pragma Assert (First_Element (V) = F(4));
      pragma Assert (Last_Element (V) = F(3));

      pragma Assert (Find_Index (V, F(0)) = No_Index);
      pragma Assert (Find_Index (V, F(4)) = 1);
      pragma Assert (Find_Index (V, F(4), 2) = No_Index);

      pragma Assert (Reverse_Find_Index (V, F(0)) = No_Index);
      pragma Assert (Reverse_Find_Index (V, F(4)) = 1);
      pragma Assert (Reverse_Find_Index (V, F(4), 2) = 1);

      pragma Assert (Contains (V, F(4)));
      pragma Assert (not Contains (V, F(0)));
      pragma Assert (Has_Element (V, 1));
      pragma Assert (not Has_Element (V, No_Index));
      pragma Assert (not Has_Element (V, 3));

      pragma Assert (not Sort.Is_Sorted (V));
      Sort.Sort (V);
      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 2);
      pragma Assert (Element (V, 1) = F(3));
      pragma Assert (Element (V, 2) = F(4));
      pragma Assert (Sort.Is_Sorted (V));

      Replace_Element (V, 1, Element (V, 2));

      pragma Check (Only_For_Proof, False);  --  @ASSERT:FAIL check absence of inconsistency
   end Test;

end Indefinite_Unbounded_Tagged;
