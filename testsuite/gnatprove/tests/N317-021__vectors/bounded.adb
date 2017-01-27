pragma Check_Policy (Only_For_Proof, Ignore);

package body Bounded with
  SPARK_Mode
is

   function Lt (Left, Right : Integer) return Boolean is (Left < Right);
   package Sort is new Generic_Sorting ("<" => Lt);

   procedure Test is
      V : Vector (5);
   begin
      Clear (V);
      pragma Assert (Is_Empty (V));
      pragma Assert (V = Empty_Vector);
      pragma Assert (Capacity (V) = 5);

      Append (V, 1);
      Append (V, 2);
      Append (V, 3);
      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 3);
      pragma Assert (Capacity (V) = 5);
      pragma Assert (Element (V, 1) = 1);
      pragma Assert (Element (V, 2) = 2);
      pragma Assert (Element (V, 3) = 3);

      Reserve_Capacity (V, 3);

      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 3);
      pragma Assert (Capacity (V) = 5);

      declare
         W : Vector := Copy (V, 6);
      begin
         pragma Assert (not Is_Empty (W));
         pragma Assert (Length (W) = 3);
         pragma Assert (Capacity (W) = 6);
         pragma Assert (Element (W, 1) = 1);
         pragma Assert (Element (W, 2) = 2);
         pragma Assert (Element (W, 3) = 3);

         Append (W, V);
         pragma Assert (not Is_Empty (W));
         pragma Assert (Length (W) = 6);
         pragma Assert (Capacity (W) = 6);
         pragma Assert (Element (W, 1) = 1);
         pragma Assert (Element (W, 2) = 2);
         pragma Assert (Element (W, 3) = 3);
         pragma Assert (Element (W, 4) = 1);
         pragma Assert (Element (W, 5) = 2);
         pragma Assert (Element (W, 6) = 3);

         Assign (W, Empty_Vector);
         pragma Assert (Is_Empty (W));
         pragma Assert (W = Empty_Vector);
      end;

      Replace_Element (V, 2, 4);
      pragma Assert (Element (V, 1) = 1);
      pragma Assert (Element (V, 2) = 4);
      pragma Assert (Element (V, 3) = 3);

      Swap (V, 1, 3);
      pragma Assert (Element (V, 1) = 3);
      pragma Assert (Element (V, 2) = 4);
      pragma Assert (Element (V, 3) = 1);

      Delete_Last (V);
      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 2);
      pragma Assert (Capacity (V) = 5);
      pragma Assert (Element (V, 1) = 3);
      pragma Assert (Element (V, 2) = 4);

      Reverse_Elements (V);
      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 2);
      pragma Assert (Capacity (V) = 5);
      pragma Assert (Element (V, 1) = 4);
      pragma Assert (Element (V, 2) = 3);

      pragma Assert (First_Index (V) = 1);
      pragma Assert (Last_Index (V) = 2);
      pragma Assert (First_Element (V) = 4);
      pragma Assert (Last_Element (V) = 3);

      pragma Assert (Find_Index (V, 0) = No_Index);
      pragma Assert (Find_Index (V, 4) = 1);
      pragma Assert (Find_Index (V, 4, 2) = No_Index);

      pragma Assert (Reverse_Find_Index (V, 0) = No_Index);
      pragma Assert (Reverse_Find_Index (V, 4) = 1);
      pragma Assert (Reverse_Find_Index (V, 4, 2) = 1);

      pragma Assert (Contains (V, 4));
      pragma Assert (not Contains (V, 0));
      pragma Assert (Has_Element (V, 1));
      pragma Assert (not Has_Element (V, No_Index));
      pragma Assert (not Has_Element (V, 3));

      pragma Assert (not Sort.Is_Sorted (V));
      Sort.Sort (V);
      pragma Assert (not Is_Empty (V));
      pragma Assert (Length (V) = 2);
      pragma Assert (Capacity (V) = 5);
      pragma Assert (Element (V, 1) = 3);
      pragma Assert (Element (V, 2) = 4);
      pragma Assert (Sort.Is_Sorted (V));

      Replace_Element (V, 1, Element (V, 2));

      pragma Assert (Capacity (V) = 5);

      pragma Check (Only_For_Proof, False);  --  @ASSERT:FAIL check absence of inconsistency
   end Test;

end Bounded;
