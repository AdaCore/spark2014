with Ada;
with Ada.Containers;
with Ada.Containers.Formal_Indefinite_Doubly_Linked_Lists;

use Ada.Containers;
with Test_List;

with Ada.Text_IO; use Ada.Text_IO;

procedure Test with SPARK_Mode is
   package Lists is new Ada.Containers.Formal_Indefinite_Doubly_Linked_Lists (Element_Type => Natural);
   use Lists;
   L, K, M : List;
   C, D : Cursor;
   N : Natural;
begin

   Test_List.Run;

   Test_List.Large_Run;

   pragma Assert (Is_Empty (L));

   --  L : [1, 2, 3, 4, 5]

   for J in 1 .. 5 loop
      Append (L, J);
      Append (K, J);
   end loop;

   C := First (L);
   for J in 1 .. Length (L) loop
      pragma Assert (Element (L, C) = Natural (J));
      Next (L, C);
   end loop;

   pragma Assert (not Is_Empty (L));
   pragma Assert (Length (L) = 5);

   pragma Assert (L = K);

   pragma Assert (not (for some Cl in L =>
                         (for some Ck in K =>
                            (Element (L, Cl) = Element (K, Ck) and Cl /= Ck))));

   --  shulfle list cursor

   C := First (L);
   C := Next (L, C);

   --          C
   --  L : [1, 2, 3, 4, 5]

   Delete (L, C);

   C := Find (L, 3);
   Delete (L, C);

   pragma Assert (Length (L) = 3);

   C := First (L);
   pragma Assert (Element (L, C) = 1);
   N := 4;
   Next (L, C);
   while C /= No_Element loop
      pragma Assert (Element (L, C) = N);
      N := N + 1;
      Next (L, C);
   end loop;

   C := Find (L, 4);

   --          C
   --  L : [1, 4, 5]

   Insert (L, C, 2);
   Insert (L, C, 3);

   pragma Assert (L = K);

   pragma Assert (for some Cl in L =>
                     (for some Ck in K =>
                       (Element (L, Cl) = Element (K, Ck) and Cl /= Ck)));

   M := Copy (L);

   --  The indexes must be the same

   pragma Assert (Length (L) = Length (M));
   pragma Assert (M = L);
   C := First (L);
   D := First (M);
   while C /= No_Element and D /= No_Element loop
      pragma Assert (C = D);
      pragma Assert (Element (L, C) = Element (M, D));
      Next (L, C);
      Next (M, D);
   end loop;

   --  Make sure Assign is a weaker copy

   Clear (K);
   pragma Assert (Length (K) = 0);
   pragma Assert (Is_Empty (k));

   Assign (K, M);

   pragma Assert (M = M);
   pragma Assert (for some Cl in L =>
                     (for some Ck in K =>
                       (Element (L, Cl) = Element (K, Ck) and Cl /= Ck)));

   --  Test with sorting by hand

   --  L : [4, 2, 1]
   --  K : [7, 8, 5, 3, 6]

   Clear (L);
   Append (L, 4);
   Append (L, 2);
   Append (L, 1);

   Clear (K);
   Append (K, 8);
   Append (K, 7);
   Append (K, 5);
   Append (K, 3);
   Append (K, 6);

   C := Last (L);
   D := First (L);

   Swap (L, C, D);

   --  L : [1, 2, 4]
   --  K : [7, 8, 5, 3, 6]

   C := Last (L);
   D := Find (K, 3);

   Splice (L, C, K, D);

   --  L : [1, 2, 3, 4]
   --  K : [8, 7, 5, 6]

   C := First (K);
   D := Find (K, 7);

   --  L : [1, 2, 3, 4]
   --  K : [8, 7, 5, 6]
   --       C  D

   Swap_Links (K, C, D);

   --  L : [1, 2, 3, 4]
   --  K : [7, 8, 5, 6]
   --       D  C-> ->

   Next (K, C);
   Next (K, C);

   Splice (K, D, C);
   C := Last (K);
   Previous (K, D);
   Splice (K, D, C);

   --  L : [1, 2, 3, 4]
   --  K : [5, 6, 7, 8]

   Reverse_Elements (L);

   Splice (K, First (K), L);

   N := 1;
   C := First (K);
   while C /= No_Element loop
      pragma Assert (Element (K, C) = N);
      N := N + 1;
      Next (K, C);
   end loop;

   pragma Assert (Last_Element (K) = 8);
   pragma Assert (First_Element (k) = 1);

   D := Last (K);
   Previous (K, D);
   C := Reverse_Find (K, 8, D);

   pragma Assert (C = No_Element);

   C := Reverse_Find (K, 5, D);

   pragma Assert (Element (K, C) = 5);

   pragma Assert (Contains (K, 4));
   pragma Assert (not Contains (K, 9));

end Test;
