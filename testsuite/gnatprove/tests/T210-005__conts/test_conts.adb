with Ada.Containers; use Ada.Containers;
with SPARK.Containers.Formal.Doubly_Linked_Lists;
with SPARK.Containers.Formal.Ordered_Maps;
with SPARK.Containers.Formal.Ordered_Sets;
with SPARK.Containers.Formal.Hashed_Maps;
with SPARK.Containers.Formal.Hashed_Sets;

procedure Test_Conts (X : out Integer) with SPARK_Mode is
   package My_Lists is new SPARK.Containers.Formal.Doubly_Linked_Lists
     (Integer);
   package My_OrMaps is new SPARK.Containers.Formal.Ordered_Maps
     (Integer, Integer);
   package My_OrSets is new SPARK.Containers.Formal.Ordered_Sets
     (Integer);
   function Int_Hash (I : Positive) return Hash_Type is
     (Hash_Type (I));
   package My_HaMaps is new SPARK.Containers.Formal.Hashed_Maps
     (Positive, Integer, Int_Hash);
   package My_HaSets is new SPARK.Containers.Formal.Hashed_Sets
     (Positive, Int_Hash);

begin
   X := 0;
   declare
      use My_Lists;
      L : List (100);
      C : Cursor;
   begin
      Prepend (L, 1);
      C := First (L);
      Delete (L, C);
      if Is_Empty (L) then
         X := X + 1;
      end if;
   end;
   declare
      use My_OrMaps;
      L : Map (100);
      C : Cursor;
   begin
      Insert (L, 1, 1);
      C := First (L);
      Delete (L, C);
      if Is_Empty (L) then
         X := X + 1;
      end if;
   end;
   declare
      use My_HaMaps;
      L : Map (100, Default_Modulus (100));
      C : Cursor;
   begin
      Insert (L, 1, 1);
      C := First (L);
      Delete (L, C);
      if Is_Empty (L) then
         X := X + 1;
      end if;
   end;
   declare
      use My_OrSets;
      L : Set (100);
      C : Cursor;
   begin
      Insert (L, 1);
      C := First (L);
      Delete (L, C);
      if Is_Empty (L) then
         X := X + 1;
      end if;
   end;
   declare
      use My_HaSets;
      L : Set (100, Default_Modulus (100));
      C : Cursor;
   begin
      Insert (L, 1);
      C := First (L);
      Delete (L, C);
      if Is_Empty (L) then
         X := X + 1;
      end if;
   end;
   pragma Assert (X = 5);
end Test_Conts;
