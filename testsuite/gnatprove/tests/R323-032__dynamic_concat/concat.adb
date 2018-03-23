procedure Concat with SPARK_Mode is
   function Id (X : Natural) return Natural is (X);

   V : Natural := Id (1);
   D : constant Natural := V;

   type Index is new Natural range D .. 8;

   type Nat_Array is array (Index) of Natural;

   A : Nat_Array := (others => 0);
   B : Nat_Array := (others => 1);

   C : Nat_Array := A (4 .. 7) & B (5 .. 8);
begin
   pragma Assert (C'First = 1);
   pragma Assert (C = (0, 0, 0, 0, 1, 1, 1, 1));
end;
