procedure Test with SPARK_Mode is

   --  Test counterexample generation for indexes on containers

   type Arr is array (1 .. 10) of Integer;
   type C is record
      H : Arr;
   end record with Iterable =>
     (First => First,
      Next => Next,
      Has_Element => Has_Element,
      Element => Element);

   function First (X : C) return Natural is (1);
   function Next (X : C; P : Natural) return Natural is (if P in 1 .. 9 then P + 1 else 0);
   function Has_Element (X : C; P : Natural) return Boolean is (P in 1 .. 10);
   function Element (X : C; P : Natural) return Integer is (X.H (P)) with
     Pre => Has_Element (X, P);

   A : C := (H => (others => 0));
begin
   A.H (5) := 1;
   pragma Assert (for all E of A => E = 0); -- @ASSERT:FAIL @COUNTEREXAMPLE
end;
