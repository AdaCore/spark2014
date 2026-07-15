procedure Test_Access with SPARK_Mode is

   --  Same test, but with an access type as a cursor

   type Cst_Acc is not null access constant Natural;
   type Arr is array (1 .. 10) of Integer;
   type C is record
      H : Arr;
   end record with Iterable =>
     (First => First,
      Next => Next,
      Has_Element => Has_Element,
      Element => Element);
   function First (X : C) return Cst_Acc;
   function Next (X : C; P : Cst_Acc) return Cst_Acc;
   function Has_Element (X : C; P : Cst_Acc) return Boolean;
   function Element (X : C; P : Cst_Acc) return Integer with
     Pre => Has_Element (X, P);

   function First (X : C) return Cst_Acc is
   begin
      return new Natural'(1);
   end First;
   function Next (X : C; P : Cst_Acc) return Cst_Acc is
   begin
      if P.all in 1 .. 9 then
         return new Natural'(P.all + 1);
      else
         return new Natural'(0);
      end if;
   end Next;
   function Has_Element (X : C; P : Cst_Acc) return Boolean is (P.all in 1 .. 10);
   function Element (X : C; P : Cst_Acc) return Integer is (X.H (P.all));

   A : C := (H => (others => 0));
begin
   A.H (5) := 1;
   pragma Assert (for all E of A => E = 0); -- @ASSERT:FAIL @COUNTEREXAMPLE
end;
