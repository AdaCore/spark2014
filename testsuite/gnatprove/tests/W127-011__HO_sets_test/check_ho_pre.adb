with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Sets.Higher_Order;

procedure Check_HO_Pre with SPARK_Mode is

   --  Check that the notion of compatibility of access to functions work as
   --  expected.

   package My_Sets is new SPARK.Containers.Functional.Sets
     (String);
   use My_Sets;

   package HO is new My_Sets.Higher_Order;
   use HO;

   function Test_Bad (X : String) return Boolean is
     (X'First = 1);
   --  Test_Bad is not compatible with the equality on strings, as it will not
   --  return the same value on 2 equivalent elements.

   procedure P1 (M : Set) with Global => null is
   begin
      pragma Assert (Eq_Compatible (M, Test_Bad'Access)); --@ASSERT:FAIL
   end P1;

   function Test_OK (X : String) return Boolean is
     (X'Length <= 10);
   --  Test_OK is compatible with the equality on strings, as it will return
   --  the same value on 2 equivalent elements.

   procedure P2 (M : Set) with Global => null is
   begin
      pragma Assert (Eq_Compatible (M, Test_OK'Access));
   end P2;

   function Value_Bad (X : String) return Big_Integer is
     (To_Big_Integer (X'First));
   --  Value_Bad is not compatible with the equality on strings, as it will not
   --  return the same value on 2 equivalent elements.

   procedure P3 (M : Set) with Global => null is
   begin
      pragma Assert (Eq_Compatible (M, Value_Bad'Access)); --@ASSERT:FAIL
   end P3;

   function Value_OK (X : String) return Big_Integer is
     (To_Big_Integer (X'Length));
   --  Value_OK is compatible with the equality on strings, as it will return
   --  the same value on 2 equivalent elements.

   procedure P4 (M : Set) with Global => null is
   begin
      pragma Assert (Eq_Compatible (M, Value_OK'Access));
   end P4;

begin
   null;
end Check_HO_Pre;
