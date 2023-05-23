with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Maps.Higher_Order;

procedure Check_HO_Pre with SPARK_Mode is

   --  Check that the notion of compatibility of access to functions work as
   --  expected.

   package My_Maps is new SPARK.Containers.Functional.Maps
     (String, String);
   use My_Maps;

   package HO is new My_Maps.Higher_Order;
   use HO;

   function Test_Bad (X : String; Y : String) return Boolean is
     (X'First = 1 and Y'Length <= 10);
   --  Test_Bad is not compatible with the equality on strings, as it will not
   --  return the same value on 2 equivalent keys.

   procedure P1 (M : Map) with Global => null is
   begin
      pragma Assert (Eq_Compatible (M, Test_Bad'Access)); --@ASSERT:FAIL
   end P1;

   function Test_OK (X : String; Y : String) return Boolean is
     (X'Length <= 10 and Y'First = 1);
   --  Test_OK is compatible with the equality on strings, as it will return
   --  the same value on 2 equivalent keys. The same restriction does not
   --  apply to elements.

   procedure P2 (M : Map) with Global => null is
   begin
      pragma Assert (Eq_Compatible (M, Test_OK'Access));
   end P2;

   function Value_Bad (X : String; Y : String) return Big_Integer is
     (To_Big_Integer (X'First) + To_Big_Integer (Y'Length));
   --  Value_Bad is not compatible with the equality on strings, as it will not
   --  return the same value on 2 equivalent keys.

   procedure P3 (M : Map) with Global => null is
   begin
      pragma Assert (Eq_Compatible (M, Value_Bad'Access)); --@ASSERT:FAIL
   end P3;

   function Value_OK (X : String; Y : String) return Big_Integer is
     (To_Big_Integer (X'Length) + To_Big_Integer (Y'First));
   --  Value_OK is compatible with the equality on strings, as it will return
   --  the same value on 2 equivalent keys. The same restriction does not
   --  apply to elements.

   procedure P4 (M : Map) with Global => null is
   begin
      pragma Assert (Eq_Compatible (M, Value_OK'Access));
   end P4;

begin
   null;
end Check_HO_Pre;
