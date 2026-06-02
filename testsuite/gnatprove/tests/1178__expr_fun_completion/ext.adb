package body Ext with SPARK_Mode is

   package Nested is
      function F return Boolean is (True);
   end Nested;

   package Nested_2 is
      function F return Boolean;
   end Nested_2;

   package body Nested_2 is
      function F return Boolean is (True);
   end Nested_2;

   package Nested_3 is
      function F return Boolean;
      function F return Boolean is (True);
   end Nested_3;

   procedure P is
   begin
      pragma Assert (Nested.F);   -- @ASSERT:PASS
      pragma Assert (Nested_2.F); -- @ASSERT:FAIL
      pragma Assert (Nested_3.F); -- @ASSERT:PASS
   end P;

end Ext;
