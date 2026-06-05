with System.Storage_Elements; use System.Storage_Elements;
with System; use System;

procedure Minimal with SPARK_Mode is

   procedure Test_1 is
      function Id (X : Storage_Offset) return Storage_Offset is (X);

      X : Address := To_Address (127);
      Y : Storage_Offset := Id (-10);
   begin
      pragma Assert (X + Y /= To_Address (117)); --@ASSERT:FAIL
   end Test_1;

   procedure Test_2 is
      function Id (X : Storage_Offset) return Storage_Offset is (X);

      X : Address := To_Address (127);
      Y : Storage_Offset := Id (-10);
   begin
      pragma Assert (Y + X /= To_Address (117));  --@ASSERT:FAIL
   end Test_2;

   procedure Test_3 is
      function Id (X : Integer_Address) return Integer_Address is (X);

      X : Address := To_Address (127);
      Y : Address := To_Address (Id (130));
   begin
      pragma Assert (X - Y /= -3); --@ASSERT:FAIL
   end Test_3;

   procedure Test_4 is
      function Id (X : Integer_Address) return Integer_Address is (X);

      X : Address := To_Address (127);
      Y : Address := To_Address (Id (130));
   begin
      pragma Assert (Y - X /= 3); --@ASSERT:FAIL
   end Test_4;

   procedure Test_5 is
      function Id (X : Storage_Offset) return Storage_Offset is (X);

      X : Address := To_Address (127);
      Y : Storage_Offset := Id (10);
   begin
      pragma Assert (X mod Y /= 7); --@ASSERT:FAIL
   end Test_5;

begin
   null;
end Minimal;
