with Interfaces; use Interfaces;

procedure Test with SPARK_Mode is
   procedure Test_OK is
      X : constant Integer_16 := Integer_16'Last;
      Y : constant Integer_16 with Import,
        Address => X'Address,
        Potentially_Invalid;
   begin
      pragma Assert (Y'Valid); -- @ASSERT:PASS
   end;

   procedure Test_KO is
      X : constant Integer_16 := Integer_16'Last;
      Y : constant Integer_8 with Import,
        Address => X'Address,
        Size => 16,
        Potentially_Invalid;
   begin
      pragma Assert (Y'Valid); -- @ASSERT:FAIL
   end;

begin
   Test_OK;
   Test_KO;
end;
