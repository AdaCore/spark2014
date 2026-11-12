procedure Main with SPARK_Mode is
   type A is array (Integer range <>, Integer range <>) of Integer;
   X : A := (1 .. 42 => (2 .. 36 => 454));
   Y : A := X'Update ((1,2) => 48, (4,5) => 62);
   function Random (X : Integer) return Boolean with Import, Global => null;
   procedure Test (X : A) with Pre => X'First (1) <= 42 and then X'Last (1) >= 43 and then X'First (2) <= 5 and then X'Last (2) >= 7;
   procedure Test (X : A) is
      Y : A := X'Update ((42, --@INDEX_CHECK:PASS
                           6) => 42); --@INDEX_CHECK:PASS
      Z : A := X'Update ((42, --@INDEX_CHECK:PASS
                           8) => 42); --@INDEX_CHECK:FAIL
   begin
      null;
   end Test;
begin
   if Random (0) then
      declare
         Z : A := X'Update ((43, --@INDEX_CHECK:FAIL
                              3) => 2, --@INDEX_CHECK:PASS
                              (42, --@INDEX_CHECK:PASS
                              1) => 1); --@INDEX_CHECK:FAIL
      begin
         null;
      end;
   end if;
   pragma Assert (Y (1,2) = 48); --@ASSERT:PASS
   pragma Assert (Y (4,5) = 62); --@ASSERT:PASS
   pragma Assert (Y (4,3) = 454); --@ASSERT:PASS
   pragma Assert (Y (35,2) = 454); --@ASSERT:PASS
end Main;
