--  This test ensures that we do not assume that overlays are in bounds outside
--  of their scope.

procedure P (A, B : Boolean; C, D : Integer) with SPARK_Mode, Pre => C /= D is

   Z : aliased Integer;

begin
   if A and B then
      declare
         subtype T1 is Integer range C .. D;
         X : T1 with Import, Address => Z'Address;
         subtype T2 is Integer range D .. C;
         Y : T2 with Import, Address => Z'Address;
      begin
         Z := 3;
         pragma Assert (False); -- Here the unsoundness is expected, both incompatible overlays are in scope
      end;
   elsif A then
      declare
         subtype T1 is Integer range C .. D;
         X : T1 with Import, Address => Z'Address;
      begin
         null;
      end;
   elsif B then
      declare
         subtype T2 is Integer range D .. C;
         Y : T2 with Import, Address => Z'Address;
      begin
         null;
      end;
   end if;
   Z := 3;
   pragma Assert (False); -- @ASSERT:FAIL -- Here the assertion should not be provable
end P;
