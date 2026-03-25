pragma Extensions_Allowed (All_Extensions);

procedure Test with SPARK_Mode
is
   procedure Test_OK is
      X : Integer := 0;
   begin
      X := 1;
      <<L>>
      X := 2;
      pragma Assert (X'At (L) = 1); -- @ASSERT:PASS
   end;

   procedure Test_RTE is
      X : Integer := 0;
   begin
      <<L>>
      X := 1;
      pragma Assert (Integer'(1 / X)'At (L) = 1); -- @DIVISION_CHECK:FAIL
   end;

   procedure Test_Multiple is
      X : Integer := 0;
   begin
      <<L1>>
      <<L2>>
      X := 1;
      <<L3>>
      X := 2;
      <<L4>>
      X := 3;
      <<L5>>
      X := 4;
      pragma Assert (X'At (L1) = 0); -- @ASSERT:PASS
      pragma Assert (X'At (L2) = 0); -- @ASSERT:PASS
      pragma Assert (X'At (L3) = 1); -- @ASSERT:PASS
      pragma Assert (X'At (L4) = 2); -- @ASSERT:PASS
      pragma Assert (X'At (L5) = 3); -- @ASSERT:PASS
   end;

   procedure Test_Assert_And_Cut is
      X : Integer := 0;
   begin
      <<L1>>
      <<L2>>
      X := 1;
      <<L3>>
      X := 2;
      pragma Assert (X'At (L1) = 0); -- @ASSERT:PASS
      pragma Assert (X'At (L2) = 0); -- @ASSERT:PASS
      pragma Assert (X'At (L3) = 1); -- @ASSERT:PASS
      pragma Assert_And_Cut (X = 2);
      <<L4>>
      X := 3;
      <<L5>>
      X := 4;
      pragma Assert (X'At (L1) = 0); -- @ASSERT:PASS
      pragma Assert (X'At (L2) = 0); -- @ASSERT:PASS
      pragma Assert (X'At (L4) = 2); -- @ASSERT:PASS
      pragma Assert (X'At (L5) = 3); -- @ASSERT:PASS
   end;

   procedure Test_Goto (B1, B2 : Boolean) is
      X : Integer := 0;
   begin
      <<L1>>
      X := 42;
      <<L2>>
      X := 1;
      if B1 then
         pragma Assert (X'At (L1) = 0); -- @ASSERT:PASS
         pragma Assert (X'At (L2) = 42); -- @ASSERT:PASS
         goto L4;
      end if;
      <<L3>>
      X := 2;
      if B2 then
         pragma Assert (X'At (L1) = 0); -- @ASSERT:PASS
         pragma Assert (X'At (L2) = 42); -- @ASSERT:PASS
         goto L5;
      end if;
      <<L4>>
      X := 3;
      <<L5>>
      X := 4;
      pragma Assert (X'At (L1) = 0); -- @ASSERT:PASS
      pragma Assert (X'At (L2) = 42); -- @ASSERT:PASS
      pragma Assert (X'At (L5) = (if B1 or not B2 then 3 else 2)); -- @ASSERT:PASS
   end;

   type R is record
      F, G : Positive;
   end record;

   procedure Test_Potentially_Invalid (X : in out R; B : Boolean) with
     Potentially_Invalid => X
   is
   begin
      <<L1>>
      X.F := 42;
      <<L2>>
      X.G := 1;
      declare
         X1 : constant R := X'At (L1) with Potentially_Invalid;
         X2 : constant R := X'At (L2) with Potentially_Invalid;
      begin
         pragma Assert (if B then X1.F'Valid); --  @ASSERT:FAIL
         pragma Assert (X2.F'Valid); --  @ASSERT:PASS
      end;
      pragma Assert (X'At (L2).F = 42); --  @ASSERT:PASS
   end;
begin
   null;
end;
