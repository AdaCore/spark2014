procedure Test_Valid_Components with SPARK_Mode is
   type R1 is record
      F1 : Natural;
      F2 : Natural;
      F3 : Integer;
   end record;
   type R2 is record
      G1 : Integer;
      G2 : Integer;
   end record;
   type R3 is record
      H1 : R1;
      H2 : R2;
   end record;

   procedure Test_Access (X : R3) with
     Global => null,
     Potentially_Invalid => X;

   procedure Test_Access (X : R3) is
     I : Integer;
   begin
      pragma Assert (X.H1.F3'Valid);
      pragma Assert (X.H2'Valid_Scalars);
      I := X.H2.G1;
      pragma Assert (X.H1.F1'Valid); -- @ASSERT:FAIL
   end Test_Access;

   procedure Test_Update (X : in out R3) with
     Global => null,
     Potentially_Invalid => X;

   procedure Test_Update (X : in out R3) is
   begin
      X.H1.F1 := 1;
      X.H1.F3 := 1;
      X.H2.G2 := 1;
      pragma Assert (X'Valid_Scalars); -- @ASSERT:FAIL
   end Test_Update;
begin
   null;
end;
