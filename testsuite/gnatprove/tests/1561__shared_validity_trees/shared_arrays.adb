procedure Shared_Arrays with SPARK_Mode is
   type A is array (Positive range <>) of Positive;
   type B is array (Positive range <>) of Positive;
   type C is array (1 .. 1) of A (1 .. 2);
   type D is array (1 .. 1) of B (1 .. 3);

   procedure Update_B (X : in out B) with
     Global => null, Potentially_Invalid => X,
     Pre => X'First = 5 and X'Last = 6;
   procedure Update_B (X : in out B) is
   begin
      X (5) := 1;
      pragma Assert (X (5)'Valid);
      pragma Assert (X (6)'Valid); -- @ASSERT:FAIL
   end Update_B;

   procedure Complete (X : in out C) with
     Global => null, Potentially_Invalid => X;
   procedure Complete (X : in out C) is
   begin
      X (1) (1) := 1;
      X (1) (2) := 1;
      pragma Assert (X'Valid_Scalars);
   end Complete;

   procedure Partial (X : in out D) with
     Global => null, Potentially_Invalid => X;
   procedure Partial (X : in out D) is
   begin
      X (1) (1) := 1;
      X (1) (2) := 1;
      pragma Assert (X'Valid_Scalars); -- @ASSERT:FAIL
      X (1) (3) := 1;
      pragma Assert (X'Valid_Scalars);
   end Partial;
begin
   null;
end Shared_Arrays;
