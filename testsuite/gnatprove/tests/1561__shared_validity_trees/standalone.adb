procedure Standalone with SPARK_Mode is
   type A is array (1 .. 2) of Positive;
   type R is record
      F : Positive;
      Items : A;
   end record;
   type D is new R;
   procedure Partial (X : in out D) with
     Global => null, Potentially_Invalid => X;
   procedure Partial (X : in out D) is
   begin
      X.F := 1;
      pragma Assert (X.F'Valid);
      pragma Assert (X'Valid_Scalars); -- @ASSERT:FAIL
   end Partial;

   procedure Full (X : out D) with
     Global => null, Potentially_Invalid => X,
     Post => X'Valid_Scalars;
   procedure Full (X : out D) is
   begin
      X.F := 1;
      X.Items := (others => 1);
      pragma Assert (X'Valid_Scalars);
   end Full;
begin
   null;
end Standalone;
