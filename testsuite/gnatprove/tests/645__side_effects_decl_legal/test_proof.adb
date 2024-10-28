pragma Extensions_Allowed (On);

procedure Test_Proof with SPARK_Mode is

   function F (X : in out Integer) return Integer
     with Side_Effects,
          Pre => X < Integer'Last,
          Post => X = X'Old + 1
            and then F'Result = X'Old
   is
   begin
      X := X + 1;
      return X - 1;
   end F;

begin
   X : Integer := 0;
   Y : constant Integer := F(X);

   pragma Assert (X /= Y);

   --  The definition of Y cannot be assumed globally in an axiom, it needs to
   --  be propagated using contracts.

   declare
      function G return Integer is (Y) with
        Post => G'Result = 0;  --  unprovable
      function H return Integer is (Y) with
        Pre => Y = 0,
        Post => H'Result = 0; --  @POSTCONDITION:PASS
   begin
      C : constant Integer := G + H;
   end;
end Test_Proof;
