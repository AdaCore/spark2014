procedure Inline_Init with
  SPARK_Mode
is
   function Id (X : Integer) return Integer;

   type Rec is record
      C : Integer := Id (3);
   end record;

   function Id (X : Integer) return Integer is
   begin
      return X;
   end Id;

   R : Rec;
   Y : Integer := Id(3);
begin
   pragma Assert (Y = 3);         -- @ASSERT:PASS
   pragma Assert (R.C = Id (3));  -- @ASSERT:PASS
   --  The first assertion is proved because the call in declaration is inlined
   --  The second one is proved, because proof knows the default expression
end Inline_Init;
