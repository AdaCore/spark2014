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
   pragma Assert (Y = 3);
   pragma Assert (R.C = 3);
end Inline_Init;
