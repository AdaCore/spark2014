procedure MyLoops with SPARK_Mode is

   type Wrapper (Max : Natural) is record
      G : String (1 .. Max);
   end record;

   procedure Init_Arr (Y : out String) is
      Tmp1 : constant Integer := Y'First;
      Tmp2 : constant Integer := Y'Last;
      Z : String (Tmp1 .. Tmp2);
   begin
      null;
   end;

   procedure Init_Rec (X : out Wrapper) is
   begin
      Init_Arr (X.G);
   end;

begin
   null;
end;
