procedure Empty_Type (C : Natural) with SPARK_Mode is
   type Empty is new Integer range 1 .. C;
   pragma Annotate (GNATprove, Init_By_Proof, Empty);
   subtype My_Nat is Natural;

   type Rec is record
      F : Empty;
      G : My_Nat;
   end record;
   pragma Annotate (GNATprove, Init_By_Proof, Rec);

   procedure Update_G (X : in out Rec) with
     Pre => X.G'Valid_Scalars
   is
   begin
      pragma Assert (C > 0);  --@ASSERT:FAIL
      X.G := X.G / 5;
   end Update_G;

   Y : Empty;

   procedure Set_Y (B : Boolean) is
   begin
      if B then
         Y := 1; --@RANGE_CHECK:FAIL
      end if;
   end Set_Y;

   X : Rec;
begin
   X.G := 3;
   Update_G (X);
   Set_Y (True);
end Empty_Type;
