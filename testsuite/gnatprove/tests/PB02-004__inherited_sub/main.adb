with Rec;

procedure Main with SPARK_Mode is

   function Build_Rec (A : Rec.Enum) return Rec.Sub_Rec
      with Pre => True;

   function Build_Rec (A : Rec.Enum) return Rec.Sub_Rec is
      Z : Rec.Sub_Rec (A);
   begin
      return Z;
   end Build_Rec;

   function Build_Rec_OK (A : Rec.Enum) return Rec.Sub_Rec_OK
      with Pre => True;

   function Build_Rec_OK (A : Rec.Enum) return Rec.Sub_Rec_OK is
      Z : Rec.Sub_Rec_OK (A);
   begin
      return Z;
   end Build_Rec_OK;

   function Build_Arr (F, L : Natural) return Rec.Sub_Arr
      with Pre => True;

   function Build_Arr (F, L : Natural) return Rec.Sub_Arr is
      Z : Rec.Sub_Arr (F, L);
   begin
      return Z;
   end Build_Arr;

   X : Rec.Sub_Rec := Build_Rec (Rec.C);
   Y : Rec.Sub_Rec_OK := Build_Rec_OK (Rec.C);
   F : Rec.Sub_Arr := Build_Arr (1, 2);
begin
   null;
end Main;
