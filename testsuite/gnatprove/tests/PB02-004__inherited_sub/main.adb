with Rec;

procedure Main is

   function Build_Rec (A : Rec.Enum) return Rec.Sub_Rec
      with Pre => True;

   function Build_Rec (A : Rec.Enum) return Rec.Sub_Rec is
      Z : Rec.Sub_Rec (A);
   begin
      return Z;
   end Build_Rec;

   X : Rec.Sub_Rec := Build_Rec (Rec.C);
begin
   null;
end Main;
