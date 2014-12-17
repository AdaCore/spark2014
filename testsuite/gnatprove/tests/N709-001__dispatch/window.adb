package body Window is

   procedure Draw (Obj : Object.T'Class) is
   begin
      Total_Area := Total_Area - Obj.Get_Stored_Area;
   end Draw;

   procedure Prepare_To_Draw (Obj : in out Object.T'Class) is
      Tmp : Natural;
      pragma Unreferenced (Tmp);
   begin
      Obj.Get_Area (Tmp);
   end Prepare_To_Draw;

   procedure Draw_Large_Rectangle is
      Rec : Rectangle.T;
   begin
      Rec.Set_Width (10);
      Rec.Set_Height (10);
      Prepare_To_Draw (Rec);
      Draw (Rec);
   end Draw_Large_Rectangle;

end Window;
