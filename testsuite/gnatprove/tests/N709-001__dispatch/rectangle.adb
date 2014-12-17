package body Rectangle is

   procedure Get_Area (Rec : in out T; Result : out Natural) is
   begin
      if not Rec.Has_Stored_Area then
         Rec.Set_Area (Rec.Width * Rec.Height);
      end if;
      Result := Rec.Get_Stored_Area;
   end Get_Area;

   procedure Set_Width (Rec : in out T; Value : Natural) is
   begin
      Rec.Width := Value;
   end Set_Width;

   procedure Set_Height (Rec : in out T; Value : Natural) is
   begin
      Rec.Height := Value;
   end Set_Height;

end Rectangle;
