with Rectangle;

procedure Draw is
   Rec : Rectangle.T;
begin
   Rec.Set_Width (10);
   -- Uses Rec as an IN OUT parameter, with its private part uninitialized

   Rec.Set_Height (10);
end Draw;
