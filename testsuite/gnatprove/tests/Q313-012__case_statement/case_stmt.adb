with Ada.Text_IO;
procedure Case_Stmt with SPARK_Mode is
   type Color is (Red, Green, Blue);

   function One_Color return Color is
   begin
      return Red;
   end One_Color;

   procedure Print_Float (F : Float) is
   begin
      Ada.Text_IO.Put_Line (Float'Image (F));
   end Print_Float;

   C : Color := One_Color;
   Res : Float;
begin
   case C is
   when Red =>
      Res := 1.0;
   when Green =>
      Res := 2.0;
   when Blue =>
      Res := 3.0;
   when others =>
      -- Unreachable code
      null;
   end case;
   Print_Float (Res);
end Case_Stmt;
