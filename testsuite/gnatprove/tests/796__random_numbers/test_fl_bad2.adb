with Ada.Numerics.Float_Random; use Ada.Numerics.Float_Random;
with Ada.Text_IO;               use Ada.Text_IO;

procedure Test_Fl_Bad2 with SPARK_Mode => On is

   G : Generator;
   X : Float;

   function Get_Random (Gen : Generator) return Float is
      Res : Float;
   begin
      Res := Random (Gen);
      -- ERROR: constant object as "in" parameter of an access-to-variable type
      -- is not allowed in SPARK
      return Res;
   end Get_Random;

begin
   X := Get_Random (G);
   Put_Line ("X = " & Float'Image (X));
end Test_Fl_Bad2;
