with Ada.Numerics.Discrete_Random;
with Ada.Text_IO; use Ada.Text_IO;

procedure Test_Di_Bad2 with SPARK_Mode => On is

   package Random_Integer is new Ada.Numerics.Discrete_Random (Integer);
   use Random_Integer;

   G : Generator;
   X : Integer;

   function Get_Random (Gen : Generator) return Integer is
      Res : Integer;
   begin
      Res := Random (Gen);
      -- ERROR: constant object as "in" parameter of an access-to-variable type
      -- is not allowed in SPARK
      return Res;
   end Get_Random;

begin
   X := Get_Random (G);
   Put_Line ("X = " & Integer'Image (X));
end Test_Di_Bad2;
