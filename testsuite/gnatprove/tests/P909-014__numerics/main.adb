with Ada.Text_IO; use Ada.Text_IO;
with Numerics;
with Numerics.Algo;

procedure Main is
   X21 : Numerics.T_Float;
   X22 : Numerics.T_Float;
   X23 : Numerics.T_Float;
   X24 : Numerics.T_Float;
   X25 : Numerics.T_Float;
begin
   Numerics.Algo.Algo (X => 0.0, X1 => X21, X2 => X22, X3 => X23, X4 => X24, X5 => X25);
   Put_Line ("X21 = " & Numerics.T_Float'Image (X21));
   Put_Line ("X22 = " & Numerics.T_Float'Image (X22));
   Put_Line ("X23 = " & Numerics.T_Float'Image (X23));
   Put_Line ("X24 = " & Numerics.T_Float'Image (X24));
   Put_Line ("X25 = " & Numerics.T_Float'Image (X25));
end Main;
