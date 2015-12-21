package Tetris with Elaborate_Body
is

   Y_Size : constant Natural := 16;
   subtype Y_Coord is Natural range 1 .. Y_Size;

   type Action is (None, Left, Right, Down);

end Tetris;
