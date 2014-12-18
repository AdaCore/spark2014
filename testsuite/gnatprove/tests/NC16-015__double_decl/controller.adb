pragma SPARK_Mode (on);

with Tetris;        use Tetris;
pragma Elaborate_All(Tetris);
with Ada.Numerics.Discrete_Random;

package body Controller is

   package Random_Move is new Ada.Numerics.Discrete_Random (user_action_type);

   subtype Piece_count_type is Integer range 0..1000;

   Piece_count      : Piece_count_type := 0;
   Create_Piece     : boolean := true;
   Game_Board       : Board := New_Board;

   Test_Piece       : Piece;

   procedure Refresh_game is
   begin

      -- Create a new piece if last finished run
      if Create_Piece = true then
         if Tetris.is_empty_cell(The_Board => Game_Board,
                                 Xpos      => Start_X,
                                 Ypos      => Start_Y) then
            Create_Piece := false;
            Piece_count := Piece_count +1;
         end if;
      end if;

   end Refresh_game;

end Controller;
