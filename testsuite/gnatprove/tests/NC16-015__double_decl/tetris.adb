pragma SPARK_Mode (On);
package body Tetris

is

   function New_Board return Board
   is
   begin
      return Board' (others => (others => Cell' (Kind     => Empty)));
   end New_Board;

   function New_Piece (Kind : Piece_Type;
                       Pos_X : X_Coord;
                       Pos_Y : Y_Coord) return Piece
   is
   begin

      return Piece' (Kind     => Kind,
                     X        => Pos_X,
                     Y        => Pos_Y);
   end New_Piece;

   procedure Insert_Piece_In_Board (P: in Piece; B: in out Board) is
   begin
      B (P.Y) (P.X) := (Kind     => P.Kind);
   end Insert_Piece_In_Board;


   procedure Update_Graphics (P: in out Piece) is
   begin
      null;
   end Update_Graphics;

   procedure move_piece( The_Piece : in out Piece; Direction : in action_type)
   is
      Xnew : X_Coord := The_Piece.X;
      Ynew : Y_Coord := The_Piece.Y;
   begin
      case Direction is
         when Left  =>
            if Xnew > X_Coord'first then
               Xnew:= Xnew -1;
            end if;
         when Right =>
            if Xnew < X_Coord'last then
               Xnew:= Xnew +1;
            end if;
         when down  => Ynew := Ynew+1;
         when None  => null;
      end case;

      The_Piece.X := Xnew;
      The_Piece.Y := Ynew;


   end;


end Tetris;
