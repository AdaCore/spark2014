pragma SPARK_Mode (on);


package Tetris
is

   --  Logical coordinate system
   X_Size : constant Natural := 8;
   Y_Size : constant Natural := 16;
   subtype X_Coord is Natural range 1 .. X_Size;
   subtype Y_Coord is Natural range 1 .. Y_Size;


   type action_type is (none,left, right, down );
   subtype user_action_type is action_type range none..right;

   type Cell_Type is (Empty, I, O, J, L, S, T, Z);
   -- I: cyan, J: blue, L: white, O: yellow, S: green, T: magenta, Z: red)

   subtype Piece_Type is Cell_Type range I .. Z;



   type Cell is record
      Kind     : Cell_Type;
   end record;

   type Piece is record
      Kind     : Piece_Type;
      Y        : Y_Coord;
      X        : X_Coord;
   end record;

   type Row   is array (X_Coord) of Cell;
   type Board is array (Y_Coord) of Row;

   --  Pixel constants for graphical components
   Pxl_Width    : constant Natural := 10;
   Pxl_Origin_X : constant Integer := -40;
   Pxl_Origin_Y : constant Integer := 80;

   Start_X : constant X_Coord := X_Coord'last/2;
   Start_Y : constant Y_Coord := Y_Coord'first;

   function New_Board return Board;

   function New_Piece (Kind  : Piece_Type;
                       Pos_X : X_Coord;
                       Pos_Y : Y_Coord) return Piece;

   procedure Insert_Piece_In_Board (P: in Piece; B: in out Board);

   procedure Update_Graphics (P: in out Piece);

   procedure move_piece( The_Piece : in out Piece; Direction : in action_type)
     with pre=> is_valid_move(The_Piece,Direction)=true;


   function is_valid_move (The_Piece : in Piece;
                           Direction : in action_type) return boolean is
      (if (direction = down) and The_Piece.Y = Y_Coord'Last then false else true);

   function is_empty_cell (The_Board : in board;
                               Xpos  : in X_Coord;
                               Ypos  : in Y_Coord) return boolean is
      (if The_Board(Ypos)(Xpos).Kind = Empty then true else false);





end Tetris;
