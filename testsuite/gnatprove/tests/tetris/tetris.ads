package Tetris with
  SPARK_Mode
is
   --  possible content of the board cells
   type Cell is (Empty, I, O, J, L, S, T, Z);

   --  subset of cells that correspond to a shape
   subtype Shape is Cell range I .. Z;

   --  subset of shapes that fits in a 3 x 3 box, that is, all expect I and O
   subtype Three_Shape is Cell range J .. Z;

   --  the board is a matrix of X_Size x Y_Size cells, where the origin (1,1)
   --  is at the top left corner

   X_Size : constant := 10;
   Y_Size : constant := 50;

   subtype X_Coord is Integer range 1 .. X_Size;
   subtype Y_Coord is Integer range 1 .. Y_Size;

   type Line is array (X_Coord) of Cell;
   type Board is array (Y_Coord) of Line;

   Cur_Board : Board;

   --  the current piece has a shape, a direction, and a coordinate for the
   --  top left corner of the square box enclosing the piece:
   --    a 2 x 2 box for shape O
   --    a 3 x 3 box for all shapes except I and O
   --    a 4 x 4 box for shape I

   subtype PX_Coord is Integer range -1 .. X_Size - 1;
   subtype PY_Coord is Integer range -1 .. Y_Size - 1;

   type Direction is (North, East, South, West);

   type Piece is record
      S : Shape;
      D : Direction;
      X : PX_Coord;
      Y : PY_Coord;
   end record;

   Cur_Piece : Piece;

   --  either a piece is falling, in which case Cur_Piece is set to this piece,
   --  or it has been included in the board, in which case Cur_Piece is
   --  ignored.

   type State is (Piece_Falling, No_Piece_Falling);

   Cur_State : State;

   --  orientations of shapes are taken from the Super Rotation System at
   --  http://tetris.wikia.com/wiki/SRS
   --    shape O has no orientation
   --    shape I has 4 orientations, which all fit in the 4 x 4 box
   --    shapes except I and O have 4 orientations, which all fit in the 3 x 3 box

   --  Note that Possible_I_Shapes and Possible_Three_Shapes should be accessed
   --  with Y component first, then X component, so that higher value for
   --  Direction correspond indeed to clockwise movement.

   subtype I_Delta is Integer range 0 .. 3;
   type Oriented_I_Shape is array (I_Delta, I_Delta) of Boolean;
   subtype Three_Delta is Integer range 0 .. 2;
   type Oriented_Three_Shape is array (Three_Delta, Three_Delta) of Boolean;

   --  orientations for I

   Possible_I_Shapes : constant array (Direction) of Oriented_I_Shape :=
     (((False, False, False, False), (True,  True,  True,  True),  (False, False, False, False), (False, False, False, False)),
      ((False, False, True,  False), (False, False, True,  False), (False, False, True,  False), (False, False, True,  False)),
      ((False, False, False, False), (False, False, False, False), (True,  True,  True,  True),  (False, False, False, False)),
      ((False, True,  False, False), (False, True,  False, False), (False, True,  False, False), (False, True,  False, False)));

   Possible_Three_Shapes : constant array (Three_Shape, Direction) of Oriented_Three_Shape :=
     (--  orientations for J
      (((True, False, False), (True,  True,  True),  (False, False, False)),
       ((False, True, True), (False,  True,  False),  (False, True, False)),
       ((False, False, False), (True,  True,  True),  (False, False, True)),
       ((False, True, False), (False,  True,  False),  (True, True, False))),

      --  orientations for L
      (((False, False, True), (True,  True,  True),  (False, False, False)),
       ((False, True, False), (False,  True,  False),  (False, True, True)),
       ((False, False, False), (True,  True,  True),  (True, False, False)),
       ((True, True, False), (False,  True,  False),  (False, True, False))),

      --  orientations for S
      (((False, True, True), (True,  True,  False),  (False, False, False)),
       ((False, True, False), (False,  True,  True),  (False, False, True)),
       ((False, False, False), (False,  True,  True),  (True, True, False)),
       ((True, False, False), (True,  True,  False),  (False, True, False))),

      --  orientations for T
      (((False, True, False), (True,  True,  True),  (False, False, False)),
       ((False, True, False), (False,  True,  True),  (False, True, False)),
       ((False, False, False), (True,  True,  True),  (False, True, False)),
       ((False, True, False), (True,  True,  False),  (False, True, False))),

      --  orientations for Z
      (((True, True, False), (False,  True,  True),  (False, False, False)),
       ((False, False, True), (False,  True,  True),  (False, True, False)),
       ((False, False, False), (True,  True,  False),  (False, True, True)),
       ((False, True, False), (True,  True,  False),  (True, False, False))));

   --  the configuration of the board and piece should always be valid, meaning
   --  the piece and the board should not overlap, and the piece should fit in
   --  the board limits.

   function Is_Empty (B : Board; Y : Integer; X : Integer) return Boolean is
      (X in X_Coord and then Y in Y_Coord and then B(Y)(X) = Empty);

   function No_Overlap (B : Board; P : Piece) return Boolean is
      (case P.S is
         when O => Is_Empty (B, P.Y, P.X) and then Is_Empty (B, P.Y, P.X + 1) and then
                   Is_Empty (B, P.Y + 1, P.X) and then Is_Empty (B, P.Y + 1, P.X + 1),
         when I =>
           (for all Y in I_Delta =>
              (for all X in I_Delta =>
                 (if Possible_I_Shapes (P.D) (Y, X) then Is_Empty (B, P.Y + Y, P.X + X)))),
         when Three_Shape =>
           (for all Y in Three_Delta =>
              (for all X in Three_Delta =>
                 (if Possible_Three_Shapes (P.S, P.D) (Y, X) then Is_Empty (B, P.Y + Y, P.X + X)))));

   function Valid_Configuration return Boolean is
      (if Cur_State = Piece_Falling then No_Overlap (Cur_Board, Cur_Piece));

   --  movements of the piece in the 3 possible directions

   type Action is (Move_Left, Move_Right, Move_Down, Turn_Counter_Clockwise, Turn_Clockwise);

   subtype Move_Action is Action range Move_Left .. Move_Right;
   subtype Turn_Action is Action range Turn_Counter_Clockwise .. Turn_Clockwise;

   function Turn_Direction (D : Direction; T : Turn_Action) return Direction is
      (case T is
         when Turn_Counter_Clockwise =>
           (if D = Direction'First then Direction'Last else Direction'Pred (D)),
         when Turn_Clockwise         =>
           (if D = Direction'Last then Direction'First else Direction'Succ (D)));

   function Move (P : Piece; A : Action) return Piece is
      (case A is
         when Move_Left   => P'Update (X => P.X - 1),
         when Move_Right  => P'Update (X => P.X + 1),
         when Move_Down   => P'Update (Y => P.Y + 1),
         when Turn_Action => P'Update (D => Turn_Direction (P.D, A)));

   procedure Do_Action (A : Action; Success : out Boolean) with
     Pre  => Valid_Configuration,
     Post => Valid_Configuration;

end Tetris;
