------------------------------------------------------------------------------
--                                                                          --
--                             GNAT EXAMPLE                                 --
--                                                                          --
--                    Copyright (C) 2013-2014, AdaCore                      --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Interfaces.C; use Interfaces.C;

package Patris with
  SPARK_Mode => On,
  Abstract_State => (Game_State, Score_State, Best_Score_State),
  Initializes    => (Game_State, Score_State, Best_Score_State)
is
   type Score_T is mod 100_000;

   --  possible content of the board cells
   type Cell is (Empty, I, O, J, L, S, T, Z);

   --  subset of cells that correspond to a shape
   subtype Shape is Cell range I .. Z;

   --  subset of shapes that fits in a 3 x 3 box, that is, all expect I and O
   subtype Three_Shape is Cell range J .. Z;

   --  the board is a matrix of X_Size x Y_Size cells, where the origin (1,1)
   --  is at the top left corner

   X_Size : constant := 10;
   Y_Size : constant := 20;

   subtype X_Coord is Integer range 1 .. X_Size;
   subtype Y_Coord is Integer range 1 .. Y_Size;

   type Line is array (X_Coord) of Cell with Pack;
   type Board is array (Y_Coord) of Line;

   function Get_Board return Board
     with Global => (Input => Game_State);

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
   end record with Pack;

   function Get_Piece return Piece
     with Global => (Input => Game_State);

   function Get_Next_Piece return Piece
     with Global => (Input => Game_State);

   --  the game loops through the following states:
   --    . a piece is falling, in which case Cur_Piece is set to this piece
   --    . the piece Cur_Piece is blocked by previous fallen pieces in the
   --      board Cur_Board
   --    . the piece has been included in the board, which may contain complete
   --      lines that need to be deleted
   --    . complete lines have been deleted from the board

   type State is (Piece_Falling, Piece_Blocked, Board_Before_Clean,
                  Board_After_Clean, Game_Over);

   function Get_State return State
     with Global => (Input => Game_State);

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
      (X in X_Coord and then Y in Y_Coord and then B(Y)(X) = Empty)
   with Post => True;

   function Is_Complete_Line (L : Line) return Boolean is
     (for all X in X_Coord => L(X) /= Empty)
   with Post => True;

   function Is_Empty_Line (L : Line) return Boolean is
     (for all X in X_Coord => L(X) = Empty)
   with Post => True;

   function No_Complete_Lines (B : Board) return Boolean is
     (for all Y in Y_Coord => not Is_Complete_Line (B(Y)));

   function Is_Empty (B : Board) return Boolean is
      (for all Y in Y_Coord => Is_Empty_Line (B(Y)))
   with Ghost;

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

   function Valid_Configuration (Cur_Board : Board;
                                 Cur_State : State;
                                 Cur_Piece : Piece) return Boolean is
      (case Cur_State is
         when Piece_Falling | Piece_Blocked => No_Overlap (Cur_Board, Cur_Piece),
         when Board_Before_Clean => True,
         when Game_Over => True,
          when Board_After_Clean => No_Complete_Lines (Cur_Board));

   function Valid_Configuration return Boolean is
     (Valid_Configuration (Get_Board, Get_State, Get_Piece));
--       (case Get_State is
--           when Piece_Falling | Piece_Blocked => No_Overlap (Get_Board, Get_Piece),
--           when Board_Before_Clean => True,
--           when Game_Over => True,
--            when Board_After_Clean => No_Complete_Lines (Get_Board))
--     with Ghost;


   --  movements of the piece in the 3 possible directions

   type Action is (Move_Left, Move_Right, Move_Down, Turn_Counter_Clockwise, Turn_Clockwise);

   subtype Move_Action is Action range Move_Left .. Move_Right;
   subtype Turn_Action is Action range Turn_Counter_Clockwise .. Turn_Clockwise;

   function Turn_Direction (D : Direction; T : Turn_Action) return Direction is
      (case T is
         when Turn_Counter_Clockwise =>
           (if D = Direction'First then Direction'Last else Direction'Pred (D)),
         when Turn_Clockwise         =>
           (if D = Direction'Last then Direction'First else Direction'Succ (D)))
   with Post => True;

   function Move_Is_Possible (P : Piece; A : Action) return Boolean is
      (case A is
         when Move_Left   => P.X - 1 in PX_Coord,
         when Move_Right  => P.X + 1 in PX_Coord,
         when Move_Down   => P.Y + 1 in PY_Coord,
         when Turn_Action => True)
   with Post => True;

   function Move (P : Piece; A : Action) return Piece is
      (case A is
         when Move_Left   => P'Update (X => P.X - 1),
         when Move_Right  => P'Update (X => P.X + 1),
         when Move_Down   => P'Update (Y => P.Y + 1),
         when Turn_Action => P'Update (D => Turn_Direction (P.D, A)))
   with
     Pre => Move_Is_Possible (P, A);

   procedure Do_Action (A : Action; Success : out Boolean) with
     Pre  => Get_State = Piece_Falling and then
             Valid_Configuration,
     Post => Valid_Configuration;

   procedure Include_Piece_In_Board with
     Global => (In_Out => Game_State),
     Pre    => Get_State = Piece_Blocked and then
               Valid_Configuration,
     Post   => Get_State = Board_Before_Clean and then
               Valid_Configuration;
   --  transition from state where a piece is falling to its integration in the
   --  board when it cannot fall anymore.

   procedure Delete_Complete_Lines with
     Global => (In_Out => (Game_State, Score_State)),
     Pre    => Get_State = Board_Before_Clean and then
               Valid_Configuration,
     Post   => Get_State = Board_After_Clean and then
               Valid_Configuration;
   --  remove all complete lines from the board

   procedure Game_Reset with
     Global => (Output => (Game_State, Score_State)),
     Post => Get_State = Board_After_Clean and then
             Is_Empty (Get_Board) and then
             Valid_Configuration;

   procedure Set_Game_State (New_Board                     : Board;
                             New_Cur_State                 : State;
                             New_Cur_Piece, New_Next_Piece : Piece) with
     Global => (Output => (Game_State)),
     Pre => Valid_Configuration (New_Board, New_Cur_State, New_Cur_Piece),
     Post => Valid_Configuration;

   procedure Game_Step
     (Redraw_Board, Redraw_Score, Redraw_Current_Piece : out Boolean) with
     Pre  => Valid_Configuration,
     Post => Valid_Configuration;

   procedure Action_Request (A : Action) with
     Pre  => Valid_Configuration,
     Post => Valid_Configuration;

   function Get_Score return Score_T
     with Global => (Input => Score_State);

   procedure Set_Score (Score : Score_T) with
     Global => (In_Out => Score_State);

   function Get_Best_Score return Score_T
     with Global => (Input => Best_Score_State);

   procedure Set_Best_Score (Score : Score_T) with
     Global => (Output => Best_Score_State);

   function Get_Level return Score_T
     with Global => (Input => Score_State);

   procedure Set_Level (Lvl : Score_T) with
     Global => (In_Out => Score_State);

   function Get_Line_Counter return Score_T
     with Global => (Input => Score_State);

   procedure Set_Line_Counter (Lines : Score_T) with
     Global => (In_Out => Score_State);

   function Get_Step_Interval return Natural
     with Global => (Input => (Game_State, Score_State));
end Patris;
