--  PantherChess - based on AdaChess Copyright (C) 2017-2018 Bill Zuercher
--
--  AdaChess - Cool Chess Engine
--
--  Copyright (C) 2013-2017 - Alessandro Iavicoli
--  Email: adachess@gmail.com - Web Page: http://www.adachess.com
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.
--
--  This program is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License
--  along with this program.  If not, see <http://www.gnu.org/licenses/>.

with Ada.Text_IO;
with Ada.Numerics.Discrete_Random;

with AChess; use AChess;
with ACPiece; use ACPiece;
with ACChessboard; use ACChessboard;


package ACEvaluate is

   Debug_BZ     : Ada.Text_IO.File_Type;
   Debug_Opened : boolean := False;


   subtype Score_Type is Integer_Type;

   type Game_Over_Value_Type is
     (In_Game, -- Game playing
      Checkmate,
      Stalemate,
      Draw_By_Insufficient_Material,
      Draw_By_Threefold_Repetitions,
      Draw_By_Perpetual_Check) with Size => 3;

   type Evaluation_Type is
      record
         Score      : Score_Type := 0;
         Game_Phase : Game_Over_Value_Type := In_Game;
      end record;
   pragma Pack (Evaluation_Type);

   -----------------
   -- Random Mode --
   -----------------

   subtype Random_Score_Type is Score_Type range -2 .. 2;

   package Score_Random is new Ada.Numerics.Discrete_Random (Random_Score_Type);
   use Score_Random;

   Score_Seed : Score_Random.Generator;
   Random_Mode : Boolean := False;

   ---------------------
   -- Game Over Score --
   ---------------------

   Mate      : constant Integer_Type := 32767;
   Draw      : constant Integer_Type := 0;

   -----------------
   -- Piece Score --
   -----------------

   Pawn_Score   : constant Integer_Type := 100;
   Knight_Score : constant Integer_Type := 300;
   Bishop_Score : constant Integer_Type := 305;
   Rook_Score   : constant Integer_Type := 500;
   Panther_Score  : constant Integer_Type := 425;
   Queen_Score  : constant Integer_Type := 900;
   King_Score   : constant Integer_Type := 30000;

   Piece_Score : array (Chess_Piece_Type'Range) of Integer_Type;

   -----------------
   -- Evaluations --
   -----------------

   procedure Initialize_Evaluation_Data;

   -- Evaluate statically the board for both sides
   -- and give a score of it.
   function Evaluate return Evaluation_Type;

   -- Count how many times a ChessBoard position occurred.
   -- Chess rules says that when a position comes for 3 times
   -- then the game is a Draw
   function Count_Repetitions return Integer_Type with Inline => True;

   Center_Distance_Factor : constant array (Chessboard'Range) of Integer_Type :=
     (0, 0,  0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0,  0,
      0, 0,  0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0,  0,
      0, 0,  0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0,  0,
      0, 0,  0, -20, -12, -10, -10, -10, -10, -10, -10, -12, -20, 0, 0,  0,
      0, 0,  0, -10,  -6,  -5,   0,   0,   0,   0,  -5,  -6, -10, 0, 0,  0,
      0, 0,  0, -10,   0,   0,   5,   5,   5,   5,   0,   0, -10, 0, 0,  0,
      0, 0,  0, -10,   0,   0,   5,  10,  10,   5,   0,   0, -10, 0, 0,  0,
      0, 0,  0, -10,   0,   0,   5,  10,  10,   5,   0,   0, -10, 0, 0,  0,
      0, 0,  0, -10,   0,   0,   5,   5,   5,   5,   0,   0, -10, 0, 0,  0,
      0, 0,  0, -10,  -6,  -5,   0,   0,   0,   5,  -5,  -6, -10, 0, 0,  0,
      0, 0,  0, -20, -12, -10, -10, -10, -10, -10, -10, -12, -20, 0, 0,  0,
      0, 0,  0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0,  0,
      0, 0,  0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0,  0,
      0, 0,  0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0,  0);

private

   -----------------
   -- Evaluations --
   -----------------

   procedure Reset_Evaluation_Data with Inline => True;

   function Insufficient_Material return Boolean with Inline => True;

   -----------------------------------------
   -- Work with distances between squares --
   -----------------------------------------

   -- Hold the number of moves required for a knight
   -- to move from a square to a target one.
   -- Assuming a completely empty board
   -- While for other pieces is easy to calculate
   -- distance at needed, for knight or Panther would be
   -- harder and that's why I use these tables.

   Knight_Distance_Table        : array (Chessboard_Type'Range, Chessboard_Type'Range) of Integer_Type;

   Panther_Distance_Table        : array (Chessboard_Type'Range, Chessboard_Type'Range) of Integer_Type;

   -- Pre-calculate the Knight_Distance_Table
   -- using an adapted Dijkstra algorithm
   procedure Fill_Knight_Distance_Table;

   procedure Fill_Panther_Distance_Table;

   -- Call Race function between two pieces (Piece and Opponent), places in their
   -- respectively square (Square, Opponent_Square), to get in a Target square.
   -- Race is called from Piece point of view
   type Distance_Match_Type is
     (Equals, -- Both Piece and Oppoent has same distance to target
      Closer, -- Piece gets faster than Opponent
      Farther, -- Piece gets slower than Opponent
      Winner, -- Opponent piece cannot get to target square
      Loser, -- Piece cannot get to Target square in any way
      Unreachable) -- Neither Piece nor Opponent can reach Target in any way
     with Size => 3;

   -- Calculate how many moves need a piece to reach
   -- the target square from its starting square
   -- As a trick, if you pass an empty piece
   -- the distance is calculated as cartesian
   -- distance (i.e. like the king moves)
   -- See https://en.wikipedia.org/wiki/Taxicab_geometry
   function Distance
     (Piece : in Piece_Type; Square, Target : in Square_Type)
      return Integer_Type with Inline => True;

   -- Calculate the race winner between two pieces,
   -- that is the one who can get faster on a certain square
   -- Compare Piece in Square VS Opponent in Opponent_Square
   -- in direction to Target
   -- Return value is based on Piece point of view
   function Race (Piece    : in Piece_Type; Square : in Square_Type;
                  Opponent : in Piece_Type; Opponent_Square : in Square_Type;
                  Target   : in Square_Type) return Distance_Match_Type with Inline => True;

   -- Pre-filled table with king distance from any position to any other.
   Distance_Table : array (Piece_Type'Range, Chessboard_Type'Range, Chessboard_Type'Range) of Integer_Type;

   ----------------------
   -- Type Definitions --
   ----------------------

   subtype Bonus_Type is Score_Type;
   subtype Penalty_Type is Score_Type;

   ----------------
   -- Game Phase --
   ----------------

   type Game_Phase_Type is
     (Opening, Middle_Game, End_Game)
     with Size => 2;

   Game_Phase          : Game_Phase_Type;
   Endgame_Score_Limit : constant Integer_Type := 2700;

   ---------------------------------------
   -- Attacks, Defend and Mobility Maps --
   ---------------------------------------

   Knight_Mobility : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 2, Middle_Game => 3, End_Game => 4);
   Bishop_Mobility : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 1, Middle_Game => 2, End_Game => 4);
   Panther_Mobility  : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 2, Middle_Game => 3, End_Game => 4);
   Rook_Mobility  : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 0, Middle_Game => 1, End_Game => 3);
   Queen_Mobility : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 0, Middle_Game => 0, End_Game => 2);

   Mobility_Value : array (Piece_Type'Range) of Integer_Type;

   Bishop_Pair    : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 25, Middle_Game => 35, End_Game => 50);


   ---------------------------
   -- Information Collector --
   ---------------------------

   -- Piece-Color-Table
   PCT : array (Piece_Type'Range, Color_Type'Range) of Integer_Type;

   White_Pawns_Counter   : Integer_Type;
   White_Knights_Counter : Integer_Type;
   White_Bishops_Counter : Integer_Type;
   White_Panthers_Counter  : Integer_Type;
   White_Rooks_Counter   : Integer_Type;
   White_Queens_Counter  : Integer_Type;

   Black_Pawns_Counter   : Integer_Type;
   Black_Knights_Counter : Integer_Type;
   Black_Bishops_Counter : Integer_Type;
   Black_Panthers_Counter : Integer_Type;
   Black_Rooks_Counter   : Integer_Type;
   Black_Queens_Counter  : Integer_Type;

   White_Minor_Score     : Integer_Type;
   White_Major_Score     : Integer_Type;
   Black_Minor_Score     : Integer_Type;
   Black_Major_Score     : Integer_Type;

   White_Minor_Counter : Integer_Type;
   White_Major_Counter : Integer_Type;
   Black_Minor_Counter : Integer_Type;
   Black_Major_Counter : Integer_Type;

   White_Potential     : Integer_Type;
   Black_Potential     : Integer_Type;

   White_Pawns_Rank       : array (Integer_Type range 0 .. 11) of Square_Type;
   Black_Pawns_Rank       : array (Integer_Type range 0 .. 11) of Square_Type;

   White_Pawns_Position   : array (Integer_Type range 1 .. 10) of Square_Type;
   White_Knights_Position : array (Integer_Type range 1 .. 12) of Square_Type;
   White_Bishop_Position  : array (Integer_Type range 1 .. 12) of Square_Type;
   White_Panthers_Position  : array (Integer_Type range 1 .. 12) of Square_Type;
   White_Rooks_Position   : array (Integer_Type range 1 .. 12) of Square_Type;
   White_Queens_Position  : array (Integer_Type range 1 .. 12) of Square_Type;

   Black_Pawns_Position   : array (Integer_Type range 1 .. 10) of Square_Type;
   Black_Knights_Position : array (Integer_Type range 1 .. 12) of Square_Type;
   Black_Bishop_Position  : array (Integer_Type range 1 .. 12) of Square_Type;
   Black_Panthers_Position  : array (Integer_Type range 1 .. 12) of Square_Type;
   Black_Rooks_Position   : array (Integer_Type range 1 .. 12) of Square_Type;
   Black_Queens_Position  : array (Integer_Type range 1 .. 12) of Square_Type;

   ---------------------
   -- Piece Score Map --
   ---------------------

   Pawn_Score_Map          : constant array (Game_Phase_Type'Range) of Score_Type
     := (Opening => 100, Middle_Game => 100, End_Game => 120);
   Knight_Score_Map        : constant array (Game_Phase_Type'Range) of Score_Type
     := (Opening => 310, Middle_Game => 315, End_Game => 330);
   Bishop_Score_Map        : constant array (Game_Phase_Type'Range) of Score_Type
     := (Opening => 315, Middle_Game => 320, End_Game => 335);
   Panther_Score_Map         : constant array (Game_Phase_Type'Range) of Score_Type
     := (Opening => 320, Middle_Game => 325, End_Game => 340);
   Rook_Score_Map          : constant array (Game_Phase_Type'Range) of Score_Type
     := (Opening => 520, Middle_Game => 530, End_Game => 550);
   Queen_Score_Map         : constant array (Game_Phase_Type'Range) of Score_Type
     := (Opening => 930, Middle_Game => 950, End_Game => 990);

   -----------------------------------------
   -- Pawn Structure: Bonus and penalties --
   -----------------------------------------

   Doubled_Pawn        : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 5, Middle_Game => 6, End_Game => 10);
   Doubled_Pawn_Half_Helded : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 6, Middle_Game => 8, End_Game => 14);
   Doubled_Pawn_Helded : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 7, Middle_Game => 10, End_Game => 20);
   Backward_Pawn       : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 5, Middle_Game => 10, End_Game => 15);
   Isolated_Pawn       : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 3, Middle_Game => 6, End_Game => 10);
   Isolated_Center_Pawn : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 5, Middle_Game => 10, End_Game => 15);
   Exposed_Pawn        : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 4, Middle_Game => 6, End_Game => 12);
   Pawn_Supporterd     : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 3, Middle_Game => 5, End_Game => 10);
   Passed_Pawn         : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 1, Middle_Game => 10, End_Game => 20);

   Pawn_Promotion_Potential : constant Bonus_Type := 700; -- only for endgame

   -- Positional Bonus on pieces in strong/weak square
   Knight_On_Weak_Square    : constant Bonus_Type := 3;
   Bishop_On_Weak_Square    : constant Bonus_Type := 2;
   Panther_On_Weak_Square     : constant Bonus_Type := 3;
   Rook_On_Weak_Square      : constant Bonus_Type := 1;

   -----------------
   -- Rook Scores --
   -----------------

   Rook_On_Open_File : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 10, Middle_Game => 15, End_Game => 20);
   Rook_On_Semi_Open_File : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 5, Middle_Game => 10, End_Game => 15);
   Rook_On_Seventh_Rank : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => -10, Middle_Game => 15, End_Game => 10); -- for use only for white rooks
   Rook_On_Second_Rank : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => -10, Middle_Game => 15, End_Game => 10); -- same as rook_on_seventh_rank (this is only for black)

   -------------
   -- Pattern --
   --------------

   Trapped_Bishop : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 120, Middle_Game => 100, End_Game => 70);
   Blocked_Bishop : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 30, Middle_Game => 30, End_Game => 20);
   Center_Pawn_Blocked : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 60, Middle_Game => 70, End_Game => 90);
   Trapped_Rook : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 40, Middle_Game => 30, End_Game => 130);

   Queen_Exposed : constant Penalty_Type := 25;

   -------------------------
   -- Piece Square Tables --
   -------------------------

   Reverse_Rank : array (Rank_1 .. Rank_8) of Integer_Type
     := (Rank_8, Rank_7, Rank_6, Rank_5, Rank_4, Rank_3, Rank_2, Rank_1);

   Out_Of_Bound : constant Square_Type := 0;

   -- PST are calculated by looking at rank of the pawn
   -- and then multiplied with its file PST value.
   -- Extra columns needed for
   Piece_File_PST : constant array (File_A - 1 .. File_J + 1) of Score_Type
     := (0, -2, -1, 0, +1, +2, +2, +1, 0, -1, -2, 0);
   Piece_Rank_PST : constant array (Rank_1 - 1 .. Rank_8 + 1) of Score_Type
     := (0, -1, 0, 1, 2, 2, 1, 0, -1, 0);


   Pawn_PST       : constant array (Chessboard_Type'Range) of Integer_Type :=
     (0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0,10,  20,  20,  20,  20,10, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 5,  10,  10,  10,  10, 5, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0,-10, -20, -20, -20, -20,-10, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0,-15, -30, -30, -30, -30,-15, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0);

   Knight_PST : constant array (Chessboard'Range) of Integer_Type :=
     (0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0, -20, -10, -10, -10, -10, -10, -10, -10, -10, -20, 0, 0, 0,
      0, 0, 0, -10,   0,   0,   0,   5,   5,   0,   0,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,   5,   5,   5,   5,   5,   5,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,   5,   5,  10,  10,   5,   5,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,  10,  10,  10,  10,  10,  10,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,  15,  15,  10,  10,  15,  15,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,   0,   0,   5,   5,   0,   0,   0, -10, 0, 0, 0,
      0, 0, 0, -20, -50, -10, -10, -10, -10, -10, -10, -50, -20, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0);


   Bishop_PST : constant array (Chessboard'Range) of Integer_Type :=
     (0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0,
      0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0,
      0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0,
      0, 0, 0, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, 0, 0, 0,
      0, 0, 0, -2,  4,  5,  5,  5,  5,  5,  5,  4, -2, 0, 0, 0,
      0, 0, 0, -2,  3,  3,  3,  5,  5,  3,  3,  3, -2, 0, 0, 0,
      0, 0, 0, -2,  1,  4,  4,  4,  4,  4,  4,  1, -2, 0, 0, 0,
      0, 0, 0, -2,  1,  4,  4,  4,  4,  4,  4,  1, -2, 0, 0, 0,
      0, 0, 0, -2,  3,  3,  3,  5,  5,  3,  3,  3, -2, 0, 0, 0,
      0, 0, 0, -2,  6,  3,  3,  1,  1,  3,  3,  6, -2, 0, 0, 0,
      0, 0, 0, -2, -2,-15,-15, -2, -2,-15,-15, -2, -2, 0, 0, 0,
      0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0,
      0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0,
      0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0);

   Panther_PST : constant array (Chessboard'Range) of Integer_Type :=
     (0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0, -20, -10, -10, -10, -10, -10, -10, -10, -10, -20, 0, 0, 0,
      0, 0, 0, -10,   0,   0,   0,   5,   5,   0,   0,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,   5,   5,   5,   5,   5,   5,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,   5,   5,  10,  10,   5,   5,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,  10,  10,  10,  10,  10,  10,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,  15,  15,  10,  10,  15,  15,   0, -10, 0, 0, 0,
      0, 0, 0, -10,   0,   0,   0,   5,   5,   0,   0,   0, -10, 0, 0, 0,
      0, 0, 0, -20, -50, -10, -10, -10, -10, -10, -10, -50, -20, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0);

--     Pawn_PST       : constant array (Chessboard_Type'Range) of Integer_Type :=
--       (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 5, 10, 15, 20, 20, 15, 10, 5, 0, 0,
--        0, 0, 4, 8, 12, 16, 16, 12, 8, 4, 0, 0,
--        0, 0, 3, 6, 9, 12, 12, 9, 6, 3, 0, 0,
--        0, 0, 2, 4, 6, 8, 8, 6, 4, 2, 0, 0,
--        0, 0, 1, 2, 3, 4, 4, 3, 2, 1, 0, 0,
--        0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
--
--     Knight_PST : constant array (Chessboard'Range) of Integer_Type :=
--       (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, -10, -5, -5, -5, -5, -5, -5, -10, 0, 0,
--        0, 0, -5, 0, 0, 3, 3, 0, 0, -5, 0, 0,
--        0, 0, -5, 0, 5, 5, 5, 5, 0, -5, 0, 0,
--        0, 0, -5, 0, 5, 10, 10, 5, 0, -5, 0, 0,
--        0, 0, -5, 0, 5, 10, 10, 5, 0, -5, 0, 0,
--        0, 0, -5, 0, 5, 5, 5, 5, 0, -5, 0, 0,
--        0, 0, -5, 0, 0, 3, 3, 0, 0, -5, 0, 0,
--        0, 0, -10, -5, -5, -5, -5, -5, -5, -10, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
--
--
--     Bishop_PST : constant array (Chessboard'Range) of Integer_Type :=
--       (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, -5, -5, -5, -5, -5, -5, -5, -5, 0, 0,
--        0, 0, -5, 10, 5, 10, 10, 5, 10, -5, 0, 0,
--        0, 0, -5, 5, 3, 12, 12, 3, 5, -5, 0, 0,
--        0, 0, -5, 3, 12, 3, 3, 12, 3, -5, 0, 0,
--        0, 0, -5, 3, 12, 3, 3, 12, 3, -5, 0, 0,
--        0, 0, -5, 5, 3, 12, 12, 3, 5, -5, 0, 0,
--        0, 0, -5, 10, 5, 10, 10, 5, 10, -5, 0, 0,
--        0, 0, -5, -5, -5, -5, -5, -5, -5, -5, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);


   PST        : array (Piece_Type'Range, Chessboard_Type'Range) of Integer_Type;


   Flip                : constant array (Chessboard'Range) of Integer_Type :=
     (0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0,
      0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0,
      0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0,
      0, 0, 0, A1, B1, C1, D1, E1, F1, G1, H1, I1, J1, 0, 0, 0,
      0, 0, 0, A2, B2, C2, D2, E2, F2, G2, H2, I2, J2, 0, 0, 0,
      0, 0, 0, A3, B3, C3, D3, E3, F3, G3, H3, I3, J3, 0, 0, 0,
      0, 0, 0, A4, B4, C4, D4, E4, F4, G4, H4, I4, J4, 0, 0, 0,
      0, 0, 0, A5, B5, C5, D5, E5, F5, G5, H5, I5, J5, 0, 0, 0,
      0, 0, 0, A6, B6, C6, D6, E6, F6, G6, H6, I6, J6, 0, 0, 0,
      0, 0, 0, A7, B7, C7, D7, E7, F7, G7, H7, I7, J7, 0, 0, 0,
      0, 0, 0, A8, B8, C8, D8, E8, F8, G8, H8, I8, J8, 0, 0, 0,
      0, 0, 0, 0,  0,  0,  0,  0,  0,   0,  0,  0,  0, 0, 0, 0,
      0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0,
      0, 0, 0, 0,  0,  0,  0,  0,  0,   0,  0,  0,  0, 0, 0, 0);


   Color_Board         : constant array (Chessboard'Range) of Color_Type :=
     (White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black,
      Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White,
      White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black,
      Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White,
      White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black,
      Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White,
      White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black,
      Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White,
      White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black,
      Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White,
      White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black,
      Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White,
      White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black,
      Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White, Black, White);


   -- Track material for sides to see if
   -- the score is concrete
   White_Has_Enough_Material : Boolean;
   Black_Has_Enough_Material : Boolean;

   -----------------
   -- King Safety --
   -----------------

   Kingside_Castle_Protection  : Bonus_Type := 10;
   Queenside_Castle_Protection : Bonus_Type := 15;
   Losed_Castle_Rights         : Penalty_Type := 10;
   No_Castle_Yet               : Penalty_Type := 5;
   Castle_Has_Spoiled          : Penalty_Type := 10;

   Open_File_Near_King        : Penalty_Type := 5;
   Open_File_In_Front_Of_King : Penalty_Type := 10;

   Pawn_Shield : constant array (Game_Phase_Type'Range) of Bonus_Type
     := (Opening => 10, Middle_Game => 15, End_Game => 0);
   Pawn_Moved_One_Square : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 5, Middle_Game => 10, End_Game => 0);
   Pawn_Moved_Two_Square : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 10, Middle_Game => 20, End_Game => 0);
   Pawn_Shield_Hole : constant array (Game_Phase_Type'Range) of Penalty_Type
     := (Opening => 20, Middle_Game => 30, End_Game => 0);

    -- Penalties for pawn shield hole after castle
--     Pawn_Shield           : constant Bonus_Type := 20;
--     Pawn_Moved_One_Square : constant Penalty_Type := 11;
--     Pawn_Moved_Two_Square : constant Penalty_Type := 23;
--     Pawn_Shield_Hole      : constant Penalty_Type := 39;

   -- Bonuses for pawn storm near opponent castle
   Pawn_Storm       : constant Bonus_Type := 15;
   Pawn_Storm_Close : constant Bonus_Type := 10;
   Pawn_Storm_Far   : constant Bonus_Type := 5;

    -- Look for king protection by pawn shields
   function Evaluate_White_Pawn_Shield (Square : in Square_Type) return Integer_Type with Inline => True;
   function Evaluate_Black_Pawn_Shield (Square : in Square_Type) return Integer_Type with Inline => True;

   function Evaluate_White_Pawn_Storm (Square : in Square_Type) return Integer_Type with Inline => True;
   function Evaluate_Black_Pawn_Storm (Square : in Square_Type) return Integer_Type with Inline => True;

    King_Square_Value   : constant array (Chessboard'Range) of Integer_Type :=
     (0, 0, 0,   0  , 0,  0,   0,   0,   0,   0,   0,   0,   0,  0, 0, 0,
      0, 0, 0,   0,   0,  0,   0,   0,   0,   0,   0,   0,   0,  0, 0, 0,
      0, 0, 0,   0,   0,  0,   0,   0,   0,   0,   0,   0,   0,  0, 0, 0,
      0, 0, 0, -55, -55, -89, -89, -89, -89, -89, -89, -55, -55, 0, 0, 0,
      0, 0, 0, -34, -34, -55, -55, -55, -55, -55, -55, -34, -34, 0, 0, 0,
      0, 0, 0, -21, -21, -34, -34, -34, -34, -34, -34, -21, -21, 0, 0, 0,
      0, 0, 0, -13, -13, -21, -21, -21, -21, -21, -21, -13, -13, 0, 0, 0,
      0, 0, 0,  -8,  -8, -13, -13, -13, -13, -13, -13,  -8,  -8, 0, 0, 0,
      0, 0, 0,  -5,  -5,  -8,  -8,  -8,  -8,  -8,  -8,  -5,  -5, 0, 0, 0,
      0, 0, 0,  -5,   5, -15, -50, -50, -50, -50, -15,   0,  -5, 0, 0, 0,
      0, 0, 0,  -5,  14, -10,  -5,   0,  -5,   0, -10,  14,  -5, 0, 0, 0,
      0, 0, 0,   0,   0,  0,   0,   0,   0,   0,   0,   0,   0,  0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0);

--     King_Square_Value   : constant array (Chessboard'Range) of Integer_Type :=
--       (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 2, 10, 4, 0, 0, 7, 10, 2, 0, 0,
--        0, 0, -3, -3, -5, -5, -5, -5, -3, -3, 0, 0,
--        0, 0, -5, -5, -8, -8, -8, -8, -5, -5, 0, 0,
--        0, 0, -8, -8, -13, -13, -13, -13, -8, -8, 0, 0,
--        0, 0, -13, -13, -21, -21, -21, -21, -13, -13, 0, 0,
--        0, 0, -21, -21, -34, -34, -34, -34, -21, -21, 0, 0,
--        0, 0, -34, -34, -55, -55, -55, -55, -34, -34, 0, 0,
--        0, 0, -55, -55, -89, -89, -89, -89, -55, -55, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
--        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

   King_End_Game_Square_Value : constant array (Chessboard'Range) of Integer_Type :=
     (0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0, -50, -30, -20, -20, -20, -20, -20, -20, -30, -50, 0, 0, 0,
      0, 0, 0, -30,   0,  10,  10,  10,  10,  10,  10,   0, -30, 0, 0, 0,
      0, 0, 0, -20,  10,  25,  25,  25,  25,  25,  25,  10, -20, 0, 0, 0,
      0, 0, 0, -20,  10,  25,  50,  50,  50,  50,  25,  10, -20, 0, 0, 0,
      0, 0, 0, -20,  10,  25,  50,  50,  50,  50,  25,  10, -20, 0, 0, 0,
      0, 0, 0, -20,  10,  25,  25,  25,  25,  25,  25,  10, -20, 0, 0, 0,
      0, 0, 0, -30,   0,  10,  10,  10,  10,  10,  10,   0, -30, 0, 0, 0,
      0, 0, 0, -50, -30, -20, -20, -20, -20, -20, -20, -30, -50, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0,
      0, 0, 0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0);

   ---------------------------------------
   -- Strategical bonuses and penalties --
   ---------------------------------------

   Castle_Pawn_Destroyed      : constant Penalty_Type := 22;
   Castle_Pawn_Corrupted      : constant Penalty_Type := 17;
   Castle_Pawn_Spoiled        : constant Penalty_Type := 8;
   King_Safety                : constant Bonus_Type := 10;
   King_Critical_Safety_Factor : constant Penalty_Type := 3;
   King_Forced_To_The_Corner  : constant Bonus_Type := 8;
   King_Exposed               : constant Penalty_Type := 11;

   -- Scale King safety accorting to opponent
   -- strength. The premise is that if opponent has
   -- not enough piece to attack then the King is
   -- safe.
   White_Threat_Factor       : Integer_Type;
   Black_Threat_Factor       : Integer_Type;
   King_Safety_Threat_Factor : constant Score_Type := 2750;
   --     King_Safety_Threat_Factor : constant Score_Type := 2800;

   Use_Attack_Near_King_Weight : constant Boolean := True;

   Attack_Weight : constant array (Integer_Type range 0 .. 8) of Integer_Type :=
     (0, 0, 10, 20, 35, 68, 94, 97, 99);

   Attack_Score  : constant array (Piece_Type'Range) of Integer_Type :=
     (Frame        => 0, Empty => 0,
      White_Pawn   => 5,
      White_Knight => 10,
      White_Bishop => 15,
      White_Panther  => 12,
      White_Rook   => 25,
      White_Queen  => 60,
      White_King   => 0,
      Black_Pawn   => 5,
      Black_Knight => 10,
      Black_Bishop => 15,
      Black_Panther  => 12,
      Black_Rook   => 25,
      Black_Queen  => 60,
      Black_King   => 0);

--     Attacks_Factor : constant Integer_Type := 100;
   Attacks_Factor : constant array (Game_Phase_Type'Range) of Integer_Type
     := (Opening => 1, Middle_Game => 100, End_Game => 80);

   Escape_Factor  : constant array (Integer_Type range 0 .. 8) of Integer_Type :=
     (0, 1, 2, 4, 6, 10, 20, 20, 20);

   -- In the endgame with no opponent major pieces, the attacker must be helped with its king
   King_Endgame_Help_Factor : constant array (Integer_Type range 1 .. 8) of Integer_Type :=
     (-50, -30, -10, 0, 10, 30, 50, 100);

   type Castle_Type is
     (No_Castle,       -- Castle not performed and available
      Castle_Losed,    -- Castle not performed, but losed the chance to do it
      Castle_Spoiled,  -- Castle done, but king position compromised
      Kingside_Castle,
      Queenside_Castle)
     with Size => 3;

   White_Castle : Castle_Type;
   Black_Castle : Castle_Type;

end Acevaluate;
