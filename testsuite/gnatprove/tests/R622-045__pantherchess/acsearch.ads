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


with AChess; use AChess;
with ACPiece; use ACPiece;
with ACChessBoard;  use ACChessBoard;

package ACSearch is


   procedure Check_Piece_Table with Inline => True;

   Infinity : constant Integer_Type := 1_000_000;

   -- Shortcut
   Zero_Depth : constant Depth_Type := Depth_Type'First;

   ----------------------------
   -- Move Reduction Factors --
   ----------------------------

   Full_Depth_Moves : constant Integer_Type := 2; -- LMR
   Reduction_Limit  : constant Integer_Type := 3; -- LMR
   R                : constant Integer_Type := 2; -- Null move Reduction

   Aspiration_Window_Error_Margin : constant Integer_Type := 33;


   function Move_Is_Null_Ok (Move : Move_Type) return Boolean with Inline => True;

   ---------------------------
   -- Extra time management --
   ---------------------------

   -- Save the root move of the principal variation
   -- and it's score and if it changes then consider
   -- the idea to think more. Try to allocate an extra
   -- time bound to the score difference.
   Last_Best_Move  : Move_Type;
   Last_Best_Score : Integer_Type;

   -------------------------
   -- Principal Variation --
   -------------------------

   type Collection_Type is array (Depth_Type'Range, Depth_Type'Range) of Move_Type;
   type Collection_Depth_Type is array (Depth_Type'Range) of Depth_Type;

   type Principal_Variation_Type is
      record
         Main_Line : Collection_Type;
         Depth     : Collection_Depth_Type;
         Score     : Integer_Type;
      end record;

   Principal_Variation : Principal_Variation_Type;

   ----------------------
   -- Search functions --
   ----------------------

   Following_Principal_Variation : Boolean;

--     Principal_Variation : array(Depth_Type'Range, Depth_Type'Range) of Move_Type;
--     Principal_Variation_Depth : array(Depth_Type'Range) of Depth_Type;
--     Principal_Variation_Score : Integer_Type;

   procedure Update_Principal_Variation
     (Move : in Move_Type; Ply : in Depth_Type) with Inline => True;


   Principal_Variation_Changes : Integer_Type;

   Search_Depth : Depth_Type;

   function Think return Move_Type;

   function Principal_Variation_Search
     (Max_Depth : in Depth_Type; Alpha, Beta : in Integer_Type; Allow_Null_Move : Boolean := True) return Integer_Type;
   function Quiescence_Search
     (Alpha, Beta : in Integer_Type) return Integer_Type;

   -- Static Exchange Evaluation
   function Static_Exchange_Evaluation (Move : in Move_Type) return Integer_Type with Inline => True;

   -- Called when thinking time has up, this
   -- procedure will undo to the beginning position
   procedure Rollback;

   -- Print PV to the console.
   procedure Print_Principal_Variation;

   -- Must be called first when program start
   procedure Initialize_Search_Data;

   -- Sort Moves by using a quicksort algorithm
--     procedure Quick_Sort (From, To : in Integer_Type) with Inline => True;

   -- Pick the next sorted move from the moves list and return
   procedure Prepare_Next_Move (From : in Integer_Type) with Inline => True;

   -- Order_Moves is called to find the PV and assign the
   -- highest score to the move who is the PV move.
   -- Then the 2nd best score is assigned at the killer move, if any
   type Sorting_Strategy_Type is (Normal, See_On_Captures, Mvv_Lva_On_Captures);
   procedure Order_Moves (Sorting_Strategy : in Sorting_Strategy_Type) with Inline => True;

--     -- While sorting moves, pick moves in priority order
--     -- A PV move is the move that has been found to be part
--     -- of a principal variation and should be searched first.
--     -- The any Killer move should be searched because they are
--     -- proved to fail soft. After that moves can have priority
--     -- due to some criteria. Checks should be searched first,
--     -- then captures, promotions and later other moves.
--     -- Moves without any information are "unknown".
--     -- Skip value is for move that can be skipped
--     type Priority_Type is
--       (PV, Killer_Move, High, Normal, Low, Unknown, Skip) with Size => 3;
--
--     type Search_Move_Type is
--        record
--           Move : Move_Type;
--           Score : Integer_Type;
--           Priority : Priority_Type;
--        end record;
--
--     -- While searching for the best move and collecting the PV
--     -- we want to keep moves ordered and play the "best" move first
--     -- to maximize cut-offs in alpha-beta search.
--     -- Moves are sorted here and a priority has given. Then, moves
--     -- are played from the highest priority to the lowest.
--     -- Moves that can be skipped will be skipped :-)
--     Search_Moves_List : array (Depth_Type'Range, Integer_Type range 1 .. 128) of Search_Move_Type;

   -- Moves must be ordered to perform more
   -- cut-offs and make tree-search faster.
   -- use MVV_LVA algorithm to do this
   -- but consider killer moves, principal variation score
   -- and history heuristic
   function Assign_Score (Move : in Move_Type) return Integer_Type with Inline => True;

   -- Decide if a capture is a "bad" capture.
   -- A bad capture is a capture made by a minor/major
   -- piece to an opponent piece protected by a pawn
   -- However, even if the opponent piece is pawn-protected
   -- we can considere a capture as "good" if the capturing
   -- piece is a minor while the captured is a major
   -- i.e. Knight takes a Queen...
   function Bad_Capture (Move : in Move_Type) return Boolean with
     Inline => True,
     Pre => Move.Captured in Chess_Piece_Type'Range;

   -- Detect pins by looking up on
   -- the Pin table
   function Pin (Captured, Capturing : in Piece_Type) return Pin_Type with Inline => True;


   procedure Clear_All_Euristics;

private

   Console_Output : Boolean := True;

   -- Order moves based on different sorting strategy
   procedure Order_Moves_Without_See with Inline => True;
   procedure Order_Moves_With_See_On_Captures with Inline => True;
   procedure Order_Moves_With_Mvv_Lva with Inline => True;


   -- Allocate pointer to order moves procedure
   type Order_Moves_Strategy_Access is access procedure;

   Order_Moves_By_Strategy     : constant array (Sorting_Strategy_Type'Range) of
     Order_Moves_Strategy_Access := (Normal              => Order_Moves_Without_See'Access,
                                     See_On_Captures     => Order_Moves_With_See_On_Captures'Access,
                                     Mvv_Lva_On_Captures => Order_Moves_With_Mvv_Lva'Access);

   ----------------------
   -- Killer Heuristic --
   ----------------------

   Killer_Heuristic    : array (Depth_Type'Range) of Move_Type;
   Killer_Score        : array (Depth_Type'Range) of Integer_Type;

   --  Any time a killer move has been found, update
   procedure Update_Killer_Moves
     (Move : in Move_Type; Score : in Integer_Type) with Inline => True;

   -- Assign a score for the MVV_LVA captures.
   -- MVV LVA is Most Valuable Victim, Least Valuable Attackers.
   -- i.e is based to the concept that capturing a queen with a pawn
   -- is a move that should be considered before capturing a pawn with a queen
   Mvv_Lva_Score_Table : array (Piece_Type'Range, Piece_Type'Range) of Integer_Type;

   -- Preload Pin data
   Pin_Type_Table : array (Piece_Type'Range, Piece_Type'Range) of Pin_Type;

   -- Keep cut-offs data by tracing piece movement on target squares
   -- History has been disabled due to some magical things that makes
   -- AdaChess stronger without it ;-)
   History_Heuristic : array (Square_Type'Range, Square_Type'range) of Integer_Type;

end ACSearch;
