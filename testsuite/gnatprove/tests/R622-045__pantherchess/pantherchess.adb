--  pantherchess - based on AdaChess Copyright (C) 2017-2018 Bill Zuercher
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


--------------------------------------
-- Roadmap from Version 0.0 to 1.0: --
--------------------------------------

-- AdaChess v0.1
-- Hello World. Environment preparation and
-- ChessBoard description as array of 64 squares.

-- AdaChess v0.2
-- Basic set-up of chessboard, pseudo-moves piece generator

-- AdaChess v0.3
-- Play and Undo function. First primitive Evaluation function
-- helps for debug.

-- AdaChess v0.4
-- Added AlphaBeta searching algorithm

-- AdaChess v0.5
-- Implemented Sorting algorithm for moves.
-- Added HistoryHeuristic to help AlphaBeta doing more
-- cut offs. Added also a MVV-LVA score to capture moves.

-- AdaChess v0.6
-- Implemented the (Triangular) Principal Variation line
-- Move searching changed using iterative deepening.

-- Adachess v0.7
-- Added Quiescence after AlphaBeta searching

-- AdaChess v0.8
-- Move generator is completed with Castle, en-passant and
-- pawn promotion. Additionally, a first incomplete FEN
-- parser is developed

-- AdaChess v0.9
-- Implemented Zobrist hashing algorithm.
-- Implemented the fifty move rules, draw by three-fold repetitions
-- Implemented first, rudimental, time-support (only on 40 moves in 5 minutes)

-- AdaChess v1.0
-- Added a first, weak, Winboard protocol support

-- Benchmark for v1.0 are estimated as
-- 10000 NPS (Nodes per Second)


--------------------------------------
-- Roadmap from Version 1.0 to 2.0: --
--------------------------------------

-- AdaChess v1.1:
-- ChessBoard Implementation changed from array(1 .. 64) to array(1 .. 144)
-- All the code related to the ChessBoard has been rewritten according to
-- this new implementation. The 144 board is easier for maintenance.

-- AdaChess v1.2:
-- Piece implementation changed. Piece are now identified as integers and
-- differ from white/black. The new implementation involves constants to
-- recognize out-of-board squares and empty sqares.

-- AdaChess v1.3:
-- Some utility functions has been added. Those utilities helps to detect
-- which color stands on a certain square, if a square is empty and so on.
-- the complete list is:
-- function Is_White (Piece : in Integer) return Boolean with Inline => True;
-- function Is_Black (Piece : in Integer) return Boolean with Inline => True;
-- function Is_In_Board (Square : in Integer) return Boolean with Inline => True;
-- function Is_Piece (Piece : in Integer) return Boolean with Inline => True;
-- function Is_Empty (Square  : in Integer) return Boolean with Inline => True;
-- function Is_Capture (Move : in Move_Type) return Boolean with Inline => True;

-- AdaChess v1.4:
-- Added an array of pieces to loop through (for white and black). No more
-- time spent to loop through the whole ChessBoard, now just loop through
-- those array. Special function to Add, Delete and Lookup piece here help
-- to keep update all data.

-- AdaChess v1.5:
-- Thinking function improved with new features. Aspiration window added to the
-- iterative deepening loop and a small transposition table based on hash
-- to store some previous score calculation.
-- Added a Zero-Window-Search for some moves
-- The table for evaluation function has been removed.

-- AdaChess v1.6:
-- Evaluation function has been improved with a lot of new features. Current
-- evaluation looks for and assign bonus/penalties for:
-- 0) Default: Material and piece position
-- 1) Pawn structure, isolated pawns, and so on.
-- 2) Rooks position like rooks on open file, and so on.
-- 3) King safety. Bonus for Castling and for king protection.
-- 4) While in the opening, a strong penalies for piece not developed
-- 5) Encourage capture when in advantage of material
-- 6) Added a mobility check to find blocked pawns, blocked bishops, and so on
-- 7) Pinned piece detection
-- 8) Small improvements on positional play with weak square recognition
-- 9) Unprotected piece recognition

-- AdaChess v1.7:
-- Small improvements added to the code for find File/Ranks on a given square.
-- The new code use a table-driven algorithm. Tables added for Diagonal
-- and Anti-Diagonal too.

-- AdaChess v1.8:
-- Legality test improved. Legality test is now based from the king position
-- looking reverse to find attackers. The legality test is asked only in
-- certain position. Like when a (potential) absolutely pinned piece moves
-- but not along the same path as it's (potential) attacker.
-- However, the same idea has been applied to the Find_Attack function.

-- AdaChess v1.9:
-- Improved Xboard support with new commands and parameters recognition
-- Utility to parse input added. Time management improved with new features
-- and more advanced time-consumption while thinking.

-- AdaChess v2.0:
-- Perft and Divide test added.
-- Improved move sorting with Killer Moves recognition.
-- Late Move Reduction algorithm added to the search

-- AdaChess 2.1 has been release with some bug fixed
-- This version has been called with the name of the
-- Italian tournament "GSEI" (Gruppo Scacchi E Informatica,
-- Italian Chess and computer-chess club) because
-- it played first time on that event.
-- This 2.1 GSEI version is more or less 50 Elo point
-- stronger that the previous one.


-----------------------------------------------
-- Roadmap from Version 2.1 to the 2016.11.0 --
-----------------------------------------------

-- Starting from the 3rd release, AdaChess names will be named with
-- the current year-month-day as version. For example, a release target
-- with 2016.02.05 means a release released on 5th of february 2016.

-- While in the 2.0 and in the next 2.1 GSEI version a great work
-- has been done to improve the first release, now I focused in two
-- main aspects: the code optimization and other "transitionals" stuffs.
-- I mean that the focus has been shifted towards the code cleanup
-- as a better starting point for the next steps and special improvement
-- has been done to improve performance.
-- And, of course, bug fixing!

-- A big part of the code has been rewritten from scratch with
-- previous engine version as guideline.
-- The code is now cleaner and better documented than before to acheive
-- the closest idiomatic Ada types and structures.
-- You can see how much comment there are into the sources hoping
-- you'll find them helpful.

-- AdaChess v2015.1
-- New datatypes replace the previous ones for piece and square description.
-- Based on those new datatypes (and other minor changes), the Move description
-- and White/Black pieces array are lighter and faster then before.
-- Hashing methods has been updated accordingly

-- AdaChess v2015.2
-- Introduced a new move input/output engine with support for multiple
-- notations. AdaChess recognize input in Winboard/UCI, SAN and
-- in the Long Algebraic notations. AdaChess che switch output to your
-- favourite notations.
-- Gui connection and notation were moved in a specific package to open
-- AdaChess to many connection levels.

-- AdaChess 2015.3
-- Algorithms that find attacks and checks has been replaced with a new
-- idea based on pointer to functions and some other tricks.
-- Improved, also, the way to decide if a move must be analyzed to find if it
-- leaves the king in check. The analyze itself has been also improved.
-- While generating moves, the legality check is faster and, in the end,
-- the move generation speed increased.

----------------------------------------
-- Roadmap from Version 2015 to 2016: --
----------------------------------------

-- AdaChess 2016.01
-- The Evaluation has been improved. It takes into account all the basics
-- data like pawn structure, center-control, rook on the (semi-)open files.
-- In addition, the bishop mobility has been added in addition to the
-- trapped-bishop algorithm.
-- The King-Safety evaluation has been developed to take into account many
-- things like castle strength, pawn shield and pawn storm and a new important
-- improvement has been added by looking for attacks near king locations and
-- king escapes. This algorithm is a little "overtuned" in a way that the
-- engine can try sacrifices.

-- AdaChess v2016.03
-- Added check and pin recognition. AdaChess is able to recognize
-- if a move makes check, discovery check, double check or checkmate.
-- In the same way, AdaChess keeps information about pins. The engine
-- recognize if a move pins opponent pieces and if it is a relative
-- or absolute pin.
-- The move ordering algorithm has been update accordingly to those new
-- information and other parameters.

-- AdaChess v2016.06
-- Added SEE to improve quescence search. The static exchange evaluation
-- makes AdaChess faster in taking decisions in long capture sequences.
-- Currently the SEE is used only to take decisions in Quiescence. In
-- particular, a move that does not pass the SEE test is not searched
-- furthermore in Quiescence.

-- AdaChess v2016.07
-- Implemented a new, complete, transposition table for the engine.
-- The previous one was small and weak due to the fact that
-- was implementend inside the stack-memory. The new tables are
-- bigger and works well in endgames.

-- AdaChess v2016.08
-- Search has been improved with the Late Move Reduction algorithm and
-- with a Zero-Window search after a PV is detected
-- AdaChess can search 1-2ply deeper than before.

-- AdaChess v2016.08.12
-- The Pin recognition has beed disabled as move information.
-- However, the move generator has furthermore improved by looking
-- on absolute pinned piece while generating moves. The generator
-- uses this info to generate check-evasion if the king is in check or
-- moves that unlock the pinned piece if any.
-- Empirical data shows that the perft speed is 3x and search is 2x
-- (because of the slower-but-better evaluation) compared to the
-- old v2.1 of the engine.

-- AdaChess v2016.08.15
-- The Score assignment and the move ordering have been improved.
-- The move score looks for checks, moves outside/inside the center
-- of the board, and for bad captures.
-- The sorting algorithm can use three different strategies depending
-- on the situation. Currently, only "normal" and scoring by using a SEE
-- on capture are used. The third one is only for debug (uses MVV_LVA).

-- AdaChess v2016.11.06
-- The History_Heuristic has been disabled. Tuning discover that the
-- engine without the HH is stronger that with it.

-- AdaChess 2016.11.20
-- Added the "random" mode by assigning a +/-2 point to the
-- final score after evaluation.

-- AdaChess 2016.11.21
-- Fixed a small bug on LMR search on alpha-beta window

-- AdaChess 2016.12.24
-- Bug fix: removed the update of Transposition Table data inside
-- the Zero_Window_Search that made search instable

-- AdaChess 2016.12.26
-- Removed parameter Beta to the Zero_Window_Search (it is calculated
-- as Alpha + 1 as it is a zero-window)

-- AdaChess 2016.12.30
-- Time management moved into a separate task.
-- Also, some basic system information as provided

-- AdaChess 2017.01.04
-- Fixed a bug into the current move generator
-- New move generator specific for check evasions.
-- Verify if a check is a chekmate
-- Added new look to perft search that shows: nodes, captures, en-passant,
-- castles, promotions, checks and checkmates.

-- AdaChess 2017.01.14
-- Pins has been removed to from the move informations.
-- Testing showed that the engine is faster and a bit stronger
-- without it.

-- AdaChess 2017.01.11
-- Added depth information about quiescence search.

-- pantherchess 1st version: Modified AdaChess to add a 10x8 board (10 files, 8 ranks) and to add
-- the panther piece (2 for each side).  The panther( V ) moves as a Camel (3,1) leaper or as a Wazir( one step orthoganally).
-- pantherchess has random positions for the NVB, mirror symetric.  There are 6 posible positions.
-- pantherchess currently uses just the two positions that have all the pawns protected.


with AChess; use AChess;

with Ada.Exceptions;
with Ada.Text_IO;           use Ada.Text_IO;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Command_Line;      use Ada.Command_Line;

with ACCommunication;       use ACCommunication;
with ACPiece;               use ACPiece;
with ACChessboard;          use Acchessboard;
with ACSearch;              use Acsearch;
with ACEvaluate;            use ACEvaluate;
with ACIOUtils;             use ACIOUtils;
with ACFen;                 use ACFen;
with ACBook;                use ACBook;
with ACClock;               use ACClock;
with ACMultiprocessor;
with ACPonder;              use ACPonder;


procedure pantherchess is


   -----------------
   -- System_Info --
   -----------------

   procedure System_Info is
      use ACMultiprocessor;
   begin
   	  if Protocol=No_GUI_Connection then
         Ada.Text_IO.Put_Line( "#   " );
         Ada.Text_IO.Put_Line( "#   Number of CPU detected:" & CPU_Range'Image (Number_Of_CPUs));
         Ada.Text_IO.Put_Line( "#   " );
      end if;
   end System_Info;


   ------------
   -- Prompt --
   ------------

   procedure Prompt is
   begin
      Flush;
      Put( "#   pantherchess => " );
      Flush;
   end Prompt;


   -----------
   -- Usage --
   -----------

   procedure Usage is
   begin
      New_Line;
      Put_Line ("#  Usage:");
      New_Line;
   end Usage;

   -- forcemode is an xboard parameter that,
   -- when enabled, force engine to NOT do anything
   Forcemode : Boolean;

   -- Engine
   Engine : Color_Type := Black;

   -- user input and other stuffs
   Move          : Move_Type;
   Input         : Unbounded_String;
   Console_Input : String (1 .. 128);
   Last          : Natural;
   Params        : Parameter_Type;

   -- benchmarking engine
   Benchmark_Nps      : array (Integer_Type range 1 .. 5) of Node_Type;
   Benchmark_Best_Nps : Node_Type;

   Score : Integer_Type;

   Argc  : Integer;

   To_WB   : File_Type;
   From_WB : File_Type;



   procedure Initialize_Program is
   begin
      -------------------------
      -- Data Initialization --
      -------------------------

      -- Initialization functions must be called exactly in this order
      Init;
--      Ada.Text_IO.Put_Line ("Initial Setup : " & Acchessboard.Random_Setup_Type'Image(This_Random_Setup));
--      Ada.Text_IO.New_Line;

      Initialize_Evaluation_Data;
      Initialize_Search_Data;
      Init_Transposition_Table;
      Preload_Sliding_Direction;

      Set_Fixed_Time_Per_Move( 5.0 );

      Engine    := Black;
      Forcemode := False;

      Check_For_Legal := True;
      Check_For_Check := True;

      --Open_Book;

   end Initialize_Program;


   Is_Initialized_Program : boolean := False;
   Is_Setup               : boolean := False;

begin  --Pantherchess

   -- Set Protocol for debugging Winboard connection
--   Set_GUI_Communication_Protocol( No_Gui_Connection );
   Set_GUI_Communication_Protocol( Winboard );
   Set_Output_Notation( Winboard );

   -- open debug files
   begin
      Ada.Text_IO.Open( File => To_WB,
                        Mode => Out_File,
                        Name => "To_WinBoard.txt",
                        Form => "" );
   exception
      when Name_Error =>
         Ada.Text_IO.Create( File => To_WB,
                             Mode => Out_File,
                             Name => "To_WinBoard.txt",
                             Form => "");
   end;

   begin
      Ada.Text_IO.Open( File => From_WB,
                        Mode => Out_File,
                        Name => "From_WinBoard.txt",
                        Form => "" );
   exception
      when Name_Error =>
         Ada.Text_IO.Create( File => From_WB,
                             Mode => Out_File,
                             Name => "From_WinBoard.txt",
                             Form => "");
   end;

   Put_Line( To_WB, "This is the To_WinBoard file for debugging");
   Flush;
   Put_Line( From_WB, "This is the From_WinBoard file for debugging");
   Flush;

--   This_Random_Setup := Setup_RBVN;  -- temporary

   System_Info;
         if Is_Initialized_Program = False then
         	  System_Info;
            Initialize_Program;
            Is_Initialized_Program := True;
            Put_Line( To_WB, "Initialized NOW ");
            Flush;
         else
         	  Put_Line( To_WB, "Program initialized already" );
         	  Flush;
         end if;

   -----------------------------------
   -- Parse command line parameters --
   -----------------------------------

--   Put_Line( From_WB, To_String( Input ));
   Put_Line( "#  Argument_Count = " & Integer'Image(Argument_Count ));
   if Argument_Count > 0 then
      Argc := 1;
      while Argc <= Argument_Count loop
         if Argument (Argc) in "-n" | "--notation" then
            if Argc + 1 <= Argument_Count then
               if Argument (Argc + 1) = "winboard" then
                  Set_Output_Notation (Winboard);
               elsif Argument (Argc + 1) = "algebraic" or else Argument (Argc + 1) = "san" then
                  Set_Output_Notation (Algebraic);
                  Put_Line( "#   going to The_Console_Loop");
                  Set_GUI_Communication_Protocol( No_Gui_Connection );
                  goto The_Console_Loop;
               elsif Argument (Argc + 1) = "long algebraic" or else Argument (Argc + 1) = "long" then
                  Set_Output_Notation (Long_Algebraic);
                  Put_Line( "#   going to The_Console_Loop");
                  Set_GUI_Communication_Protocol( No_Gui_Connection );
                  goto The_Console_Loop;
               end if;
               Argc := Argc + 1;
            end if;

         elsif Argument (Argc) in "-m" | "--hash" then
            if Argc + 1 <= Argument_Count then
               Put_Line ("Reserve memory for hashing:" & Integer_Type'Image (Integer_Type'Value (Argument (Argc + 1))));
               Argc := Argc + 1;
            end if;
         end if;

         Argc := Argc + 1;
      end loop;
   end if;



   GUI_Loop:
   while True loop


      if History_Ply > 0 then
         null; --Close_Book;
      end if;
      -- On the engine turn of move
      if Side_To_Move = Engine and then Forcemode = False then

--           Ponder_Mode := Off;
--           Ada.Text_IO.Put_Line ("Engine side to move");
--
--           Ada.Text_IO.Put_Line ("Last move: " & Move_To_String (Last_Move_Made));
--           Ada.Text_IO.Put_Line ("Ponder mv: " & Move_To_String (Ponder_Move));
--
--           if Ponder_Mode = On and then Last_Move_Made = Ponder_Move then
--              Ada.Text_IO.Put_Line ("Ponder hit!");
--              Stop_Ponder;
--              Move := Principal_Variation.Main_Line (1, 1);
--              Ada.Text_IO.Put_Line ("Move pondered: " & Move_To_String (Move));
--
--           end if;

         Move := Think;

         Play (Move);
         Put_Line( To_WB, " Protocol = " & Communication_Protocol_Type'Image( Protocol ));
         if Protocol = Winboard then
            Put ("move ");
            Print_Move (Move, Winboard);
            New_Line;
            Flush;
         end if;

         Clear_All_Euristics;

      end if;

--         Clear_All_Euristics;

--           if Ponder_Mode = On then
--              Start_Ponder (Principal_Variation.Main_Line (1, 2));
--           end if;

--      end if;

      Generate_Moves;

--      if Protocol = No_Gui_Connection then
--         Display;
--      end if;

--      Generate_Moves;

--      if Protocol = No_Gui_Connection then
--         Prompt;
--      end if;

      ----------------------------------
      -- Read user input and parse it --
      ----------------------------------

      Get_Line( Console_Input, Last );
      Flush;
      Input  := To_Unbounded_String (Console_Input (1 .. Last));
      --Flush;
      Put_Line( From_WB, "Input received, " & To_String( Input ) & "  " & "Last = " & Integer'Image(Last));
      --Flush;
      Params := Parse_Input (To_String (Input));

      Put_Line( From_WB, To_String( Input ));
      Flush;
      Put_Line( To_WB, "<<<  " & To_String( Input ));
      Flush;
      ---------------------------------
      -- Scan input and do your work --
      ---------------------------------

      if To_String (Params.Command) = "quit" then
         --           abort Clock;
         return;
      end if;

      -- Check if a communication protocol must be activated

      if To_String (Params.Command) = "xboard" or else To_String (Params.Command) = "winboard" then
         Set_GUI_Communication_Protocol (Winboard);
         New_Line;
         Flush;

      elsif To_String (Params.Command) = "uci" then
         Set_GUI_Communication_Protocol (Uci);
         New_Line;
         Flush;
      end if;


      if Console_Input (1) = Ascii.Lf then
         -- Sometimes Xboard sends a new line to the engine
         -- Just skip this command
         null;

      elsif Console_Input (1) = '?' then
         Forcemode := False;
--         Engine    := Side_To_Move;
--         Move      := Think;
--         Forcemode := False;

      elsif To_String (Params.Command) = "ping" then
     	   Flush;
     	   declare
     	      Number_String : Unbounded_String;
     	   begin
     	   	  Number_String := Params.Params( 2 );
     	   	  Put_Line ( "pong " & To_String( Number_String ));
     	   end;
      Flush;

      elsif To_String (Params.Command) = "usage"
        or else To_String (Params.Command) = "help" then
         Usage;

      elsif To_String (Params.Command) = "protover" then
         Put_Line ("feature myname=""pantherchess""" );
         Flush;
         Put_Line ("feature done=1");
         Flush;


      elsif To_String (Params.Command) = "new" then
     	   Flush;
     	   if Is_Initialized_Program = False then
            System_Info;
            Initialize_Program;
            Is_Initialized_Program := True;
            Put_Line( To_WB, "Initialized NOW ");
            Flush;
         else
         	  Put_Line( To_WB, "Program initialized already" );
         	  Flush;
         end if;

     	   Put_Line( To_WB, "&&&Is_Setup is " & boolean'Image( Is_Setup ));
        if Is_Setup then
        	 null;
        else
          Put_Line( "feature ping=1 memory=1 usermove=0 setboard=1 debug=1 sigint=0 sigterm=0" );
          Flush;
          Put_Line( To_WB, "feature ping=1 memory=1 usermove=0 setboard=1 debug=1 sigint=0 sigterm=0" );
          Flush;
          Put_Line( "feature smp=1 reuse=0 draw=1 pause=0 nps=1 analyze=1 highlight=1");
          Flush;
          Put_Line( To_WB,  "feature smp=1 reuse=0 draw=1 pause=0 nps=1 analyze=1 highlight=1");
          Flush;
          Put_Line( "feature playother=1 san=0 colors=1 name=1");
          Flush;
          Put_Line( To_WB,  "feature playother=1 san=0 colors=1 name=1 piece=1");
          Flush;
          Put_Line( "feature option=""resign threshold -spin 0 0 10000""");
          Flush;
          Put_Line ("feature myname=""pantherchess""" );
          Flush;
          Put_Line( To_WB, "feature myname=pantherchess" );
          Flush;
          Put_Line( "feature variants=""pantherchess""");
          Flush;
          Put_Line( To_WB,  "feature variants=pantherchess");
          Flush;
          Put_Line( "variant pantherchess"  );
          Flush;
          Put_Line( To_WB, "variant pantherchess" );
          Flush;
         if Is_Initialized_Program = False then
         	System_Info;
            Initialize_Program;
            Is_Initialized_Program := True;
            Put_Line( To_WB, "Initialized NOW ");
            Flush;
         else
         	  Put_Line( To_WB, "Program initialized already" );
         	  Flush;
         end if;


         if Is_Setup = False then
            case This_Random_Setup is
            	 when Setup_RVBN =>
                  Put_Line( "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rxbnqknbxr/pppppppppp/10/10/10/10/PPPPPPPPPP/RXBNQKNBXR w KQkq - 0 1");
                  Flush;
                  --Put_Line( To_WB, "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rxbnqknbxr/pppppppppp/10/10/10/10/PPPPPPPPPP/RXBNQKNBXR w KQkq - 0 1");
                  --Flush;
                  --Is_Setup := True;
                  --Flush;
               when Setup_RBVN =>
                  Put_Line( "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rbxnqknxbr/pppppppppp/10/10/10/10/PPPPPPPPPP/RBXNQKNXBR w KQkq - 0 1");
                  Flush;
                  --Put_Line( To_WB, "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rbxnqknxbr/pppppppppp/10/10/10/10/PPPPPPPPPP/RBXNQKNXBR w KQkq - 0 1");
                  --Flush;
                  --Is_Setup := True;
                  --Flush;
               when Setup_RNBV =>
                  Put_Line( "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rnbxqkxbnr/pppppppppp/10/10/10/10/PPPPPPPPPP/RNBXQKXBNR w KQkq - 0 1");
                  Flush;
                  --Put_Line( To_WB, "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rnbxqkxbnr/pppppppppp/10/10/10/10/PPPPPPPPPP/RNBXQKXBNR w KQkq - 0 1");
                  --Flush;
                  --Is_Setup := True;
                  --Flush;
               when Setup_RNVB =>
                  Put_Line( "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rnxbqkbxnr/pppppppppp/10/10/10/10/PPPPPPPPPP/RNXBQKBXNR w KQkq - 0 1");
                  Flush;
                  --Put_Line( To_WB, "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rnxbqkbxnr/pppppppppp/10/10/10/10/PPPPPPPPPP/RNXBQKBXNR w KQkq - 0 1");
                  --Flush;
                  --Is_Setup := True;
                  --Flush;
               when Setup_RBNV =>
                  Put_Line( "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rbnxqkxnbr/pppppppppp/10/10/10/10/PPPPPPPPPP/RBNXQKXNBR w KQkq - 0 1");
                  Flush;
                  --Put_Line( To_WB, "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rbnxqkxnbr/pppppppppp/10/10/10/10/PPPPPPPPPP/RBNXQKXNBR w KQkq - 0 1");
                  --Flush;
                  --Is_Setup := True;
                  --Flush;
               when Setup_RVNB =>
                  Put_Line( "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rxnbqkbnxr/pppppppppp/10/10/10/10/PPPPPPPPPP/RXNBQKBNXR w KQkq - 0 1");
                  Flush;
                  --Put_Line( To_WB, "setup (PNBRQ................XKpnbrq................xk) 10x8+0_capablanca rxnbqkbnxr/pppppppppp/10/10/10/10/PPPPPPPPPP/RXNBQKBNXR w KQkq - 0 1");
                  --Flush;
                  --Is_Setup := True;
                  --Flush;
            end case;


            --Put_Line( "piece X& (0,1)(0,3)");
            Put_Line( "piece X& WH" );
            Flush;
            Put_Line( To_WB, "piece X& WH" );
            Flush;
            Is_Setup := True;
           end if;
         end if;
	         Put_Line( "post" );
	         Flush;
--	         Put_Line( "go" );

      elsif To_String (Params.Command) = "variant" then
     	   Flush;

      elsif To_String (Params.Command) = "new variant" then
      	 Flush;
         Engine      := Black;
	      Forcemode   := False;
         Random_Mode := False;
--         Put_Line( "go" );

      elsif To_String (Params.Command) = "variant pantherchess" then
         Flush;

         Engine      := Black;
	      Forcemode   := False;
         Random_Mode := False;
--         Put_Line( "White" );
--         Put_Line( "go" );



      elsif To_String (Params.Command) = "random" then
         Random_Mode := not Random_Mode;
         Put_Line( To_WB, "random" );

      elsif To_String (Params.Command) = "go" then
         Forcemode := False;
         Engine    := Side_To_Move;
         Forcemode := False;

      elsif To_String (Params.Command) = "white" then
         Engine    := Black;

      elsif To_String (Params.Command) = "black" then
         Engine := White;

      elsif To_String (Params.Command) = "force" then
         Forcemode := True;

      elsif To_String (Params.Command) = "move" then

         -- when user types a move like Ke3, e2e4, Nb1-c3, the parser
         -- engine can detect it and transform it by sending itself
         -- the "move" command and moving the input as parameter
         Move := Parse_Move (To_String (Params.Params (Params.Params'First)));
         Put_Line( To_WB, To_String (Params.Params (Params.Params'First)) );
         Flush;
         Play (Move);

      elsif To_String (Params.Command) = "usermove" then
         -- when user types a move like Ke3, e2e4, Nb1-c3, the parser
         -- engine can detect it and transform it by sending itself
         -- the "move" command and moving the input as parameter

         Move := Parse_Move (To_String (Params.Params (Params.Params'First)));
         Put_Line( To_WB, To_String (Params.Params (Params.Params'First)) );
         Flush;
         Play (Move);
--         Display;
--         Engine    := Black;
--         Put_Line( "post" );
--         Flush;
--         Forcemode := False;
--         Move      := Think;
        Generate_Moves;
        Move := Think;

      elsif To_String (Params.Command) = "undo" then
         Ply := Ply + 1; -- adjust undo
         Undo;
         Forcemode := True;

         ---------------------------
         -- Time control commands --
         ---------------------------

         -- TODO: replace with new version
         --        elsif To_String (Params.Command) = "level" then
         --           declare
         --              Number_Of_Moves : Integer_Type;
         --              Total_Time      : Duration;
         --              Increment       : Duration;
         --           begin
         --              if Params.Tokens = 3 then
         --                 Number_Of_Moves := Integer_Type'Value (To_String (Params.Params (Params.Params'First)));
         --                 Total_Time := 60 * Duration'Value (To_String (Params.Params (Params.Params'First + 1)));
         --                 Increment := Duration'Value (To_String (Params.Params (Params.Params'First + 2)));
         --                 Put_Line ("Moves     :" & Integer_Type'Image (Number_Of_Moves));
         --                 Put_Line ("Total_Time: " & Duration'Image (Total_Time));
         --                 Put_Line ("Increment : " & Duration'Image (Increment));
         --                 Set_Level (Number_Of_Moves => Integer (Number_Of_Moves),
         --                            Total_Time      => Total_Time,
         --                            Increment       => Increment);
         --              end if;
         --           end;


      elsif To_String (Params.Command) = "time" then
         declare
            Available_Time     : constant Duration := Duration'Value (To_String (Params.Params (Params.Params'First))) / 100.0;
            Time_For_Next_Move : constant Duration := (if History_Ply < 80 then Available_Time / 40 else Available_Time / 10);
         begin
            Update_Residual_Time_Per_Game (Available_Time);
            Set_Fixed_Time_Per_Move (Time_For_Next_Move);
         end;

         -- TODO: update with new version
      elsif To_String (Params.Command) = "otim" then
         Opponent_Time := (Duration'Value (To_String (Params.Params (Params.Params'First))) / 100.0);

      elsif To_String (Params.Command) = "st" then
         Set_Fixed_Time_Per_Move (Duration'Value (To_String (Params.Params (Params.Params'First))));

         -- TODO: update with new version
         --        elsif To_String (Params.Command) = "sd" then
         --           -- Force search to stop after a certain depth
         --           -- The Horizon does not affects quiescence nor
         --           -- other search extension: it just stop iterative.
         --           declare
         --              Horizon : Depth_Type;
         --           begin
         --              Horizon := 1 + Integer_Type'Value (To_String (Params.Params (Params.Params'First)));
         --              Set_Fixed_Depth (Horizon);
         --           end;
         ---------------
         -- Notations --
         ---------------

      elsif To_String (Params.Command) = "notation" then
         declare
            Notation_Input : String (1 .. 32);
            Length         : Natural;
         begin
            Put_Line ("Choose the engine output notation:");
            Put_Line ("* Winboard/Xboard");
            Put_Line ("* Algebraic/SAN");
            Put_Line ("* Long Algebraic");
            Put_Line ("* UCI");
            Put_Line ("Type the name of notation you want, in lowercase: ");
            Get_Line (Notation_Input, Length);
            if Notation_Input (1 .. Length) = "winboard" or else Notation_Input (1 .. Length) = "xboard"  then
               Set_Output_Notation (Winboard);
               Put_Line ("Switched to Winboard/Xboard output");

            elsif Notation_Input (1 .. Length) = "algebraic" or else Notation_Input (1 .. Length) = "san" then
               Set_Output_Notation (Algebraic);
               Put_Line ("Switched to Algebraic/SAN output");

            elsif Notation_Input (1 .. Length) = "long algebraic" then
               Set_Output_Notation (Long_Algebraic);
               Put_Line ("Switched to Long Algebraic output");

            else
               Put_Line ("Sorry I don't understand...");
            end if;
            New_Line;
         end;

      elsif To_String (Params.Command) = "book" then
         Move := Book_Move;

      elsif To_String (Params.Command) = "perft" then

         declare
            Check_For_Check_Status : constant Boolean := Check_For_Check;
            Check_For_Legal_Status : constant Boolean := Check_For_Legal;
         begin

            Check_For_Check := True;
            Check_For_Legal := True;

            if Params.Tokens = 2
              and then To_String (Params.Params (Params.Params'First + 1)) = "raw"
            then
               Check_For_Legal := False;
               -- Call perft on <raw> nodes
               Perft (Integer_Type'Value (To_String (Params.Params (Params.Params'First))));

            elsif Params.Tokens = 1 then
               Perft (Integer_Type'Value (To_String (Params.Params (Params.Params'First))));
            else
               Put_Line ("Usage: perft <depth> [raw|legal]");
            end if;

            Check_For_Legal := Check_For_Legal_Status;
            Check_For_Check := Check_For_Check_Status;
         end;

      elsif To_String (Params.Command) = "divide" then
         if Params.Tokens = 1 then
            Divide (Integer_Type'Value (To_String (Params.Params (Params.Params'First))));
         else
            Put_Line ("Usage: divide <depth>");
         end if;

      elsif To_String (Params.Command) = "fen" or else To_String (Params.Command) = "setboard" then
         Forcemode := True;
         --Close_Book;
         Put_Line ("Tokens: " & Integer'Image (Params.Tokens));
         Init_Transposition_Table;
         Fen_Init;
         Fen_Load_Pieces (To_String (Params.Params (Params.Params'First)));
         Fen_Load_Side_To_Move (To_String (Params.Params (Params.Params'First + 1)));
         Fen_Load_Castle_Flags (To_String (Params.Params (Params.Params'First + 2)));
         Fen_Load_En_Passant (To_String (Params.Params (Params.Params'First + 3)));
         Fen_Load_Fifty_Move_Counter (To_String (Params.Params (Params.Params'First + 4)));
         Fen_Load_Ply_Depth (To_String (Params.Params (Params.Params'First + 5)));

      elsif To_String (Params.Command) = "fensave" then
         declare
            Output : constant String := Fen_Save_To_String;
         begin
            Ada.Text_IO.Put_Line ("My output is: " & Output);
         end;

      elsif To_String (Params.Command) = "moves" then


         Check_For_Legal := True;
         Check_For_Check := True;
         Generate_Moves;
         --           Quick_Sort (1, Moves_Counter (Ply));
         Print_Moves_List;

      elsif To_String (Params.Command) = "sort" then

         New_Line;
         Put_Line ("Sorting with NORMAL strategy");

         Following_Principal_Variation := True;
         Order_Moves (Sorting_Strategy => Normal);

         declare
            Move : Move_Type;
         begin
            Print_Moves_List;
            Ada.Text_IO.Put_Line ("After sorting:");
            for I in 1 .. Moves_Counter (Ply) loop
               Prepare_Next_Move (I);
               Move := Moves_List (Ply, I);
               Print_Move (Move);
               Put (" => Score:" & Integer_Type'Image (Move.Score));
               New_Line;
            end loop;
         end;

         --           New_Line;
         --           Put_Line ("Sorting with SEE_ON_CAPTURE strategy");
         --           Generate_Moves;
         --           Order_Moves (Sorting_Strategy => See_On_Captures);
         --           Quick_Sort (1, Moves_Counter (Ply));
         --           Print_Moves_List;
         --           for I in 1 .. Moves_Counter (Ply) loop
         --              Print_Move (Moves_List (Ply, I));
         --              Put (" " & Integer_Type'Image (Moves_List (Ply, I).Score));
         --              New_Line;
         --           end loop;
         --
         --           New_Line;
         --           Put_Line ("Sorting with MVV_LVA_ON_CAPTURES strategy");
         --           Generate_Moves;
         --           Order_Moves (Sorting_Strategy => Mvv_Lva_On_Captures);
         --           Quick_Sort (1, Moves_Counter (Ply));
         --           Print_Moves_List;
         --           for I in 1 .. Moves_Counter (Ply) loop
         --              Print_Move (Moves_List (Ply, I));
         --              Put (" " & Integer_Type'Image (Moves_List (Ply, I).Score));
         --              New_Line;
         --           end loop;


      elsif To_String (Params.Command) = "see" then
         -- Test See data to see if a capture is
         -- a winning capture
         declare
            See_Score : Integer_Type;
         begin
            New_Line;
            Generate_Moves;
            for I in 1 .. Moves_Counter (Ply) loop
               Move := Moves_List (Ply, I);
               if Move.Captured /= Empty then
                  See_Score := Static_Exchange_Evaluation (Move);
                  Print_Move (Move);
                  Put (" see score:" & Integer_Type'Image (See_Score));
                  if See_Score > 0 then
                     Put (" (winning capture)");
                  elsif See_Score < 0 then
                     Put (" (losing capture)");
                  else
                     Put (" (equal capture)");
                  end if;
                  New_Line;
               end if;
            end loop;
         end;

      elsif To_String (Params.Command) = "dpt" then
         Display_Piece_Table;

      elsif To_String (Params.Command) = "evasion" then
         -- fen: k7/5r2/6N1/2B5/6N1/7B/8/4K1n1 w - - 0 1
         Generate_Check_Evasion;
         Print_Moves_List;

      elsif To_String (Params.Command) = "pin" then
         New_Line;
         Generate_Moves;
         for I in 1 .. Moves_Counter (Ply) loop
            Move := Moves_List (Ply, I);
            declare
               Pins : Pin_Type;
            begin
               Pins := Move_Pin_Opponent_Piece (Move);
               Print_Move (Move);
               Put (" ");
               Put_Line (Pin_Type'Image (Pins));
            end;
         end loop;

         New_Line (2);

         declare
            Direction : Integer_Type := 0;
         begin
            if Side_To_Move = White then
               for Square of White_Pieces loop
                  exit when Square = 0;
                  Direction := Is_Absolute_Pinned (Square);
                  Put_Line (Symbols (Chessboard (Square)) & Pc_Sqr (Square) & " pin dir:" & Integer_Type'Image (Direction));
               end loop;
            else
               for Square of White_Pieces loop
                  exit when Square = 0;
                  Direction := Is_Absolute_Pinned (Square);
                  Put_Line (Symbols (Chessboard (Square)) & Pc_Sqr (Square) & " pin dir:" & Integer_Type'Image (Direction));
               end loop;
            end if;
         end;

         ----------------
         -- Benchmarks --
         ----------------

      elsif To_String (Params.Command) = "benchmark" then
         --Close_Book;
         Display;
         Put_Line ("Benchmarking current displayed position for" & Integer_Type'Image (Benchmark_Nps'Last - Benchmark_Nps'First + 1));
         Flush;
         Benchmark_Best_Nps := 0;
         for Test in Benchmark_Nps'Range loop
            Put_Line ("Test number" & Integer_Type'Image (Test) & " of" & Integer_Type'Image (Benchmark_Nps'Last - Benchmark_Nps'First + 1));
            delay 2.0;
            Set_Fixed_Time_Per_Move (60.0);
            Move := Think;
            Put ("Nodes:" & Node_Type'Image (Nodes) & "; NPS:" & Node_Type'Image (Nodes / 60));
            New_Line;
            Flush;
            Benchmark_Nps (Test) := Nodes / 60;
            Clear_Transposition_Table;
         end loop;
         -- find best value
         for I in Benchmark_Nps'Range loop
            if Benchmark_Nps (I) > Benchmark_Best_Nps then
               Benchmark_Best_Nps := Benchmark_Nps (I);
            end if;
         end loop;
         Put_Line ("Best NPS:" & Node_Type'Image (Benchmark_Best_Nps));
         New_Line;
         --Open_Book;
         Clear_Transposition_Table;

      elsif To_String (Params.Command) = "bench" then
         declare
            Seconds : Duration;
         begin
            if Params.Tokens = 1 then
               Seconds := Duration'Value (To_String (Params.Params (Params.Params'First)));
            else
               Seconds := 30.0;
            end if;
            --Close_Book;
            Display;
            Put_Line ("Benchmarking current displayed position for" &  Integer'Image (Integer (Seconds)) & " seconds");
            Flush;
            delay 2.0;
            Set_Fixed_Time_Per_Move (Seconds);
            Move := Think;
            Put ("Nodes:" & Node_Type'Image (Nodes) & "; NPS:" & Node_Type'Image (Nodes / Node_Type (Integer (Seconds))));
            New_Line;
            Flush;
         end;

--       elsif To_String (Params.Command) = "pgn" then
--           Close_Book;
--           Open_Pgn;
--           Read_Pgn_Data;
--           Close_Pgn;
--           Open_Book;

      elsif To_String (Params.Command) = "eval" then
         Score := Evaluate.Score;
         Put_Line ("Score: " & Integer_Type'Image (Score));
         New_Line;

      elsif To_String (Params.Command) = "reps" then
         declare
            Repetitions : Integer_Type := Count_Repetitions;
         begin
            Ada.Text_IO.Put_Line ("Repetitions: " & Integer_Type'Image (Repetitions));
         end;

      end if;

      Flush;

      exit when Console_Input (1 .. Last) = "quit";

   end loop GUI_Loop;

   <<The_Console_Loop>>

   Put_Line( "#   in the Console_Loop" );

      -- Set Protocol for debugging Console
   Set_GUI_Communication_Protocol( No_Gui_Connection );
   Set_Output_Notation( algebraic );

   --This_Random_Setup := Setup_RBVN;  -- temporary

   System_Info;
         if Is_Initialized_Program = False then
         	  System_Info;
            Initialize_Program;
            Is_Initialized_Program := True;
            Put_Line( To_WB, "Initialized NOW ");
            Flush;
         else
         	  Put_Line( To_WB, "Program initialized already" );
         	  Flush;
         end if;

   Put_Line( "#   entering the Console_Loop" );

   Console_Loop:
   while True loop

      if History_Ply > 0 then
         Close_Book;
      end if;

      -- On the engine turn of move
      if Side_To_Move = Engine and then Forcemode = False then

         Move := Think;

         Play (Move);

         Clear_All_Euristics;

      end if;

      --Ada.Text_IO.Put_Line( "Protocol = " & Communication_Protocol_Type'Image( Protocol ));
      if Protocol = No_Gui_Connection then
         if Is_Initialized_Program = false then
            Initialize_Program;
            Is_Initialized_Program := true;
         end if;
         Display;
      end if;

      Generate_Moves;

      if Protocol = No_Gui_Connection then
         Prompt;
      end if;

--      Generate_Moves;



      ----------------------------------
      -- Read user input and parse it --
      ----------------------------------

      Get_Line (Console_Input, Last);

      Input  := To_Unbounded_String (Console_Input (1 .. Last));
      Params := Parse_Input (To_String (Input));

      Put_Line( From_WB, To_String( Input ));
      Flush;
      Put_Line( To_WB, "<<<  " & To_String( Input ));
      Flush;
      ---------------------------------
      -- Scan input and do your work --
      ---------------------------------

      if To_String (Params.Command) = "quit" then
         --           abort Clock;
         return;
      end if;


      if To_String (Params.Command) = "xboard" or else To_String (Params.Command) = "winboard" then
         Set_GUI_Communication_Protocol (Winboard);
         New_Line;
         Flush;


      elsif To_String (Params.Command) = "uci" then
         Set_GUI_Communication_Protocol (Uci);
         New_Line;
         Flush;
      end if;


      if Console_Input (1) = Ascii.Lf then
         -- Sometimes Xboard sends a new line to the engine
         -- Just skip this command
         null;

      elsif Console_Input (1) = '?' then
         Forcemode := False;
         Flush;
         Engine    := Side_To_Move;
         Move      := Think;
         Forcemode := False;


      elsif To_String (Params.Command) = "usage"
        or else To_String (Params.Command) = "help" then
         Usage;
         Flush;
      elsif To_String (Params.Command) = "protover 2" then
      	 Flush;

         if Is_Initialized_Program = false then
            Initialize_Program;
            Is_Initialized_Program := true;
            Put_Line( To_WB, "Initialized NOW in protover 2");
            Flush;
         else
         	  Put_Line( To_WB, "Program initialized already, protover 2" );
         	  Flush;
         end if;

         Flush;

      elsif To_String (Params.Command) = "protover"  then
         -- debug
         Flush;

      elsif To_String (Params.Command) = "new" then
     	   Flush;
      elsif To_String (Params.Command) = "random" then
         Random_Mode := not Random_Mode;
         Put_Line( To_WB, "random" );
      elsif To_String (Params.Command) = "go" then
         Forcemode := False;
         Engine    := Side_To_Move;
         Move      := Think;
         Forcemode := False;

      elsif To_String (Params.Command) = "white" then
         Engine := Black;

      elsif To_String (Params.Command) = "black" then
         Engine := White;

      elsif To_String (Params.Command) = "force" then
         Forcemode := True;

      elsif To_String (Params.Command) = "move" then



         -- when user types a move like Ke3, e2e4, Nb1-c3, the parser
         -- engine can detect it and transform it by sending itself
         -- the "move" command and moving the input as parameter

         Move := Parse_Move (To_String (Params.Params (Params.Params'First)));
         -- debug
         Put_Line( To_WB, To_String (Params.Params (Params.Params'First)) );
         Play (Move);
         Display;
         Engine    := Side_To_Move;
         Move      := Think;
         Forcemode := False;

      elsif To_String (Params.Command) = "user move" then



         -- when user types a move like Ke3, e2e4, Nb1-c3, the parser
         -- engine can detect it and transform it by sending itself
         -- the "move" command and moving the input as parameter

         Move := Parse_Move (To_String (Params.Params (Params.Params'First)));
         -- debug
         Put_Line( To_WB, To_String (Params.Params (Params.Params'First)) );
         Play (Move);
         Display;
         Engine    := Side_To_Move;
         Move      := Think;
         Forcemode := False;

      elsif To_String (Params.Command) = "undo" then
         Ply := Ply + 1; -- adjust undo
         Undo;
         Forcemode := True;

         ---------------------------
         -- Time control commands --
         ---------------------------


      elsif To_String (Params.Command) = "time" then
         declare
            Available_Time     : constant Duration := Duration'Value (To_String (Params.Params (Params.Params'First))) / 100.0;
            Time_For_Next_Move : constant Duration := (if History_Ply < 80 then Available_Time / 40 else Available_Time / 10);
         begin
            Update_Residual_Time_Per_Game (Available_Time);
            Set_Fixed_Time_Per_Move (Time_For_Next_Move);
         end;

         -- TODO: update with new version
      elsif To_String (Params.Command) = "otim" then
         Opponent_Time := (Duration'Value (To_String (Params.Params (Params.Params'First))) / 100.0);

      elsif To_String (Params.Command) = "st" then
         Set_Fixed_Time_Per_Move (Duration'Value (To_String (Params.Params (Params.Params'First))));

         ---------------
         -- Notations --
         ---------------

      elsif To_String (Params.Command) = "notation" then
         declare
            Notation_Input : String (1 .. 32);
            Length         : Natural;
         begin
            Put_Line ("Choose the engine output notation:");
            Put_Line ("* Winboard/Xboard");
            Put_Line ("* Algebraic/SAN");
            Put_Line ("* Long Algebraic");
            Put_Line ("* UCI");
            Put_Line ("Type the name of notation you want, in lowercase: ");
            Get_Line (Notation_Input, Length);
            if Notation_Input (1 .. Length) = "winboard" or else Notation_Input (1 .. Length) = "xboard"  then
               Set_Output_Notation (Winboard);
               Put_Line ("Switched to Winboard/Xboard output");

            elsif Notation_Input (1 .. Length) = "algebraic" or else Notation_Input (1 .. Length) = "san" then
               Set_Output_Notation (Algebraic);
               Put_Line ("Switched to Algebraic/SAN output");

            elsif Notation_Input (1 .. Length) = "long algebraic" then
               Set_Output_Notation (Long_Algebraic);
               Put_Line ("Switched to Long Algebraic output");

            else
               Put_Line ("Sorry I don't understand...");
            end if;
            New_Line;
         end;

      elsif To_String (Params.Command) = "book" then
         Move := Book_Move;

      elsif To_String (Params.Command) = "perft" then

         declare
            Check_For_Check_Status : constant Boolean := Check_For_Check;
            Check_For_Legal_Status : constant Boolean := Check_For_Legal;
         begin

            Check_For_Check := True;
            Check_For_Legal := True;

            if Params.Tokens = 2
              and then To_String (Params.Params (Params.Params'First + 1)) = "raw"
            then
               Check_For_Legal := False;
               -- Call perft on <raw> nodes
               Perft (Integer_Type'Value (To_String (Params.Params (Params.Params'First))));

            elsif Params.Tokens = 1 then
               Perft (Integer_Type'Value (To_String (Params.Params (Params.Params'First))));
            else
               Put_Line ("Usage: perft <depth> [raw|legal]");
            end if;

            Check_For_Legal := Check_For_Legal_Status;
            Check_For_Check := Check_For_Check_Status;
         end;

      elsif To_String (Params.Command) = "divide" then
         if Params.Tokens = 1 then
            Divide (Integer_Type'Value (To_String (Params.Params (Params.Params'First))));
         else
            Put_Line ("Usage: divide <depth>");
         end if;

      elsif To_String (Params.Command) = "fen" or else To_String (Params.Command) = "setboard" then
         Forcemode := True;
         Close_Book;
         Put_Line ("Tokens: " & Integer'Image (Params.Tokens));
         Init_Transposition_Table;
         Fen_Init;
         Fen_Load_Pieces (To_String (Params.Params (Params.Params'First)));
         Fen_Load_Side_To_Move (To_String (Params.Params (Params.Params'First + 1)));
         Fen_Load_Castle_Flags (To_String (Params.Params (Params.Params'First + 2)));
         Fen_Load_En_Passant (To_String (Params.Params (Params.Params'First + 3)));
         Fen_Load_Fifty_Move_Counter (To_String (Params.Params (Params.Params'First + 4)));
         Fen_Load_Ply_Depth (To_String (Params.Params (Params.Params'First + 5)));

      elsif To_String (Params.Command) = "fensave" then
         declare
            Output : constant String := Fen_Save_To_String;
         begin
            Ada.Text_IO.Put_Line ("My output is: " & Output);
         end;

      elsif To_String (Params.Command) = "moves" then


         Check_For_Legal := True;
         Check_For_Check := True;
         Generate_Moves;
         --           Quick_Sort (1, Moves_Counter (Ply));
         Print_Moves_List;

      elsif To_String (Params.Command) = "sort" then

         New_Line;
         Put_Line ("Sorting with NORMAL strategy");

         Following_Principal_Variation := True;
         Order_Moves (Sorting_Strategy => Normal);

         declare
            Move : Move_Type;
         begin
            Print_Moves_List;
            Ada.Text_IO.Put_Line ("After sorting:");
            for I in 1 .. Moves_Counter (Ply) loop
               Prepare_Next_Move (I);
               Move := Moves_List (Ply, I);
               Print_Move (Move);
               Put (" => Score:" & Integer_Type'Image (Move.Score));
               New_Line;
            end loop;
         end;


      elsif To_String (Params.Command) = "see" then
         -- Test See data to see if a capture is
         -- a winning capture
         declare
            See_Score : Integer_Type;
         begin
            New_Line;
            Generate_Moves;
            for I in 1 .. Moves_Counter (Ply) loop
               Move := Moves_List (Ply, I);
               if Move.Captured /= Empty then
                  See_Score := Static_Exchange_Evaluation (Move);
                  Print_Move (Move);
                  Put (" see score:" & Integer_Type'Image (See_Score));
                  if See_Score > 0 then
                     Put (" (winning capture)");
                  elsif See_Score < 0 then
                     Put (" (losing capture)");
                  else
                     Put (" (equal capture)");
                  end if;
                  New_Line;
               end if;
            end loop;
         end;

      elsif To_String (Params.Command) = "dpt" then
         Display_Piece_Table;

      elsif To_String (Params.Command) = "evasion" then
         -- fen: k7/5r2/6N1/2B5/6N1/7B/8/4K1n1 w - - 0 1
         Generate_Check_Evasion;
         Print_Moves_List;

      elsif To_String (Params.Command) = "pin" then
         New_Line;
         Generate_Moves;
         for I in 1 .. Moves_Counter (Ply) loop
            Move := Moves_List (Ply, I);
            declare
               Pins : Pin_Type;
            begin
               Pins := Move_Pin_Opponent_Piece (Move);
               Print_Move (Move);
               Put (" ");
               Put_Line (Pin_Type'Image (Pins));
            end;
         end loop;

         New_Line (2);

         declare
            Direction : Integer_Type := 0;
         begin
            if Side_To_Move = White then
               for Square of White_Pieces loop
                  exit when Square = 0;
                  Direction := Is_Absolute_Pinned (Square);
                  Put_Line (Symbols (Chessboard (Square)) & Pc_Sqr (Square) & " pin dir:" & Integer_Type'Image (Direction));
               end loop;
            else
               for Square of White_Pieces loop
                  exit when Square = 0;
                  Direction := Is_Absolute_Pinned (Square);
                  Put_Line (Symbols (Chessboard (Square)) & Pc_Sqr (Square) & " pin dir:" & Integer_Type'Image (Direction));
               end loop;
            end if;
         end;

         ----------------
         -- Benchmarks --
         ----------------

      elsif To_String (Params.Command) = "benchmark" then
         Close_Book;
         Display;
         Put_Line ("Benchmarking current displayed position for" & Integer_Type'Image (Benchmark_Nps'Last - Benchmark_Nps'First + 1));
         Flush;
         Benchmark_Best_Nps := 0;
         for Test in Benchmark_Nps'Range loop
            Put_Line ("Test number" & Integer_Type'Image (Test) & " of" & Integer_Type'Image (Benchmark_Nps'Last - Benchmark_Nps'First + 1));
            delay 2.0;
            Set_Fixed_Time_Per_Move (60.0);
            Move := Think;
            Put ("Nodes:" & Node_Type'Image (Nodes) & "; NPS:" & Node_Type'Image (Nodes / 60));
            New_Line;
            Flush;
            Benchmark_Nps (Test) := Nodes / 60;
            Clear_Transposition_Table;
         end loop;
         -- find best value
         for I in Benchmark_Nps'Range loop
            if Benchmark_Nps (I) > Benchmark_Best_Nps then
               Benchmark_Best_Nps := Benchmark_Nps (I);
            end if;
         end loop;
         Put_Line ("Best NPS:" & Node_Type'Image (Benchmark_Best_Nps));
         New_Line;
         --Open_Book;
         Clear_Transposition_Table;

      elsif To_String (Params.Command) = "bench" then
         declare
            Seconds : Duration;
         begin
            if Params.Tokens = 1 then
               Seconds := Duration'Value (To_String (Params.Params (Params.Params'First)));
            else
               Seconds := 30.0;
            end if;
            Close_Book;
            Display;
            Put_Line ("Benchmarking current displayed position for" &  Integer'Image (Integer (Seconds)) & " seconds");
            Flush;
            delay 2.0;
            Set_Fixed_Time_Per_Move (Seconds);
            Move := Think;
            Put ("Nodes:" & Node_Type'Image (Nodes) & "; NPS:" & Node_Type'Image (Nodes / Node_Type (Integer (Seconds))));
            New_Line;
            Flush;
         end;


      elsif To_String (Params.Command) = "eval" then
         Score := Evaluate.Score;
         Put_Line ("Score: " & Integer_Type'Image (Score));
         New_Line;

      elsif To_String (Params.Command) = "reps" then
         declare
            Repetitions : Integer_Type := Count_Repetitions;
         begin
            Ada.Text_IO.Put_Line ("Repetitions: " & Integer_Type'Image (Repetitions));
         end;

      end if;

      Flush;

      exit when Console_Input (1 .. Last) = "quit";

   end loop Console_Loop;



   --     abort Clock;
   Close_Book;
   Stop_Ponder;

   Close( To_WB );
   Close( From_WB );
--   Close( Debug_BZ );

   <<End_Of_Program>>

   return;

exception
   when E : others =>
      Stop_Ponder;
      --        abort Clock;
      Ada.Text_IO.Put_Line (Ada.Exceptions.Exception_Name (E));
      Ada.Text_IO.Put_Line (Ada.Exceptions.Exception_Message (E));
      Ada.Text_IO.Put_Line (Ada.Exceptions.Exception_Information (E));

      return;

end pantherchess;
