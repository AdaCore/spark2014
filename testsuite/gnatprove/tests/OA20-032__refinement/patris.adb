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

pragma Style_Checks ("M132");
with Interfaces.C; use Interfaces.C;
with Pebble;

package body Patris with
   SPARK_Mode    => On,
   Refined_State => (Game_State => (Cur_State, Cur_Piece, Cur_Board,
                                    Next_Piece, Speed_Up, Action_Request_Nbr),
                     Score_State => (Level_Nbr, Score_Nbr, Line_Counter),
                     Best_Score_State => (Best_Score_Nbr))
is

   --  Score State
   Score_Nbr    : Score_T;
   Level_Nbr    : Score_T;
   Line_Counter : Score_T;

   --  Best Score State
   Best_Score_Nbr : Score_T := 0;

   --  Game State
   Cur_Board          : Board := (others => (others => Empty));
   Cur_Piece          : Piece;
   Next_Piece         : Piece;
   Cur_State          : State := Board_After_Clean;
   Action_Request_Nbr : Natural;
   Speed_Up           : Boolean;

   subtype Action_Request_Range is Natural range 1 .. 2;


   function Get_New_Piece return Piece;

   -------------------
   -- Get_New_Piece --
   -------------------

   function Get_New_Piece return Piece is
   begin
      return (S => Cell'Val (1 + Integer (Pebble.Rand) mod 7),
              D => Direction'Val (Integer (Pebble.Rand) mod 4),
              X => X_Size / 2,
              Y => Y_Coord'First);
   end Get_New_Piece;

   ---------------
   -- Get_Board --
   ---------------

   function Get_Board return Board is (Cur_Board);

   ---------------
   -- Get_Piece --
   ---------------

   function Get_Piece return Piece is (Cur_Piece);

   ---------------
   -- Get_Piece --
   ---------------

   function Get_Next_Piece return Piece is (Next_Piece);

   ---------------
   -- Get_State --
   ---------------

   function Get_State return State is (Cur_State);

   ----------------------------
   -- Include_Piece_In_Board --
   ----------------------------

   procedure Include_Piece_In_Board is
   begin
      case Cur_Piece.S is
         when O =>
            Cur_Board (Cur_Piece.Y) (Cur_Piece.X)         := Cur_Piece.S;
            Cur_Board (Cur_Piece.Y + 1) (Cur_Piece.X)     := Cur_Piece.S;
            Cur_Board (Cur_Piece.Y) (Cur_Piece.X + 1)     := Cur_Piece.S;
            Cur_Board (Cur_Piece.Y + 1) (Cur_Piece.X + 1) := Cur_Piece.S;

         when I =>
            --  intermediate assertion needed for proof
            pragma Assert
              (for all YY in I_Delta =>
                 (for all XX in I_Delta =>
                    (if Possible_I_Shapes (Cur_Piece.D) (YY, XX) then
                       Is_Empty (Cur_Board, Cur_Piece.Y + YY, Cur_Piece.X + XX))));

            for Y in I_Delta loop
               for X in I_Delta loop
                  if Possible_I_Shapes (Cur_Piece.D) (Y, X) then
                     Cur_Board (Cur_Piece.Y + Y) (Cur_Piece.X + X) := Cur_Piece.S;
                  end if;
               end loop;
            end loop;

         when Three_Shape =>
            --  intermediate assertion needed for proof
            pragma Assert
              (for all YY in Three_Delta =>
                 (for all XX in Three_Delta =>
                    (if Possible_Three_Shapes (Cur_Piece.S, Cur_Piece.D) (YY, XX) then
                       Is_Empty (Cur_Board, Cur_Piece.Y + YY, Cur_Piece.X + XX))));

            for Y in Three_Delta loop
               for X in Three_Delta loop
                  if Possible_Three_Shapes (Cur_Piece.S, Cur_Piece.D) (Y, X) then
                     Cur_Board (Cur_Piece.Y + Y) (Cur_Piece.X + X) := Cur_Piece.S;
                  end if;
               end loop;
            end loop;
      end case;

      --  update current state

      Cur_State := Board_Before_Clean;
   end Include_Piece_In_Board;

   ---------------------------
   -- Delete_Complete_Lines --
   ---------------------------

   procedure Delete_Complete_Lines is
      Empty_Line : constant Line := (others => Empty);

      To_Line : Y_Coord := Y_Coord'Last;
      Complete_Lines : Score_T := 0;
   begin
      --  delete all complete lines, identifying the first complete line from
      --  the bottom (higher value of Y)

      for Del_Line in Y_Coord loop
         if Is_Complete_Line (Cur_Board (Del_Line)) then
            Cur_Board (Del_Line) := Empty_Line;
            To_Line := Del_Line;
            Complete_Lines := Complete_Lines + 1;
            pragma Assert (Cur_Board (Del_Line)(X_Coord'First) = Empty);
         end if;
         pragma Loop_Invariant
           (for all Y in Y_Coord'First .. Del_Line => not Is_Complete_Line (Cur_Board (Y)));
      end loop;

      pragma Assert (No_Complete_Lines (Cur_Board));

      --  iteratively move non-empty lines to the bottom of the board

      if Complete_Lines /= 0 then
         for From_Line in reverse Y_Coord'First .. To_Line - 1 loop
            pragma Loop_Invariant (No_Complete_Lines (Cur_Board));
            pragma Loop_Invariant (From_Line < To_Line);
            if not Is_Empty_Line (Cur_Board (From_Line)) then
               Cur_Board (To_Line) := Cur_Board (From_Line);
               Cur_Board (From_Line) := Empty_Line;
               To_Line := To_Line - 1;
               pragma Assert (Cur_Board (From_Line)(X_Coord'First) = Empty);
            end if;
         end loop;
      end if;

      case Complete_Lines is
         when 1 => Score_Nbr := Score_Nbr + 4 * (Level_Nbr + 1);
         when 2 => Score_Nbr := Score_Nbr + 10 * (Level_Nbr + 1);
         when 3 => Score_Nbr := Score_Nbr + 30 * (Level_Nbr + 1);
         when 4 => Score_Nbr := Score_Nbr + 120 * (Level_Nbr + 1);
         when others => null;
      end case;

      Line_Counter := Line_Counter + Complete_Lines;

      if Line_Counter >= 10 and then Level_Nbr < 10 then
         Level_Nbr := Level_Nbr + 1;
         Line_Counter := Line_Counter - 10;
      end if;

      --  update current state

      Cur_State := Board_After_Clean;
   end Delete_Complete_Lines;

   ---------------
   -- Do_Action --
   ---------------

   procedure Do_Action (A : Action; Success : out Boolean) is
      Candidate : Piece;
   begin
      if Move_Is_Possible (Cur_Piece, A) then
         Candidate := Move (Cur_Piece, A);

         if No_Overlap (Cur_Board, Candidate) then
            Cur_Piece := Candidate;
            Success := True;
            return;
         end if;
      end if;

      Success := False;
   end Do_Action;

   ----------------
   -- Game_Reset --
   ----------------

   procedure Game_Reset
     with Refined_Global => (Output => (Cur_Board, Cur_State, Cur_Piece,
                                        Next_Piece, Speed_Up,
                                        Action_Request_Nbr, Level_Nbr,
                                        Score_Nbr, Line_Counter))
   is
   begin
      Level_Nbr := 0;
      Score_Nbr := 0;
      Line_Counter := 0;
      Cur_Board := (others => (others => Empty));
      Cur_Piece := (I, North, 0, 0);
      Next_Piece := (I, North, 0, 0);
--        Cur_Piece := Get_New_Piece;
--        Next_Piece := Get_New_Piece;
      Cur_State := Board_After_Clean;
      Action_Request_Nbr := 0;
      Speed_Up := False;
   end Game_Reset;

   --------------------
   -- Set_Game_State --
   --------------------

   procedure Set_Game_State (New_Board                     : Board;
                             New_Cur_State                 : State;
                             New_Cur_Piece, New_Next_Piece : Piece)
     with Refined_Global => (Output => (Cur_Board, Cur_State, Cur_Piece,
                                        Next_Piece, Speed_Up,
                                        Action_Request_Nbr))
   is
   begin
      Cur_Board := New_Board;
      Cur_Piece := New_Cur_Piece;
      Next_Piece := New_Next_Piece;
      Cur_State := New_Cur_State;
      Speed_Up := False;
      Action_Request_Nbr := 0;
   end Set_Game_State;

   ---------------
   -- Game_Step --
   ---------------

   procedure Game_Step
     (Redraw_Board, Redraw_Score, Redraw_Current_Piece : out Boolean)
   is
      Success : Boolean;
   begin

      Redraw_Board         := False;
      Redraw_Current_Piece := False;
      Redraw_Score         := False;

      if Cur_State = Piece_Falling then
         Action_Request_Nbr := 0;

         Do_Action (Move_Down, Success);
         Redraw_Current_Piece := True;
         if not Success then
            Cur_State := Piece_Blocked;
            Include_Piece_In_Board;
            Delete_Complete_Lines;
            --  Nbr_Pieces := Nbr_Pieces + 1;
            Redraw_Board := True;
         end if;
      elsif Cur_State = Board_After_Clean then

         --  Go back to normal speed if needed
         Speed_Up := False;

         --  Next_Piece is empty at the beginning of the game
         if Next_Piece.S = Empty then
            Next_Piece := Get_New_Piece;
         end if;

         --  Is there space left for the next piece?

         if not No_Overlap (Cur_Board, Next_Piece) then
            --  Game over

            Cur_State := Game_Over;
            if Score_Nbr > Best_Score_Nbr then
               Best_Score_Nbr := Score_Nbr;
            end if;
         else
            --  Add a new piece
            Cur_Piece := Next_Piece;

            --  Compute next one
            Next_Piece := Get_New_Piece;

            Cur_State := Piece_Falling;
         end if;
         Redraw_Score := True;
      end if;
   end Game_Step;

   --------------------
   -- Get_Best_Score --
   --------------------

   function Get_Best_Score return Score_T is
   begin
      return Best_Score_Nbr;
   end Get_Best_Score;

   --------------------
   -- Set_Best_Score --
   --------------------

   procedure Set_Best_Score (Score : Score_T) is
   begin
      Best_Score_Nbr := Score;
   end Set_Best_Score;

   ---------------
   -- Get_Score --
   ---------------

   function Get_Score return Score_T is
   begin
      return Score_Nbr;
   end Get_Score;

   ---------------
   -- Set_Score --
   ---------------

   procedure Set_Score (Score : Score_T) is
   begin
      Score_Nbr := Score;
   end Set_Score;

   --------------
   -- Get_Level --
   --------------

   function Get_Level return Score_T is
   begin
      return Level_Nbr;
   end Get_Level;

   ---------------
   -- Set_Level --
   ---------------

   procedure Set_Level (Lvl : Score_T) is
   begin
      Level_Nbr := (if Lvl > 10 then 10 else Lvl);
   end Set_Level;

   ----------------------
   -- Get_Line_Counter --
   ----------------------

   function Get_Line_Counter return Score_T is
   begin
      return Line_Counter;
   end Get_Line_Counter;

   ----------------------
   -- Set_Line_Counter --
   ----------------------

   procedure Set_Line_Counter (Lines : Score_T) is
   begin
      Line_Counter := Lines;
   end Set_Line_Counter;

   --------------------
   -- Action_Request --
   --------------------

   procedure Action_Request (A : Action) is
      Success : Boolean;
   begin
      if Cur_State = Piece_Falling then
         --  A Move_Down request means accelerate
         if A = Move_Down then
            Speed_Up := True;
            return;
         end if;

         --  Only two actions allowed
         if Action_Request_Nbr  < 2 then
            Do_Action (A, Success);
            if Success then
               Action_Request_Nbr := Action_Request_Nbr + 1;
            end if;
         end if;
      end if;
   end Action_Request;

   -----------------------
   -- Get_Step_Interval --
   -----------------------

   function Get_Step_Interval return Natural is
      Interval : Natural := ((11 - Natural (Level_Nbr) mod 11) * 50);
   begin
      return (if Speed_Up then Interval / 3 else Interval);
   end Get_Step_Interval;

begin
   Game_Reset;
end Patris;
