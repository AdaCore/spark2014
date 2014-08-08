------------------------------------------------------------------------------
--                                                                          --
--                             GNAT EXAMPLE                                 --
--                                                                          --
--                      Copyright (C) 2014, AdaCore                         --
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

--  Ignore false positive warnings
pragma Warnings (Off, "*unused initial value*");
pragma Style_Checks ("M132");

package body Tetris with
  SPARK_Mode
is
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
               pragma Loop_Invariant
                 (for all YY in I_Delta range Y .. I_Delta'Last =>
                    (for all XX in I_Delta =>
                       (if Possible_I_Shapes (Cur_Piece.D) (YY, XX) then
                          Is_Empty (Cur_Board, Cur_Piece.Y + YY, Cur_Piece.X + XX))));
               for X in I_Delta loop
                  pragma Loop_Invariant
                    (for all YY in I_Delta range Y + 1 .. I_Delta'Last =>
                       (for all XX in I_Delta =>
                          (if Possible_I_Shapes (Cur_Piece.D) (YY, XX) then
                             Is_Empty (Cur_Board, Cur_Piece.Y + YY, Cur_Piece.X + XX))));
                  pragma Loop_Invariant
                    (for all XX in I_Delta range X .. I_Delta'Last =>
                       (if Possible_I_Shapes (Cur_Piece.D) (Y, XX) then
                          Is_Empty (Cur_Board, Cur_Piece.Y + Y, Cur_Piece.X + XX)));
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
               pragma Loop_Invariant
                 (for all YY in Three_Delta range Y .. Three_Delta'Last =>
                    (for all XX in Three_Delta =>
                       (if Possible_Three_Shapes (Cur_Piece.S, Cur_Piece.D) (YY, XX) then
                          Is_Empty (Cur_Board, Cur_Piece.Y + YY, Cur_Piece.X + XX))));
               for X in Three_Delta loop
                  pragma Loop_Invariant
                    (for all YY in Three_Delta range Y + 1 .. Three_Delta'Last =>
                       (for all XX in Three_Delta =>
                          (if Possible_Three_Shapes (Cur_Piece.S, Cur_Piece.D) (YY, XX) then
                             Is_Empty (Cur_Board, Cur_Piece.Y + YY, Cur_Piece.X + XX))));
                  pragma Loop_Invariant
                    (for all XX in Three_Delta range X .. Three_Delta'Last =>
                       (if Possible_Three_Shapes (Cur_Piece.S, Cur_Piece.D) (Y, XX) then
                          Is_Empty (Cur_Board, Cur_Piece.Y + Y, Cur_Piece.X + XX)));
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
      Has_Complete_Lines : Boolean := False;
   begin
      --  delete all complete lines, identifying the first complete line from
      --  the bottom (higher value of Y)

      for Del_Line in Y_Coord loop
         if Is_Complete_Line (Cur_Board (Del_Line)) then
            Cur_Board (Del_Line) := Empty_Line;
            Has_Complete_Lines := True;
            To_Line := Del_Line;
            pragma Assert (Cur_Board (Del_Line)(X_Coord'First) = Empty);
         end if;
         pragma Loop_Invariant
           (for all Y in Y_Coord'First .. Del_Line => not Is_Complete_Line (Cur_Board (Y)));
      end loop;

      --  iteratively move non-empty lines to the bottom of the board

      if Has_Complete_Lines then
         for From_Line in reverse Y_Coord'First .. To_Line - 1 loop
            pragma Loop_Invariant (No_Complete_Lines (Cur_Board));
            pragma Loop_Invariant (From_Line < To_Line);
            if not Is_Empty_Line (Cur_Board (From_Line)) then
               Cur_Board (To_Line) := Cur_Board (From_Line);
               Cur_Board (From_Line) := Empty_Line;
               To_Line := To_Line - 1;
            end if;
         end loop;
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

end Tetris;
