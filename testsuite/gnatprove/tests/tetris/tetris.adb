pragma Warnings (Off, "*unused initial value*");  -- ignore false positive warnings

package body Tetris with
  SPARK_Mode
is
   ----------------------------
   -- Include_Piece_In_Board --
   ----------------------------

   procedure Include_Piece_In_Board is
   begin
      Cur_State := No_Piece_Falling;
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
         if Is_Complete_Line (Cur_Board(Del_Line)) then
            Cur_Board (Del_Line) := Empty_Line;
            Has_Complete_Lines := True;
            To_Line := Del_Line;
            pragma Assert (Cur_Board(Del_Line)(X_Coord'First) = Empty);
         end if;
         pragma Loop_Invariant
           (for all Y in Y_Coord'First .. Del_Line => not Is_Complete_Line (Cur_Board(Y)));
      end loop;

      --  iteratively move non-empty lines to the bottom of the board

      if Has_Complete_Lines then
         for From_Line in reverse Y_Coord'First .. To_Line - 1 loop
            pragma Loop_Invariant (No_Complete_Lines (Cur_Board));
            pragma Loop_Invariant (From_Line < To_Line);
            if not Is_Empty_Line (Cur_Board(From_Line)) then
               Cur_Board (To_Line) := Cur_Board (From_Line);
               To_Line := To_Line - 1;
            end if;
         end loop;
      end if;
   end Delete_Complete_Lines;

   ---------------
   -- Do_Action --
   ---------------

   procedure Do_Action (A : Action; Success : out Boolean) is
      Candidate : constant Piece := Move (Cur_Piece, A);
   begin
      if No_Overlap (Cur_Board, Candidate) then
         Cur_Piece := Candidate;
         Success := True;
      else
         Success := False;
      end if;
   end Do_Action;

end Tetris;
