------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                     S P A R K I F Y . C U R S O R S                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package body Sparkify.Cursors is

   -------------------
   -- Normalization --
   -------------------

   procedure Normalize_Line_Cursor (C : in out Cursor);
   --  pragma Postcondition (Cursor_Has_Line (C));
   --  Make C a line or column cursor

   procedure Normalize_Column_Cursor (C : in out Cursor);
   --  pragma Postcondition (Is_Column_Cursor (C));
   --  Make C a column cursor

   procedure Normalize_At_Column_Cursor (C : in out Cursor);
   --  Make C an At_Column cursor

   ---------------------------
   -- Normalize_Line_Cursor --
   ---------------------------

   procedure Normalize_Line_Cursor (C : in out Cursor) is
   begin
      case C.Kind is
         when Before_File =>
            C := Line_Cursor (Kind => Before_Line, Line => 1);
         when After_File =>
            C := Line_Cursor (Kind => After_Line, Line => The_Last_Line);
         when others =>
            null;
      end case;
   end Normalize_Line_Cursor;

   -----------------------------
   -- Normalize_Column_Cursor --
   -----------------------------

   procedure Normalize_Column_Cursor (C : in out Cursor) is
   begin
      Normalize_Line_Cursor (C);
      case C.Kind is
         when Before_Line =>
            C := Column_Cursor (Kind => Before_Column, Line => C.Line,
                                Column => 1);
         when After_Line =>
            C := Column_Cursor (Kind => After_Column, Line => C.Line,
                                Column => C.Line_Len);
         when others =>
            null;
      end case;
   end Normalize_Column_Cursor;

   --------------------------------
   -- Normalize_At_Column_Cursor --
   --------------------------------

   procedure Normalize_At_Column_Cursor (C : in out Cursor) is
      pragma Postcondition (C.Col_Kind = At_Column);
   begin
      Normalize_Column_Cursor (C);
      case C.Col_Kind is
         when Before_Column =>
            C.Column := C.Column - 1;
         when After_Column =>
            C.Column := C.Column + 1;
         when others =>
            null;
      end case;
      C.Col_Kind := At_Column;
   end Normalize_At_Column_Cursor;

   -------------
   -- Queries --
   -------------

   -----------------
   -- Cursor_Line --
   -----------------

   function Cursor_Line (C : Cursor) return Line_Number_Positive is
   begin
      case C.Kind is
         when Before_File =>
            return 1;
         when After_File =>
            return The_Last_Line;
         when others =>
            return C.Line;
      end case;
   end Cursor_Line;

   -------------------
   -- Cursor_Column --
   -------------------

   function Cursor_Column (C : Cursor) return Character_Position_Positive is
   begin
      case C.Kind is
         when Before_File | Before_Line =>
            return 1;
         when After_File =>
            return The_Last_Column + 1;
         when After_Line =>
            return C.Line_Len + 1;
         when Cursor_Column_Kind =>
            case C.Col_Kind is
               when Before_Column =>
                  return Character_Position'Max (C.Column - 1, 1);
               when At_Column =>
                  return C.Column;
               when After_Column =>
                  return C.Column + 1;
            end case;
      end case;
   end Cursor_Column;

   --------------------
   -- Is_File_Cursor --
   --------------------

   function Is_File_Cursor (C : Cursor) return Boolean is
   begin
      return C.Kind in Cursor_File_Kind;
   end Is_File_Cursor;

   --------------------
   -- Is_Line_Cursor --
   --------------------

   function Is_Line_Cursor (C : Cursor) return Boolean is
   begin
      return C.Kind in Cursor_Line_Kind;
   end Is_Line_Cursor;

   ----------------------
   -- Is_Column_Cursor --
   ----------------------

   function Is_Column_Cursor (C : Cursor) return Boolean is
   begin
      return C.Kind = Cursor_Column_Kind;
   end Is_Column_Cursor;

   ---------------------
   -- Cursor_Has_Line --
   ---------------------

   function Cursor_Has_Line (C : Cursor) return Boolean is
   begin
      return not Is_File_Cursor (C);
   end Cursor_Has_Line;

   ---------------------
   -- Cursor_On_Char --
   ---------------------

   function Cursor_On_Char (C : Cursor) return Boolean is
   begin
      return C.Kind = Cursor_Column_Kind and then
        (C.Col_Kind = At_Column or else
           (C.Col_Kind = Before_Column and then C.Column > 1) or else
           (C.Col_Kind = After_Column and then C.Column < C.Line_Len));
   end Cursor_On_Char;

   -------------------
   -- Cursor_At_EOF --
   -------------------

   function Cursor_At_EOF (C : Cursor) return Boolean is
   begin
      return Cursor_Line (C) >= The_Last_Line and then
        (C.Kind = After_File or else
         C.Kind = After_Line or else
           (C.Kind = Before_Line and then C.Line_Len = 0) or else
           (C.Kind = Cursor_Column_Kind and then C.Col_Kind = After_Column
            and then C.Column >= The_Last_Column));
   end Cursor_At_EOF;

   -----------------------
   -- Cursor_Line_Range --
   -----------------------

   function Cursor_Line_Range (From, To : Cursor) return Asis.Program_Text is

      function Cursor_Column_Ceiling (C : Cursor) return Character_Position;
      pragma Precondition (Is_Column_Cursor (C));
      --  Returns a suitable column for the lower bound of a line range

      function Cursor_Column_Floor (C : Cursor) return Character_Position;
      pragma Precondition (Is_Column_Cursor (C));
      --  Returns a suitable column for the upper bound of a line range

      ---------------------------
      -- Cursor_Column_Ceiling --
      ---------------------------

      function Cursor_Column_Ceiling (C : Cursor) return Character_Position is
      begin
         case C.Col_Kind is
         when Before_Column =>
            return Character_Position'Max (C.Column - 1, 1);
         when After_Column =>
            return C.Column + 1;
         when others =>
            return C.Column;
         end case;
      end Cursor_Column_Ceiling;

      -------------------------
      -- Cursor_Column_Floor --
      -------------------------

      function Cursor_Column_Floor (C : Cursor) return Character_Position is
      begin
         case C.Col_Kind is
         when Before_Column =>
            return C.Column - 1;
         when After_Column =>
            return Character_Position'Min (C.Column + 1, C.Line_Len);
         when others =>
            return C.Column;
         end case;
      end Cursor_Column_Floor;

      Local_From : Cursor := From;
      Local_To   : Cursor := To;
   begin
      Normalize_Line_Cursor (Local_From);

      if Local_From.Line_Len = 0 then
         return "";
      else
         Normalize_Column_Cursor (Local_From);
         Normalize_Column_Cursor (Local_To);

         return Local_From.Line_Buf
           (Cursor_Column_Ceiling (Local_From) ..
              Cursor_Column_Floor (Local_To));
      end if;
   end Cursor_Line_Range;

   -----------------
   -- Comparisons --
   -----------------

   function Col (C : Cursor) return Character_Position;
   --  Return an appropriate column for cursor comparison

   function Col (C : Cursor) return Character_Position is
   begin
      case C.Col_Kind is
         when Before_Column => return C.Column - 1;
         when At_Column     => return C.Column;
         when After_Column  => return C.Column + 1;
      end case;
   end Col;

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Cursor) return Boolean is
   begin
      if Left.Kind /= Right.Kind then
         return False;
      elsif Is_File_Cursor (Left) then
         return True;
      elsif Left.Line /= Right.Line then
         return False;
      elsif Is_Line_Cursor (Left) then
         return True;
      else
         return Col (Left) = Col (Right);
      end if;
   end "=";

   ---------
   -- "<" --
   ---------

   function "<" (Left, Right : Cursor) return Boolean is
   begin
      --  Case 1: Left and Right are equal

      if Left = Right then
         return False;
      end if;

      --  Case 2: one of Left or Right is of Cursor_File_Kind

      case Left.Kind is
         when Before_File =>
            return True;
         when After_File =>
            return False;
         when others =>
            null;
      end case;

      case Right.Kind is
         when Before_File =>
            return False;
         when After_File =>
            return True;
         when others =>
            null;
      end case;

      --  Case 3: Left and Right are not on the same line

      if Left.Line < Right.Line then
         return True;
      elsif Left.Line > Right.Line then
         return False;
      end if;

      --  Case 4: one of Left or Right is of Cursor_Line_Kind

      case Left.Kind is
         when Before_Line =>
            return True;
         when After_Line =>
            return False;
         when others =>
            null;
      end case;

      case Right.Kind is
         when Before_Line =>
            return False;
         when After_Line =>
            return True;
         when others =>
            null;
      end case;

      --  Case 5: Left and Right are of Cursor_Column_Kind on the same line
      return Col (Left) < Col (Right);
   end "<";

   ---------
   -- ">" --
   ---------

   function ">" (Left, Right : Cursor) return Boolean is
   begin
      return Right < Left;
   end ">";

   ------------------
   -- Constructors --
   ------------------

   -----------------
   -- File_Cursor --
   -----------------

   function File_Cursor (Kind : Cursor_File_Kind) return Cursor is
   begin
      case Kind is
         when Before_File =>
            return (Kind     => Before_File,
                    Line_Len => 0);
         when After_File =>
            return (Kind     => After_File,
                    Line_Len => 0);
      end case;
   end File_Cursor;

   -----------------
   -- Line_Cursor --
   -----------------

   function Line_Cursor
     (Kind : Cursor_Line_Kind;
      Line : Line_Number_Positive) return Cursor
   is
      The_line : constant Asis.Text.Line := Lines_Table.Table (Line);
   begin
      case Kind is
         when Before_Line =>
            return (Kind     => Before_Line,
                    Line     => Line,
                    Line_Len => Length (The_line),
                    Line_Buf => Line_Image (The_line));
         when After_Line =>
            return (Kind     => After_Line,
                    Line     => Line,
                    Line_Len => Length (The_line),
                    Line_Buf => Line_Image (The_line));
      end case;
   end Line_Cursor;

   -------------------
   -- Column_Cursor --
   -------------------

   function Column_Cursor
     (Kind   : Column_Kind;
      Line   : Line_Number_Positive;
      Column : Character_Position_Positive) return Cursor
   is
      The_line : constant Asis.Text.Line := Lines_Table.Table (Line);
   begin
      case Kind is
         when Before_Column =>
            return (Kind     => Cursor_Column_Kind,
                    Col_Kind => Before_Column,
                    Line     => Line,
                    Column   => Column,
                    Line_Len => Length (The_line),
                    Line_Buf => Line_Image (The_line));
         when At_Column =>
            return (Kind     => Cursor_Column_Kind,
                    Col_Kind => At_Column,
                    Line     => Line,
                    Column   => Column,
                    Line_Len => Length (The_line),
                    Line_Buf => Line_Image (The_line));
         when After_Column =>
            return (Kind     => Cursor_Column_Kind,
                    Col_Kind => After_Column,
                    Line     => Line,
                    Column   => Column,
                    Line_Len => Length (The_line),
                    Line_Buf => Line_Image (The_line));
      end case;
   end Column_Cursor;

   -------------------
   -- Cursor_Before --
   -------------------

   function Cursor_Before (Element : Asis.Element) return Cursor is
      Line   : constant Line_Number := First_Line_Number (Element);
      Column : constant Character_Position :=
        Element_Span (Element).First_Column;
   begin
      return Column_Cursor (Kind => Before_Column, Line => Line,
                            Column => Column);
   end Cursor_Before;

   ---------------
   -- Cursor_At --
   ---------------

   function Cursor_At (Element : Asis.Element) return Cursor is
      Line   : constant Line_Number := First_Line_Number (Element);
      Column : constant Character_Position :=
        Element_Span (Element).First_Column;
   begin
      return Column_Cursor (Kind => At_Column, Line => Line, Column => Column);
   end Cursor_At;

   ----------------------
   -- Cursor_At_End_Of --
   ----------------------

   function Cursor_At_End_Of (Element : Asis.Element) return Cursor is
      Line   : constant Line_Number := Last_Line_Number (Element);
      Column : constant Character_Position :=
        Element_Span (Element).Last_Column;
   begin
      return Column_Cursor (Kind => At_Column, Line => Line, Column => Column);
   end Cursor_At_End_Of;

   ------------------
   -- Cursor_After --
   ------------------

   function Cursor_After (Element : Asis.Element) return Cursor is
      Line   : constant Line_Number := Last_Line_Number (Element);
      Column : constant Character_Position :=
        Element_Span (Element).Last_Column;
   begin
      return Column_Cursor (Kind => After_Column, Line => Line,
                            Column => Column);
   end Cursor_After;

   ----------------
   -- Max_Cursor --
   ----------------

   function Max_Cursor (C1, C2 : Cursor) return Cursor is
   begin
      if C1 < C2 then
         return C2;
      else
         return C1;
      end if;
   end Max_Cursor;

   ----------------------
   -- Cursor_Next_Line --
   ----------------------

   procedure Cursor_Next_Line (C : in out Cursor) is
   begin
      Normalize_Line_Cursor (C);
      if The_Last_Line >= C.Line + 1 then
         C := Line_Cursor (Kind => Before_Line, Line => C.Line + 1);
      else
         C := File_Cursor (After_File);
      end if;
   end Cursor_Next_Line;

   ------------------------
   -- Cursor_Next_Column --
   ------------------------

   procedure Cursor_Next_Column (C : in out Cursor) is
   begin
      if C.Kind = Cursor_Column_Kind then
         case C.Col_Kind is
         when Before_Column =>
            C.Col_Kind := At_Column;
         when At_Column =>
            C.Col_Kind := After_Column;
         when After_Column =>
            if C.Column + 2 <= C.Line_Len then
               C.Col_Kind := At_Column;
               C.Column   := C.Column + 2;
            else
               C.Col_Kind := After_Column;
               C.Column   := C.Line_Len;
            end if;
         end case;
      end if;
   end Cursor_Next_Column;

   ----------------------
   -- Cursor_Move_Left --
   ----------------------

   procedure Cursor_Move_Left (C : in out Cursor; N : Natural) is
   begin
      case C.Col_Kind is
         when Before_Column =>
            pragma Assert (C.Column > N);
            C.Column := C.Column - N;
         when At_Column =>
            pragma Assert (C.Column >= N);
            if C.Column = N then
               C.Col_Kind := Before_Column;
               C.Column   := 1;
            else
               C.Column := C.Column - N;
            end if;
         when After_Column =>
            pragma Assert (C.Column >= N - 1);
            if C.Column = N - 1 then
               C.Col_Kind := Before_Column;
               C.Column   := 1;
            elsif C.Column = N then
               C.Col_Kind := At_Column;
               C.Column   := 1;
            else
               C.Column := C.Column - N;
            end if;
      end case;
   end Cursor_Move_Left;

   -----------------
   -- Skip_Blanks --
   -----------------

   procedure Skip_Blanks (C : in out Cursor) is

      function Cursor_Before_Line (C : Cursor) return Boolean;
      --  Returns True if the cursor points before the line. Should only be
      --  called on a line or column cursor.

      function Cursor_After_Line (C : Cursor) return Boolean;
      --  Returns True if the cursor points after the line. Should only be
      --  called on a line or column cursor.

      ------------------------
      -- Cursor_Before_Line --
      ------------------------

      function Cursor_Before_Line (C : Cursor) return Boolean is
      begin
         return C.Kind = Before_Line or else
           (C.Kind = Cursor_Column_Kind and then
            C.Col_Kind = Before_Column and then
            C.Column = 1);
      end Cursor_Before_Line;

      -----------------------
      -- Cursor_After_Line --
      -----------------------

      function Cursor_After_Line (C : Cursor) return Boolean is
      begin
         return C.Kind = After_Line or else
           (C.Kind = Cursor_Column_Kind and then
            C.Col_Kind = After_Column and then
            C.Column = C.Line_Len);
      end Cursor_After_Line;

   begin
      while not Cursor_At_EOF (C) loop --  Loop over lines

         Normalize_Line_Cursor (C);

         if C.Line_Len = 0 then
            Cursor_Next_Line (C);
         else

            loop --  Loop over columns

               Normalize_Column_Cursor (C);

               if Cursor_After_Line (C) then
                  Cursor_Next_Line (C);
                  exit;
               elsif Cursor_Before_Line (C) then
                  Cursor_Next_Column (C);
               end if;

               Normalize_At_Column_Cursor (C);

               if Is_White_Space (C.Line_Buf (C.Column)) then
                  Cursor_Next_Column (C);
               else
                  return;
               end if;

            end loop;

         end if;

      end loop;
   end Skip_Blanks;

   ---------------
   -- Skip_Word --
   ---------------

   procedure Skip_Word (C : in out Cursor; S : Asis.Program_Text) is
      Col : constant Natural := C.Column + S'Length;
   begin
      if Col <= C.Line_Len then
         C.Column := C.Column + S'Length;
      else

         pragma Assert (Col = C.Line_Len + 1);
         C.Column := C.Line_Len;

         case C.Col_Kind is
            when Before_Column =>
               C.Col_Kind := At_Column;
            when At_Column =>
               C.Col_Kind := After_Column;
            when After_Column =>
               pragma Assert (False);
               null;
         end case;
      end if;
   end Skip_Word;

end Sparkify.Cursors;
