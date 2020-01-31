------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                           P R I N T _ T A B L E                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

package body Print_Table with SPARK_Mode is

   ------------------
   -- Create_Table --
   ------------------

   function Create_Table (Lines, Cols : Natural) return Table is
      pragma Assume (Length (Null_Unbounded_String) = 0,
                     "Null_Unbounded_String represents the null String.");

      T : constant Table_Content (1 .. Lines, 1 .. Cols) :=
        (others => (others => Cell'(Content => Null_Unbounded_String,
                                    Align   => Right_Align)));
   begin
      return (Lines, Cols, T, 1, 1);
   end Create_Table;

   --------------
   -- Put_Cell --
   --------------

   procedure Put_Cell (T     : in out Table;
                       S     : String;
                       Align : Alignment_Type := Right_Align) is
   begin
      pragma Assume (Length (To_Unbounded_String (S)) = S'Length,
                     String'("To_Unbounded_String (S) returns an"
                       & " Unbounded_String that represents S."));
      pragma Assume (To_String (To_Unbounded_String (S)) = S,
                     String'("If S is a String, then "
                       & "To_String(To_Unbounded_String(S)) = S."));

      T.Content (T.Cur_Line, T.Cur_Col) :=
        Cell'(Content => To_Unbounded_String (S),
              Align   => Align);
      T.Cur_Col := T.Cur_Col + 1;
   end Put_Cell;

   procedure Put_Cell (T     : in out Table;
                       S     : Natural;
                       Align : Alignment_Type := Right_Align) is
   begin
      if S = 0 then
         Put_Cell (T, " .", Align);
      else
         pragma Assume (Integer'Image (S)'Length <= 10,
                        "Natural fits in 10 digits in 64bits machines.");

         Put_Cell (T, Integer'Image (S), Align);
      end if;
   end Put_Cell;

   --------------
   -- New_Line --
   --------------

   procedure New_Line (T : in out Table) is
   begin
      pragma Assert (T.Cur_Col = T.Content'Last (2) + 1);
      T.Cur_Line := T.Cur_Line + 1;
      T.Cur_Col := 1;
   end New_Line;

   procedure Dump_Table (H : Ada.Text_IO.File_Type; T : Table) is
      type Width_Array is array (T.Content'Range (2)) of Natural;
      Max_Width   : Width_Array := (others => 10);
      Total_Width : Natural := 0;

      procedure Compute_Max_Width;
      --  compute the maximum width for each column, minimum width is 10

      function Fit_Cell (C : Cell; Width : Natural) return String with
        Pre => Width <= Max_Size + 3
        and then Length (C.Content) <= Max_Size
        and then Length (C.Content) <= Width;
      --  @param C The cell
      --  @param Width the desired width
      --  @return a string of length Width, where the content of cell C has
      --     been fit according to the cell alignment

      procedure Put_Dash_Line;
      --  put a line of dashs of witdh Total_Width, plus a newline

      -----------------------
      -- Compute_Max_Width --
      -----------------------

      procedure Compute_Max_Width is
      begin
         for Line in T.Content'Range (1) loop
            pragma Loop_Invariant
              (for all L in T.Content'Range (1) =>
                   (if L < Line then
                        (for all C in T.Content'Range (2) =>
                               Length (T.Content (L, C).Content) + 3 <=
                           Max_Width (C))));
            pragma Loop_Invariant
              (for all C in T.Content'Range (2) =>
                   Max_Width (C) <= Max_Size + 3);
            for Col in T.Content'Range (2) loop
               declare
                  Len : constant Natural :=
                    Length (T.Content (Line, Col).Content) + 3;
               begin
                  if Max_Width (Col) < Len then
                     Max_Width (Col) := Len;
                  end if;
               end;
               pragma Loop_Invariant
                 (for all L in T.Content'Range (1) =>
                      (if L < Line then
                           (for all C in T.Content'Range (2) =>
                                  Length (T.Content (L, C).Content) + 3 <=
                              Max_Width (C))));
               pragma Loop_Invariant
                 (for all C in T.Content'Range (2) =>
                      (if C <= Col then
                            Length (T.Content (Line, C).Content) + 3 <=
                         Max_Width (C)));
               pragma Loop_Invariant
                 (for all C in T.Content'Range (2) =>
                      Max_Width (C) <= Max_Size + 3);
            end loop;
         end loop;
         for Col in Max_Width'Range loop
            pragma Loop_Invariant
              (Total_Width <= (Col - Max_Width'First) * (Max_Size + 3));
            Total_Width := Total_Width + Max_Width (Col);
         end loop;
      end Compute_Max_Width;

      --------------
      -- Fit_Cell --
      --------------

      function Fit_Cell (C : Cell; Width : Natural) return String is
         S : String (1 .. Width) := (others => ' ');
         Len : constant Natural := Length (C.Content);
         First : Natural;
      begin
         case C.Align is
            when Left_Align  => First := 1;
            when Centered    => First := (Width - Len) / 2 + 1;
            when Right_Align => First := Width - Len + 1;
         end case;
         for I in 1 .. Len loop
            S (First + I - 1) := Element (C.Content, I);
         end loop;
         return S;
      end Fit_Cell;

      -------------------
      -- Put_Dash_Line --
      -------------------

      procedure Put_Dash_Line is
      begin
         for I in 1 .. Total_Width loop
            Ada.Text_IO.Put (H, '-');
         end loop;
         Ada.Text_IO.New_Line (H);
      end Put_Dash_Line;

   begin
      Compute_Max_Width;
      Put_Dash_Line;
      for Line in T.Content'Range (1) loop
         for Col in T.Content'Range (2) loop
            Ada.Text_IO.Put
              (H,
               Fit_Cell (T.Content (Line, Col), Max_Width (Col)));
         end loop;
         Ada.Text_IO.New_Line (H);
         if Line = T.Content'First (1)
           or else Line = T.Content'Last (1) - 1
         then
            Put_Dash_Line;
         end if;
      end loop;
   end Dump_Table;

end Print_Table;
