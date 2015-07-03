------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                           P R I N T _ T A B L E                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

package body Print_Table is

   Cur_Line : Natural := 1;
   Cur_Col  : Natural := 1;

   ------------------
   -- Create_Table --
   ------------------

   function Create_Table (Lines, Cols : Natural) return Table is
      T : constant Table (1 .. Lines, 1 .. Cols) :=
        (others => (others => Cell'(Content => Null_Unbounded_String,
                                    Align   => Right_Align)));
   begin
      Cur_Line := 1;
      Cur_Col := 1;
      return T;
   end Create_Table;

   --------------
   -- Put_Cell --
   --------------

   procedure Put_Cell (T     : in out Table;
                       S     : String;
                       Align : Alignment_Type := Right_Align) is
   begin
      T (Cur_Line, Cur_Col) := Cell'(Content => To_Unbounded_String (S),
                                     Align   => Align);
      Cur_Col := Cur_Col + 1;
   end Put_Cell;

   procedure Put_Cell (T     : in out Table;
                       S     : Integer;
                       Align : Alignment_Type := Right_Align) is
   begin
      if S = 0 then
         Put_Cell (T, " .", Align);
      else
         Put_Cell (T, Integer'Image (S), Align);
      end if;
   end Put_Cell;

   --------------
   -- New_Line --
   --------------

   procedure New_Line (T : in out Table) is
   begin
      pragma Assert (Cur_Col = T'Last (2) + 1);
      Cur_Line := Cur_Line + 1;
      Cur_Col := 1;
   end New_Line;

   procedure Dump_Table (H : Ada.Text_IO.File_Type; T : Table) is
      type Width_Array is array (T'Range (2)) of Natural;
      Max_Width : Width_Array := (others => 10);

      procedure Compute_Max_Width;
      --  compute the maximum width for each column, minimum width is 10

      function Fit_Cell (C : Cell; Width : Natural) return String;
      --  @param C The cell
      --  @param Width the desired width
      --  @return a string of length Width, where the content of cell C has
      --     been fit according to the cell alignment

      -----------------------
      -- Compute_Max_Width --
      -----------------------

      procedure Compute_Max_Width is
      begin
         for Line in T'Range (1) loop
            for Col in T'Range (2) loop
               declare
                  Len : constant Natural :=
                    Length (T (Line, Col).Content) + 3;
               begin
                  if Max_Width (Col) < Len then
                     Max_Width (Col) := Len;
                  end if;
               end;
            end loop;
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

   begin
      Compute_Max_Width;
      for Line in T'Range (1) loop
         for Col in T'Range (2) loop
            Ada.Text_IO.Put (H,
                             Fit_Cell (T (Line, Col), Max_Width (Col)));
         end loop;
         Ada.Text_IO.New_Line (H);
      end loop;
   end Dump_Table;

end Print_Table;
