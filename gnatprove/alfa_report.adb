------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                            A L F A _ R E P O R T                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or modify it  --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnatprove is distributed in the hope that it will  be  useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Handling;             use Ada.Characters.Handling;
with Ada.Command_Line;
with Ada.Containers.Generic_Array_Sort;
with Ada.Directories;
with Ada.Text_IO;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;               use Ada.Strings.Unbounded;

with Call;                                use Call;
with GNAT.Directory_Operations.Iteration;
with GNAT.OS_Lib;                         use GNAT.OS_Lib;

with Alfa_Violations;

with Configuration;

procedure Alfa_Report is

   Total_Cnt        : Natural := 0;
   Alfa_Cnt         : Natural := 0;
   Not_Yet_Alfa_Cnt : Natural := 0;

   Label_Length : constant := 26;

   type Violation_Count is array (Alfa_Violations.Vkind) of Natural;
   Violation_Cnt : Violation_Count := (others => 0);

   procedure Handle_Alfa_File (Fn : String);
   --  Parse and extract all information from a single Alfa file.

   procedure Handle_Alfa_Line (Line : String);
   --  Parse and extract all information from a single Alfa line.

   procedure Handle_Source_Dir (Dir : String);
   --  Parse all .alfa files of this directory.

   procedure Print_Report;
   --  Print the final Alfa report

   procedure Print_Statistics
     (Handle    : Ada.Text_IO.File_Type;
      Label     : String;
      Label_Len : Natural;
      Cnt       : Integer;
      Total     : Integer);
   --  Print a line of the form:
   --    label:  X% (Cnt / Total)
   --  where X is the ration Cnt / Total expressed in percent.

   ----------------------
   -- Handle_Alfa_File --
   ----------------------

   procedure Handle_Alfa_File (Fn : String)
   is
      procedure Iterate_Alfa_Lines is new For_Line_In_File (Handle_Alfa_Line);
   begin
      Iterate_Alfa_Lines (Fn);
   end Handle_Alfa_File;

   ----------------------
   -- Handle_Alfa_Line --
   ----------------------

   procedure Handle_Alfa_Line (Line : String) is
      Violation_Mode : Boolean := False;
      Cur            : Positive;

      procedure Add_One_Violation (S : String);
      --  Increment violation counter for violation called S

      function Get_Name return String with
        Pre  => Cur in Line'Range
                  and then Is_Alphanumeric (Line (Cur))
                  and then not Is_Alphanumeric (Line (Line'Last)),
        Post => Get_Name'Result /= "";
      --  Return the longest alphanumeric substring possibly containing spaces
      --  of Line starting at Cur. Update Cur to the character past this
      --  substring.

      -----------------------
      -- Add_One_Violation --
      -----------------------

      procedure Add_One_Violation (S : String) is
         Count : Natural renames
                   Violation_Cnt (Alfa_Violations.Violation_From_Msg
                                  (To_Unbounded_String (S)));
      begin
         Count := Count + 1;
      end Add_One_Violation;

      --------------
      -- Get_Name --
      --------------

      function Get_Name return String is
         Start, Stop : Natural;
      begin
         Start := Cur;
         while Cur <= Line'Last
           and then (Is_Alphanumeric (Line (Cur)) or else Line (Cur) = ' ')
         loop
            Cur := Cur + 1;
         end loop;
         Stop := Cur - 1;
         return Line (Start .. Stop);
      end Get_Name;

   begin
      if Line'Length = 0 then
         return;
      end if;

      Cur := Line'First;
      Total_Cnt := Total_Cnt + 1;
      if Line (Cur) = '+' then
         Alfa_Cnt := Alfa_Cnt + 1;
      elsif Line (Cur) = '*' then
         Not_Yet_Alfa_Cnt := Not_Yet_Alfa_Cnt + 1;
      end if;

      while Cur <= Line'Last loop
         case Line (Cur) is
            when '(' | '[' =>
               Violation_Mode := True;
            when others =>
               if Violation_Mode
                 and then Is_Alphanumeric (Line (Cur))
               then
                  Add_One_Violation (Get_Name);
               end if;
         end case;
         Cur := Cur + 1;
      end loop;
   end Handle_Alfa_Line;

   -----------------------
   -- Handle_Source_Dir --
   -----------------------

   procedure Handle_Source_Dir (Dir : String)
   is
      procedure Local_Handle_Alfa_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean);

      ----------------------------
      -- Local_Handle_Alfa_File --
      ----------------------------

      procedure Local_Handle_Alfa_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean) is
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);
         Handle_Alfa_File (Item);
      end Local_Handle_Alfa_File;

      procedure Iterate is new
         GNAT.Directory_Operations.Iteration.Wildcard_Iterator
           (Action => Local_Handle_Alfa_File);

      Save_Dir : constant String := Ada.Directories.Current_Directory;

      --  beginning of processing for Handle_Source_Dir;

   begin
      Ada.Directories.Set_Directory (Dir);
      Iterate (Path => "*.alfa");
      Ada.Directories.Set_Directory (Save_Dir);
   exception
      when others =>
         Ada.Directories.Set_Directory (Save_Dir);
         raise;
   end Handle_Source_Dir;

   ------------------
   -- Print_Report --
   ------------------

   procedure Print_Report
   is
      use Ada.Text_IO;
      Handle : File_Type;

      type Violation_Ranking is
        array (Alfa_Violations.Vkind range <>) of Alfa_Violations.Vkind;
      Violation_Rank : Violation_Ranking (Alfa_Violations.Vkind);

      function Greater_Count (V1, V2 : Alfa_Violations.Vkind) return Boolean;

      function Greater_Count (V1, V2 : Alfa_Violations.Vkind) return Boolean is
      begin
         return Violation_Cnt (V1) > Violation_Cnt (V2);
      end Greater_Count;

      procedure Sort_Violations is new
        Ada.Containers.Generic_Array_Sort
          (Index_Type   => Alfa_Violations.Vkind,
           Element_Type => Alfa_Violations.Vkind,
           Array_Type   => Violation_Ranking,
           "<"          => Greater_Count);

      generic
         with function Violation_Filter
           (V : Alfa_Violations.Vkind) return Boolean;
      procedure Print_Violations;

      procedure Print_Violations is
      begin
         for J in Alfa_Violations.Vkind loop
            declare
               V     : constant Alfa_Violations.Vkind := Violation_Rank (J);
               V_Cnt : constant Natural := Violation_Cnt (V);
               Lab   : constant String :=
                         ' ' & To_String (Alfa_Violations.Violation_Msg (V));
            begin
               if Violation_Filter (V)
                 and then V_Cnt > 0
               then
                  Print_Statistics (Handle,
                                    Lab,
                                    Label_Length,
                                    V_Cnt,
                                    Total_Cnt);
               end if;
            end;
         end loop;
      end Print_Violations;

      procedure Print_NYI_Violations is new
        Print_Violations (Alfa_Violations.Is_Not_Yet_Implemented);

      procedure Print_NIR_Violations is new
        Print_Violations (Alfa_Violations.Is_Not_In_Roadmap);

   begin
      Create (Handle, Out_File, Configuration.Alfa_Report_File);
      Print_Statistics (Handle, "Subprograms in Alfa       ", Label_Length,
                        Alfa_Cnt + Not_Yet_Alfa_Cnt,
                        Total_Cnt);
      Print_Statistics (Handle, "  ... already implemented ", Label_Length,
                        Alfa_Cnt,
                        Total_Cnt);
      Print_Statistics (Handle, "  ... not yet implemented ", Label_Length,
                        Not_Yet_Alfa_Cnt,
                        Total_Cnt);
      Print_Statistics (Handle, "Subprograms not in Alfa   ", Label_Length,
                        Total_Cnt - Alfa_Cnt - Not_Yet_Alfa_Cnt,
                        Total_Cnt);

      for J in Alfa_Violations.Vkind loop
         Violation_Rank (J) := J;
      end loop;

      Sort_Violations (Violation_Rank);

      New_Line (Handle);
      Put_Line (Handle, "Subprograms not in Alfa due to" &
                  " (possibly more than one reason):");
      Print_NYI_Violations;

      New_Line (Handle);
      Put_Line (Handle, "Subprograms not yet supported due to" &
                  " (possibly more than one reason):");
      Print_NIR_Violations;

   end Print_Report;

   ----------------------
   -- Print_Statistics --
   ----------------------

   procedure Print_Statistics
     (Handle    : Ada.Text_IO.File_Type;
      Label     : String;
      Label_Len : Natural;
      Cnt       : Integer;
      Total     : Integer)
   is
      use Ada.Text_IO;

      function Integer_Image (X : Integer) return String;
      --  Return image of integer X without leading whitespace

      function Integer_Image (X : Integer) return String is
      begin
         return Ada.Strings.Fixed.Trim (Integer'Image (X), Ada.Strings.Left);
      end Integer_Image;

      function Integer_Image_Padded
        (X    : Integer;
         Size : Natural) return String;
      --  Return image of integer X with enough leading whitespace to pad the
      --  result up to Size characters.

      function Integer_Image_Padded
        (X    : Integer;
         Size : Natural) return String
      is
         Img : constant String := Integer_Image (X);
      begin
         if Img'Last >= Size then
            return Img;
         else
            declare
               Pad : constant String (1 .. Size - Img'Last) :=
                 (others => Ada.Strings.Space);
            begin
               return Pad & Img;
            end;
         end if;
      end Integer_Image_Padded;

      subtype Percentage is Integer range 0 .. 100;

      function Percentage_Image (X : Percentage) return String;
      --  Return image of percentage with
      --    - no leading whitespace for X = 100
      --    - one leading whitespace for 10 <= X <= 99
      --    - two leading whitespaces for 0 <= X <= 9
      --  In order to properly align values.

      function Percentage_Image (X : Percentage) return String is
      begin
         return Integer_Image_Padded (X, 3);
      end Percentage_Image;

      Percent          : Percentage;
      Total_Characters : constant Natural := Integer_Image (Total)'Last;

      Fixed_Len_Label  : String (1 .. Label_Len) := (others => ' ');

   begin
      Fixed_Len_Label (1 .. Natural'Min (Label_Len, Label'Last)) := Label;
      Put (Handle, Fixed_Len_Label);
      Put (Handle, ": ");

      if Total = 0 then
         pragma Assert (Cnt = 0);
         Percent := 0;
      else
         Percent := Integer (Float (Cnt) / Float (Total) * 100.0);
      end if;

      Put (Handle, Percentage_Image (Percent));
      Put (Handle, "% (");
      Put (Handle, Integer_Image_Padded (Cnt, Total_Characters));
      Put (Handle, "/");
      Put (Handle, Integer_Image (Total));
      Put_Line (Handle, ")");
   end Print_Statistics;

   procedure Iterate_Source_Dirs is new For_Line_In_File (Handle_Source_Dir);

   Source_Directories_File : GNAT.OS_Lib.String_Access;

   --  begin processing for Alfa_Report;

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Abort_With_Message ("No source directory file given, aborting");
   end if;
   Source_Directories_File := new String'(Ada.Command_Line.Argument (1));
   Iterate_Source_Dirs (Source_Directories_File.all);
   Print_Report;
end Alfa_Report;
