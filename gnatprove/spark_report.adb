------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                           S P A R K _ R E P O R T                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Ada.Containers;          use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Strings.Hash;
with Ada.Strings.Unbounded;   use Ada.Strings.Unbounded;
with Ada.Characters.Handling; use Ada.Characters.Handling;
with Ada.Command_Line;
with Ada.Containers.Generic_Array_Sort;
with Ada.Directories;
with Ada.Text_IO;
with Ada.Strings.Fixed;

with GNAT.Directory_Operations.Iteration;
with GNAT.OS_Lib;             use GNAT.OS_Lib;

with GNATCOLL.JSON;

with Call;                    use Call;
with String_Utils;            use String_Utils;
with SPARK_Violations;
with VC_Kinds;

with Configuration;           use Configuration;
with Report_Database;         use Report_Database;

procedure SPARK_Report is

   type SPARK_Status is (Supported, Not_Yet, Unsupported);
   type SPARK_Counts is array (SPARK_Status) of Natural;

   Global_Count : SPARK_Counts := SPARK_Counts'(others => 0);

   function SPARK_Count return Natural is
     (Global_Count (Supported) + Global_Count (Not_Yet));

   function Not_SPARK_Count return Natural is (Global_Count (Unsupported));

   function Total_Count return Natural is (SPARK_Count + Not_SPARK_Count);

   procedure Incr_Count (S : SPARK_Status);

   type Violation_Count is array (SPARK_Violations.Vkind) of Natural;
   Violation_Cnt : Violation_Count := (others => 0);

   function Filename_Hash (N : Unbounded_String) return Hash_Type is
      (Ada.Strings.Hash (To_String (N)));

   package Filename_Map is new Hashed_Maps
     (Key_Type        => Unbounded_String,
      Element_Type    => Natural,
      Hash            => Filename_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Total_Files        : Natural := 0;
   File_SPARK_Cnt     : Filename_Map.Map;
   File_Not_SPARK_Cnt : Filename_Map.Map;

   procedure Handle_SPARK_File (Fn : String);
   --  Parse and extract all information from a single SPARK file.

   procedure Handle_SPARK_Line (Line : String);
   --  Parse and extract all information from a single SPARK line.

   procedure Handle_Proof_File (Fn : String);
   --  Parse and extract all information from a proof result file

   procedure Handle_Source_Dir (Dir : String);
   --  Parse all result files of this directory.

   procedure Print_Report (Handle : Ada.Text_IO.File_Type);
   --  Print the final SPARK report in the file

   function Mk_Subp_Of_Entity (Ent : GNATCOLL.JSON.JSON_Value)
      return Subp_Type;
   --  convert a json entity dict to a subp

   procedure Print_Statistics
     (Handle      : Ada.Text_IO.File_Type;
      Label       : String;
      Label_Len   : Natural;
      Cnt         : Integer;
      Total       : Integer;
      Cnt_Padding : Boolean);
   --  Print a line of the form:
   --    label:  X% (Cnt / Total)
   --  where X is the ration Cnt / Total expressed in percent.

   procedure Print_Proof_Report (Handle : Ada.Text_IO.File_Type);
   --  print the proof report in the given file

   -----------------------
   -- Mk_Subp_Of_Entity --
   -----------------------

   function Mk_Subp_Of_Entity (Ent : GNATCOLL.JSON.JSON_Value)
                               return Subp_Type is
      use GNATCOLL.JSON;
   begin
      return
        Mk_Subp (Get (Get (Ent, "name")),
                 Get (Get (Ent, "file")),
                 Get (Get (Ent, "line")));
   end Mk_Subp_Of_Entity;

   -----------------------
   -- Handle_Proof_File --
   -----------------------

   procedure Handle_Proof_File (Fn : String)
   is
      use GNATCOLL.JSON;
      Dict : constant JSON_Value := Read (Read_File_Into_String (Fn), Fn);
      Unit : constant Unit_Type := Mk_Unit (Ada.Directories.Base_Name (Fn));
      Entries : constant JSON_Array := Get (Dict);
   begin
      for Index in 1 .. Length (Entries) loop
         declare
            Result : constant JSON_Value := Get (Entries, Index);
            Severe : constant String     := Get (Get (Result, "severity"));
         begin
            Add_Proof_Result (Unit,
                              Mk_Subp_Of_Entity (Get (Result, "entity")),
                              Severe = "info");
         end;
      end loop;
   end Handle_Proof_File;

   -----------------------
   -- Handle_SPARK_File --
   -----------------------

   procedure Handle_SPARK_File (Fn : String)
   is
      procedure Iterate_SPARK_Lines is new
        For_Line_In_File (Handle_SPARK_Line);

      Cur_SPARK_Cnt     : constant Natural := SPARK_Count;
      Cur_Not_SPARK_Cnt : constant Natural := Not_SPARK_Count;

   begin
      Iterate_SPARK_Lines (Fn);

      --  Update counts for files

      Total_Files := Total_Files + 1;
      File_SPARK_Cnt.Insert
        (To_Unbounded_String (Fn), SPARK_Count - Cur_SPARK_Cnt);
      File_Not_SPARK_Cnt.Insert
        (To_Unbounded_String (Fn), Not_SPARK_Count - Cur_Not_SPARK_Cnt);
   end Handle_SPARK_File;

   -----------------------
   -- Handle_SPARK_Line --
   -----------------------

   procedure Handle_SPARK_Line (Line : String) is
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
                   Violation_Cnt (SPARK_Violations.Violation_From_Msg.Element
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

      --  Update global counts

      Cur := Line'First;
      if Line (Cur) = '+' then
         Incr_Count (Supported);
      elsif Line (Cur) = '*' then
         Incr_Count (Not_Yet);
      else
         Incr_Count (Unsupported);
      end if;

      --  Update counts for violations

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
   end Handle_SPARK_Line;

   -----------------------
   -- Handle_Source_Dir --
   -----------------------

   procedure Handle_Source_Dir (Dir : String)
   is
      procedure Local_Handle_SPARK_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean);
      --  Wrapper for Handle_SPARK_File

      procedure Local_Handle_Proof_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean);
      --  Wrapper for Handle_Proof_File

      -----------------------------
      -- Local_Handle_Proof_File --
      -----------------------------

      procedure Local_Handle_Proof_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean) is
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);
         Handle_Proof_File (Item);
      end Local_Handle_Proof_File;

      -----------------------------
      -- Local_Handle_SPARK_File --
      -----------------------------

      procedure Local_Handle_SPARK_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean) is
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);
         Handle_SPARK_File (Item);
      end Local_Handle_SPARK_File;

      procedure Iterate_SPARK is new
         GNAT.Directory_Operations.Iteration.Wildcard_Iterator
          (Action => Local_Handle_SPARK_File);

      procedure Iterate_Proof is new
         GNAT.Directory_Operations.Iteration.Wildcard_Iterator
          (Action => Local_Handle_Proof_File);

      Save_Dir : constant String := Ada.Directories.Current_Directory;

      --  beginning of processing for Handle_Source_Dir;

   begin
      Ada.Directories.Set_Directory (Dir);
      Iterate_SPARK (Path => '*' & SPARK_Violations.SPARK_Suffix);
      Iterate_Proof (Path => '*' & VC_Kinds.Proof_Suffix);
      Ada.Directories.Set_Directory (Save_Dir);
   exception
      when others =>
         Ada.Directories.Set_Directory (Save_Dir);
         raise;
   end Handle_Source_Dir;

   ----------------
   -- Incr_Count --
   ----------------

   procedure Incr_Count (S : SPARK_Status) is
   begin
      Global_Count (S) := Global_Count (S) + 1;
   end Incr_Count;

   ------------------------
   -- Print_Proof_Report --
   ------------------------

   procedure Print_Proof_Report (Handle : Ada.Text_IO.File_Type) is
      use Ada.Text_IO;

      procedure For_Each_Unit (Unit : Unit_Type);
      --  print proof results for the given unit

      -------------------
      -- For_Each_Unit --
      -------------------

      procedure For_Each_Unit (Unit : Unit_Type) is

         procedure For_Each_Subp (Subp : Subp_Type; Stat : Stat_Rec);

         -------------------
         -- For_Each_Subp --
         -------------------

         procedure For_Each_Subp (Subp : Subp_Type; Stat : Stat_Rec) is
         begin
            Put (Handle,
                 " " & Subp_Name (Subp) & " at " & Subp_File (Subp) & ":" &
                 Int_Image (Subp_Line (Subp)));
            if Stat.VC_Count = Stat.VC_Proved then
               Put_Line (Handle,
                         " proved (" & Int_Image (Stat.VC_Count) & " checks)");
            else
               Put_Line (Handle,
                         " not proved," & Stat.VC_Proved'Img & " out of" &
                           Stat.VC_Count'Img & " proved");
            end if;
         end For_Each_Subp;

      begin
         Put_Line (Handle, "unit " & Unit_Name (Unit) & " analyzed");
         Iter_Unit_Subps (Unit, For_Each_Subp'Access);
      end For_Each_Unit;
   begin
      Put_Line (Handle, "Analyzed" & Num_Units'Img & " units");
      Iter_Units (For_Each_Unit'Access);
   end Print_Proof_Report;

   ------------------
   -- Print_Report --
   ------------------

   procedure Print_Report (Handle : Ada.Text_IO.File_Type) is
      use Ada.Text_IO;

      type Violation_Ranking is
        array (SPARK_Violations.Vkind range <>) of SPARK_Violations.Vkind;
      Violation_Rank : Violation_Ranking (SPARK_Violations.Vkind);

      File_Names : array (1 .. Total_Files) of Unbounded_String;
      type File_Ranking is array (Positive range <>) of Positive;
      File_SPARK_Rank     : File_Ranking (1 .. Total_Files);
      File_Not_SPARK_Rank : File_Ranking (1 .. Total_Files);

      -----------------------
      -- Local Subprograms --
      -----------------------

      function Greater_Count (V1, V2 : SPARK_Violations.Vkind) return Boolean;

      function Greater_SPARK_Count (F1, F2 : Positive) return Boolean;
      function Greater_Not_SPARK_Count (F1, F2 : Positive) return Boolean;

      procedure Print_File_Count
        (M            : Filename_Map.Map;
         M_Complement : Filename_Map.Map;
         R            : File_Ranking);

      generic
         with function Violation_Filter
           (V : SPARK_Violations.Vkind) return Boolean;
      procedure Print_Violations;

      -------------------
      -- Greater_Count --
      -------------------

      function Greater_Count (V1, V2 : SPARK_Violations.Vkind) return Boolean
      is
      begin
         return Violation_Cnt (V1) > Violation_Cnt (V2);
      end Greater_Count;

      -------------------------
      -- Greater_SPARK_Count --
      -------------------------

      function Greater_SPARK_Count (F1, F2 : Positive) return Boolean is
      begin
         return File_SPARK_Cnt.Element (File_Names (F1)) >
           File_SPARK_Cnt.Element (File_Names (F2));
      end Greater_SPARK_Count;

      -----------------------------
      -- Greater_Not_SPARK_Count --
      -----------------------------

      function Greater_Not_SPARK_Count (F1, F2 : Positive) return Boolean is
      begin
         return File_Not_SPARK_Cnt.Element (File_Names (F1)) >
           File_Not_SPARK_Cnt.Element (File_Names (F2));
      end Greater_Not_SPARK_Count;

      ----------------------
      -- Print_File_Count --
      ----------------------

      procedure Print_File_Count
        (M            : Filename_Map.Map;
         M_Complement : Filename_Map.Map;
         R            : File_Ranking)
      is
         use Filename_Map;
         Num_Printed : Natural := 0;

      begin
         for J in R'Range loop
            declare
               F_Name  : constant Unbounded_String := File_Names (R (J));
               F_Cnt   : constant Natural := M.Element (F_Name);
               Lab     : constant String :=
                           ' ' & GNAT.Directory_Operations.Base_Name
                                   (To_String (F_Name),
                                    SPARK_Violations.SPARK_Suffix);
               Tot_Cnt : constant Natural :=
                           F_Cnt + M_Complement.Element (F_Name);
            begin
               if F_Cnt > 0 then
                  Num_Printed := Num_Printed + 1;
                  Print_Statistics (Handle      => Handle,
                                    Label       => Lab,
                                    Label_Len   => Label_Length,
                                    Cnt         => F_Cnt,
                                    Total       => Tot_Cnt,
                                    Cnt_Padding => False);
               end if;
            end;
         end loop;

         if Num_Printed = 0 then
            Put_Line (Handle, " (none)");
         end if;
      end Print_File_Count;

      ----------------------
      -- Print_Violations --
      ----------------------

      procedure Print_Violations is
         Num_Printed : Natural := 0;

      begin
         for J in SPARK_Violations.Vkind loop
            declare
               V     : constant SPARK_Violations.Vkind := Violation_Rank (J);
               V_Cnt : constant Natural := Violation_Cnt (V);
               Lab   : constant String :=
                         ' ' & To_String (SPARK_Violations.Violation_Msg (V));
            begin
               if Violation_Filter (V)
                 and then V_Cnt > 0
               then
                  Num_Printed := Num_Printed + 1;
                  Print_Statistics (Handle      => Handle,
                                    Label       => Lab,
                                    Label_Len   => Label_Length,
                                    Cnt         => V_Cnt,
                                    Total       => Total_Count,
                                    Cnt_Padding => True);
               end if;
            end;
         end loop;

         if Num_Printed = 0 then
            Put_Line (Handle, " (none)");
         end if;
      end Print_Violations;

      procedure Sort_Violations is new
        Ada.Containers.Generic_Array_Sort
          (Index_Type   => SPARK_Violations.Vkind,
           Element_Type => SPARK_Violations.Vkind,
           Array_Type   => Violation_Ranking,
           "<"          => Greater_Count);

      procedure Sort_Files_SPARK is new
        Ada.Containers.Generic_Array_Sort
          (Index_Type   => Positive,
           Element_Type => Positive,
           Array_Type   => File_Ranking,
           "<"          => Greater_SPARK_Count);

      procedure Sort_Files_Not_SPARK is new
        Ada.Containers.Generic_Array_Sort
          (Index_Type   => Positive,
           Element_Type => Positive,
           Array_Type   => File_Ranking,
           "<"          => Greater_Not_SPARK_Count);

      procedure Print_NYI_Violations is new
        Print_Violations (SPARK_Violations.Is_Not_Yet_Implemented);

      procedure Print_NIR_Violations is new
        Print_Violations (SPARK_Violations.Is_Not_In_Roadmap);

   begin
      --  global statistics

      Print_Statistics (Handle      => Handle,
                        Label       => "Subprograms in SPARK",
                        Label_Len   => Label_Length,
                        Cnt         => SPARK_Count,
                        Total       => Total_Count,
                        Cnt_Padding => True);
      Print_Statistics (Handle      => Handle,
                        Label       => "  ... already supported",
                        Label_Len   => Label_Length,
                        Cnt         => Global_Count (Supported),
                        Total       => Total_Count,
                        Cnt_Padding => True);
      Print_Statistics (Handle      => Handle,
                        Label       => "  ... not yet supported",
                        Label_Len   => Label_Length,
                        Cnt         => Global_Count (Not_Yet),
                        Total       => Total_Count,
                        Cnt_Padding => True);
      Print_Statistics (Handle      => Handle,
                        Label       => "Subprograms not in SPARK",
                        Label_Len   => Label_Length,
                        Cnt         => Global_Count (Unsupported),
                        Total       => Total_Count,
                        Cnt_Padding => True);

      --  statistics per violations

      for J in SPARK_Violations.Vkind loop
         Violation_Rank (J) := J;
      end loop;

      Sort_Violations (Violation_Rank);

      New_Line (Handle);
      Put_Line (Handle, "Subprograms not in SPARK due to" &
                  " (possibly more than one reason):");
      Print_NIR_Violations;

      New_Line (Handle);
      Put_Line (Handle, "Subprograms not yet supported due to" &
                  " (possibly more than one reason):");
      Print_NYI_Violations;

      --  statistics per file

      declare
         use Filename_Map;
         C : Cursor;
      begin
         C := File_SPARK_Cnt.First;
         for J in 1 .. Total_Files loop
            File_Names (J)         := Key (C);
            File_SPARK_Rank (J)     := J;
            File_Not_SPARK_Rank (J) := J;
            Next (C);
         end loop;
      end;

      Sort_Files_SPARK (File_SPARK_Rank);
      Sort_Files_Not_SPARK (File_Not_SPARK_Rank);

      New_Line (Handle);
      Put_Line (Handle,
                "Units with the largest number of subprograms in SPARK:");
      Print_File_Count (M            => File_SPARK_Cnt,
                        M_Complement => File_Not_SPARK_Cnt,
                        R            => File_SPARK_Rank);

      New_Line (Handle);
      Put_Line (Handle,
                "Units with the largest number of subprograms not in SPARK:");
      Print_File_Count (M            => File_Not_SPARK_Cnt,
                        M_Complement => File_SPARK_Cnt,
                        R            => File_Not_SPARK_Rank);
   end Print_Report;

   ----------------------
   -- Print_Statistics --
   ----------------------

   procedure Print_Statistics
     (Handle      : Ada.Text_IO.File_Type;
      Label       : String;
      Label_Len   : Natural;
      Cnt         : Integer;
      Total       : Integer;
      Cnt_Padding : Boolean)
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
      Fixed_Len        : constant Natural :=
                         Natural'Min (Label_Len, Label'Last - Label'First + 1);
   begin
      Fixed_Len_Label (1 .. Fixed_Len) :=
        Label (Label'First .. Label'First + Fixed_Len - 1);
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

      if Cnt_Padding then
         Put (Handle, Integer_Image_Padded (Cnt, Total_Characters));
      else
         Put (Handle, Integer_Image (Cnt));
      end if;

      Put (Handle, "/");
      Put (Handle, Integer_Image (Total));
      Put_Line (Handle, ")");
   end Print_Statistics;

   procedure Iterate_Source_Dirs is new For_Line_In_File (Handle_Source_Dir);

   Source_Directories_File : GNAT.OS_Lib.String_Access;

   use Ada.Text_IO;

   Handle : File_Type;

   --  Start of SPARK_Report

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Abort_With_Message ("No source directory file given, aborting");
   end if;
   Source_Directories_File := new String'(Ada.Command_Line.Argument (1));
   Iterate_Source_Dirs (Source_Directories_File.all);
   Create (Handle,
           Out_File,
           Configuration.SPARK_Report_File
             (GNAT.Directory_Operations.Dir_Name
                (Source_Directories_File.all)));
   Print_Report (Handle);
   Print_Proof_Report (Handle);
   Close (Handle);
end SPARK_Report;
