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
with Ada.Directories;
with Ada.Text_IO;

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

   function Mk_Subp_Of_Entity (Ent : GNATCOLL.JSON.JSON_Value)
      return Subp_Type;
   --  convert a json entity dict to a subp

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
   Print_Proof_Report (Handle);
   Close (Handle);
end SPARK_Report;
