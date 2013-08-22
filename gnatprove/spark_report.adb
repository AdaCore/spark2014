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

   procedure Handle_SPARK_File (Fn : String);
   --  Parse and extract all information from a single SPARK file.

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
      use GNATCOLL.JSON;
      Dict : constant JSON_Value := Read (Read_File_Into_String (Fn), Fn);
      Unit : constant Unit_Type := Mk_Unit (Ada.Directories.Base_Name (Fn));
   begin
      declare
         Entries : constant JSON_Array := Get (Dict);
      begin
         for Index in 1 .. Length (Entries) loop
            declare
               Result : constant JSON_Value := Get (Entries, Index);
            begin
               Add_SPARK_Status (Unit,
                                 Mk_Subp_Of_Entity (Result),
                                 Get (Get (Result, "spark")));
            end;
         end loop;
      end;
   end Handle_SPARK_File;

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
                 "  " & Subp_Name (Subp) & " at " & Subp_File (Subp) & ":" &
                   Int_Image (Subp_Line (Subp)));
            if Stat.SPARK then
               if Stat.VC_Count = Stat.VC_Proved then
                  Put_Line
                    (Handle,
                     " proved (" & Int_Image (Stat.VC_Count) & " checks)");
               else
                  Put_Line (Handle,
                            " not proved," & Stat.VC_Proved'Img &
                              " checks out of" & Stat.VC_Count'Img &
                              " proved");
               end if;
            else
               Put_Line (Handle, " skipped");
            end if;
         end For_Each_Subp;

      begin
         Put_Line
           (Handle,
            "in unit " & Unit_Name (Unit) & ", " &
              Int_Image (Num_Subps_SPARK (Unit)) & " subprograms out of " &
                Int_Image (Num_Subps (Unit)) & " analyzed");
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
