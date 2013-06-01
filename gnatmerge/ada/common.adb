------------------------------------------------------------------------------
--                                                                          --
--                            G N A T M E R G E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
--                                                                          --
-- gnatmerge is  free  software;  you can redistribute it and/or  modify it --
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
-- gnatmerge is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Text_IO;                use Ada.Text_IO;
with Asis;                       use Asis;
with GNAT.Strings;               use GNAT.Strings;
with GNATCOLL.Scripts;           use GNATCOLL.Scripts;
with GNATCOLL.Scripts.Python;    use GNATCOLL.Scripts.Python;
with GNATCOLL.Projects;          use GNATCOLL.Projects;
with GNATCOLL.Any_Types;         use GNATCOLL.Any_Types;
with GNATCOLL.VFS;               use GNATCOLL.VFS;
with Configuration;              use Configuration;
with Json_Tree;                  use Json_Tree;

package body Common is

   Project : Project_Tree;

   procedure Register_Project_Module (Repo : Scripts_Repository);
   procedure Register_Asis_Module (Repo : Scripts_Repository);

   procedure On_GPR_Path
     (Data    : in out Callback_Data'Class;
      Command : String);

   procedure On_GPR_Object_Dir
     (Data    : in out Callback_Data'Class;
      Command : String);

   procedure On_GPR_Attribute
     (Data    : in out Callback_Data'Class;
      Command : String);

   procedure On_Sloc_Reader_Constructor
     (Data    : in out Callback_Data'Class;
      Command : String);

   procedure On_Sloc_Reader_Map_To_Kind
     (Data    : in out Callback_Data'Class;
      Command : String);

   procedure On_Sloc_Reader_Iterate
     (Data    : in out Callback_Data'Class;
      Command : String);

   procedure On_Debug_Conf
     (Data    : in out Callback_Data'Class;
      Command : String);

   -----------------------
   -- On_GPR_Object_Dir --
   -----------------------

   procedure On_GPR_Object_Dir
     (Data    : in out Callback_Data'Class;
      Command : String)
   is
      pragma Unreferenced (Command);
   begin
      Set_Return_Value (Data,
                        Full_Name (Object_Dir (Project.Root_Project)).all);
   end On_GPR_Object_Dir;

   -----------------
   -- On_GPR_Path --
   -----------------

   procedure On_GPR_Path
     (Data    : in out Callback_Data'Class;
      Command : String)
   is
      pragma Unreferenced (Command);
   begin
      Set_Return_Value (Data,
                        Full_Name (Project_Path (Project.Root_Project)).all);
   end On_GPR_Path;

   ----------------------
   -- On_GPR_Attribute --
   ----------------------

   procedure On_GPR_Attribute
     (Data    : in out Callback_Data'Class;
      Command : String)
   is
      pragma Unreferenced (Command);
      Package_Name   : constant String := Nth_Arg (Data, 1);
      Attribute_Name : constant String := Nth_Arg (Data, 2);
      Index          : constant String := Nth_Arg (Data, 3, "");
      Value          : String_List_Access :=
        Attribute_Value (Project.Root_Project,
                         Build (Package_Name, Attribute_Name),
                         Index);
   begin
      Set_Return_Value_As_List (Data);
      for J in Value'Range loop
         Set_Return_Value (Data, Value (J).all);
      end loop;
      Free (Value);
   end On_GPR_Attribute;

   --------------------------------
   -- On_Sloc_Reader_Constructor --
   --------------------------------

   procedure On_Sloc_Reader_Constructor
     (Data    : in out Callback_Data'Class;
      Command : String)
   is
      pragma Unreferenced (Command);
      pragma Unreferenced (Data);
   begin
      null;
   end On_Sloc_Reader_Constructor;

   --------------------------------
   -- On_Sloc_Reader_Map_To_Kind --
   --------------------------------

   procedure On_Sloc_Reader_Map_To_Kind
     (Data    : in out Callback_Data'Class;
      Command : String)
   is
      pragma Unreferenced (Command);
      Inst      : constant Class_Instance := Nth_Arg (Data, 1);
      pragma Unreferenced (Inst);
      Asis_Name : constant String := Nth_Arg (Data, 2);
      Kind_Name : constant String := Nth_Arg (Data, 3);
      Kind      : Declaration_Kinds;
   begin
      Kind := Declaration_Kinds'Value (Asis_Name);
      Json_Tree.Insert (Kind, Kind_Name);
      exception
         when Constraint_Error =>
            Put_Line ("warning: "
                      & Asis_Name & " is not a valid Asis kind, ignoring it.");
   end On_Sloc_Reader_Map_To_Kind;

   ----------------------------
   -- On_Sloc_Reader_Iterate --
   ----------------------------

   procedure On_Sloc_Reader_Iterate
     (Data    : in out Callback_Data'Class;
      Command : String)
   is
      pragma Unreferenced (Command);
      Script    : constant Scripting_Language := Get_Script (Data);
      Inst      : constant Class_Instance := Nth_Arg (Data, 1);
      pragma Unreferenced (Inst);
      File_Name : constant String := Nth_Arg (Data, 2);
      Proc      : constant Subprogram_Type := Nth_Arg (Data, 3);

      procedure Execute_Proc
        (Kind : String;
         Name : String;
         Sloc : String;
         Low  : String;
         High : String);
      --  Marshall arguments and pass them to Proc

      ------------------
      -- Execute_Proc --
      ------------------

      procedure Execute_Proc
        (Kind : String;
         Name : String;
         Sloc : String;
         Low  : String;
         High : String)
      is
         Args : Callback_Data'Class := Create (Script, 5);
      begin
         Set_Nth_Arg (Args, 1, Kind);
         Set_Nth_Arg (Args, 2, Name);
         Set_Nth_Arg (Args, 3, Sloc);
         Set_Nth_Arg (Args, 4, Low);
         Set_Nth_Arg (Args, 5, High);
         declare
            Dummy : constant Any_Type := Execute (Proc, Args);
            pragma Unreferenced (Dummy);
         begin
            null;
         end;
      end Execute_Proc;

   begin
      Json_Tree.Open (File_Name);
      Json_Tree.Iterate (Execute_Proc'Access);
      Json_Tree.Close;
   end On_Sloc_Reader_Iterate;

   -------------------
   -- On_Debug_Conf --
   -------------------

   procedure On_Debug_Conf
     (Data    : in out Callback_Data'Class;
      Command : String)
   is
      pragma Unreferenced (Command);
   begin
      Set_Return_Value (Data, Debug_Conf.all);
   end On_Debug_Conf;

   ------------------------------------
   -- Register_Scripts_And_Functions --
   ------------------------------------

   function Register_Scripts_And_Functions return Scripts_Repository is
      Repo : Scripts_Repository;
   begin
      --  Register all scripting languages. In practice, you only need to
      --  register those you intend to support

      Repo := new Scripts_Repository_Record;
      Register_Python_Scripting (Repo, "gpr");
      Register_Project_Module (Repo);
      Register_Asis_Module (Repo);
      Register_Standard_Classes (Repo, "Console");
      return Repo;
   end Register_Scripts_And_Functions;

   -----------------------------
   -- Register_Project_Module --
   -----------------------------

   procedure Register_Project_Module (Repo : Scripts_Repository) is
   begin
      if Project_File.all /= "" then
         Project.Load (GNATCOLL.VFS.Create (+(Project_File.all)));
         --  ??? Add some error handling
         --  ??? Add support for -X
      else
         Project.Load_Empty_Project;
      end if;

      Register_Command
        (Repo, "path", 0, 0,
         Handler => On_GPR_Path'Unrestricted_Access);
      Register_Command
        (Repo, "object_dir", 0, 0,
         Handler => On_GPR_Object_Dir'Unrestricted_Access);
      Register_Command
        (Repo, "attribute", 2, 3,
         Handler => On_GPR_Attribute'Unrestricted_Access);
      Register_Command
        (Repo, "debug_conf", 0, 0,
         Handler => On_Debug_Conf'Unrestricted_Access);
   end Register_Project_Module;

   --------------------------
   -- Register_Asis_Module --
   --------------------------

   procedure Register_Asis_Module (Repo : Scripts_Repository) is
      Sloc_Reader_Class : Class_Type;
   begin
      Sloc_Reader_Class := GNATCOLL.Scripts.New_Class (Repo, "SlocReader");

      Register_Command
        (Repo, Constructor_Method, 0, 0,
         On_Sloc_Reader_Constructor'Access, Sloc_Reader_Class);
      Register_Command
        (Repo, "iterate", 2, 2,
         On_Sloc_Reader_Iterate'Access, Sloc_Reader_Class);
      Register_Command
        (Repo, "map_to_kind", 2, 2,
         On_Sloc_Reader_Map_To_Kind'Access, Sloc_Reader_Class);
   end Register_Asis_Module;

end Common;
