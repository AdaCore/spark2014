------------------------------------------------------------------------------
--                                                                          --
--                            G N A T M E R G E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012, AdaCore                       --
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

with GNATCOLL.Scripts;        use GNATCOLL.Scripts;
with GNATCOLL.Scripts.Python; use GNATCOLL.Scripts.Python;
with GNATCOLL.Projects;       use GNATCOLL.Projects;
with GNATCOLL.VFS;            use GNATCOLL.VFS;
with GNAT.Strings;            use GNAT.Strings;
with Configuration;           use Configuration;

package body Common is

   Project : Project_Tree;

   procedure Register_Project_Module (Repo : Scripts_Repository);

   procedure On_GPR_Path
     (Data    : in out Callback_Data'Class;
      Command : String);

   procedure On_GPR_Object_Dir
     (Data    : in out Callback_Data'Class;
      Command : String);

   procedure On_GPR_Attribute
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

   ------------------------------------
   -- Register_Scripts_And_Functions --
   ------------------------------------

   function Register_Scripts_And_Functions return Scripts_Repository is
      Repo : Scripts_Repository;
   begin
      --  Register all scripting languages. In practice, you only need to
      --  register those you intend to support

      Repo := new Scripts_Repository_Record;
      Register_Project_Module (Repo);
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

      Register_Python_Scripting (Repo, "gpr");
      Register_Command
        (Repo, "path", 0, 0,
         Handler => On_GPR_Path'Unrestricted_Access);
      Register_Command
        (Repo, "object_dir", 0, 0,
         Handler => On_GPR_Object_Dir'Unrestricted_Access);
      Register_Command
        (Repo, "attribute", 2, 3,
         Handler => On_GPR_Attribute'Unrestricted_Access);
   end Register_Project_Module;

end Common;
