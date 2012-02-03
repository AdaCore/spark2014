------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           A L F A . F I L T E R                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                      Copyright (C) 2011-2012, AdaCore                    --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Atree;           use Atree;
with Nlists;          use Nlists;
with Sem_Util;        use Sem_Util;
with Sinfo;           use Sinfo;
with Stand;           use Stand;

with Alfa.Definition; use Alfa.Definition;
with Alfa.Common;     use Alfa.Common;

package body Alfa.Filter is

   -----------------------------
   -- Filter_Compilation_Unit --
   -----------------------------

   procedure Filter_Compilation_Unit (N : Node_Id) is
      Prefix                 : constant String :=
                                 File_Name_Without_Suffix (Sloc (N));
      --  All subprogram definitions should end up in this package, as it
      --  corresponds to the only Why file which is not included by other Why
      --  files, so that we will not redo the same proof more than once. In
      --  particular, subprogram bodies for expression functions, which may be
      --  originally declared in the package spec, should end up here.

   --  Start of processing for Filter_Compilation_Unit

   begin
      Types_In_Spec_File :=
        Make_Empty_Why_File (Prefix & Types_In_Spec_Suffix);
      Types_In_Body_File :=
        Make_Empty_Why_File (Prefix & Types_In_Body_Suffix);
      Variables_File := Make_Empty_Why_File (Prefix & Variables_Suffix);
      Context_In_Spec_File :=
        Make_Empty_Why_File (Prefix & Context_In_Spec_Suffix);
      Context_In_Body_File :=
        Make_Empty_Why_File (Prefix & Context_In_Body_Suffix);
      Main_File :=
        Make_Empty_Why_File (Prefix & Main_Suffix);

   end Filter_Compilation_Unit;

   -----------------------------
   -- Filter_Standard_Package --
   -----------------------------

   function Filter_Standard_Package return List_Of_Nodes.List is
      use List_Of_Nodes;
      Standard_Why_Package : List_Of_Nodes.List;
      Decl : Node_Id :=
        First (Visible_Declarations (Specification (Standard_Package_Node)));
   begin
      while Present (Decl) loop
         case Nkind (Decl) is
            when N_Full_Type_Declaration
               | N_Subtype_Declaration
               | N_Object_Declaration =>
               if Standard_Is_In_Alfa (Unique (Defining_Entity (Decl))) then
                  Standard_Why_Package.Append (Decl);
               end if;

            when others =>
               null;
         end case;

         Next (Decl);
      end loop;

      return Standard_Why_Package;
   end Filter_Standard_Package;

   ---------------------------------
   -- Filter_Out_Standard_Package --
   ---------------------------------

   function Filter_Out_Standard_Package return List_Of_Nodes.List is
      use List_Of_Nodes;
      Standard_Why_Package : List_Of_Nodes.List;
      Decl : Node_Id :=
        First (Visible_Declarations (Specification (Standard_Package_Node)));
      E : Entity_Id;
   begin
      while Present (Decl) loop
         case Nkind (Decl) is
            when N_Full_Type_Declaration |
                 N_Subtype_Declaration   |
                 N_Object_Declaration    =>

               E := Defining_Entity (Decl);
               if not Standard_Is_In_Alfa (Unique (E)) then
                  Standard_Why_Package.Append (E);
               end if;

            when others =>
               null;
         end case;

         Next (Decl);
      end loop;

      return Standard_Why_Package;
   end Filter_Out_Standard_Package;

end Alfa.Filter;
