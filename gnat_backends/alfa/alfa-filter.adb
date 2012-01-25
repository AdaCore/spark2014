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

with AA_Util;         use AA_Util;
with ALI;             use ALI;
with Atree;           use Atree;
with Namet;           use Namet;
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

      Spec_Unit : Node_Id := Empty;
      Body_Unit : Node_Id := Empty;

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
        Make_Empty_Why_File (Prefix & Main_Suffix, No_Theory => True);

      case Nkind (Unit (N)) is
         when N_Package_Body =>
            Spec_Unit :=
              Enclosing_Lib_Unit_Node (Corresponding_Spec (Unit (N)));
            Body_Unit := N;

         --  gnat2why should be called on a compilable unit, which excludes
         --  calling it directy on a separate or the spec unit which has a
         --  corresponding body unit. The following cases correspond to spec
         --  units for which there is no body. The case of a [generic]
         --  subprogram declaration is when the subprogram is imported.

         when N_Package_Declaration                    |
              N_Package_Renaming_Declaration           |
              N_Generic_Package_Declaration            |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Declaration                 |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Subprogram_Declaration         |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            Spec_Unit := N;

         when N_Subprogram_Body =>
            if not Acts_As_Spec (Unit (N)) then
               Spec_Unit :=
                 Enclosing_Lib_Unit_Node (Corresponding_Spec (Unit (N)));
            end if;
            Body_Unit := N;

         when others =>
            raise Program_Error;
      end case;

      --  Take into account dependencies
      --  Add standard package only to types_vars for spec
      Add_With_Clause (Types_In_Spec_File, Standard_Why_Package_Name);
      --  Add "vertical" dependencies for a single package
      Add_With_Clause (Types_In_Body_File, Types_In_Spec_File);
      Add_With_Clause (Variables_File, Types_In_Body_File);
      Add_With_Clause (Context_In_Spec_File, Variables_File);
      Add_With_Clause (Context_In_Body_File, Context_In_Spec_File);

      --  for each with clause in the package spec, add horizontal
      --  dependencies between spec packages
      if Present (Spec_Unit) then
         declare
            Cursor : Node_Id := First (Context_Items (Spec_Unit));
         begin
            while Present (Cursor) loop
               case Nkind (Cursor) is
                  when N_With_Clause =>
                     declare
                        Pkg_Name : constant String :=
                                     File_Name_Without_Suffix
                                       (Sloc (Library_Unit (Cursor)));
                     begin
                        Add_With_Clause
                          (Types_In_Spec_File,
                           Pkg_Name & Types_In_Spec_Suffix);
                        Add_With_Clause
                          (Context_In_Spec_File,
                           Pkg_Name & Context_In_Spec_Suffix);
                     end;

                  when others =>
                     null;
               end case;
               Next (Cursor);
            end loop;
         end;
      end if;

      --  Add diagonal dependencies for spec -> body dependencies. This cannot
      --  be achieved by simply browsing the with'ed units of the main unit,
      --  for reasons described below. Instead, browse all ALI files read.

      if Present (Body_Unit) then
         for Index in ALIs.First .. ALIs.Last loop
            declare
               Pkg_Name : constant String :=
                            File_Name_Without_Suffix
                              (Get_Name_String (ALIs.Table (Index).Afile));
            begin
               --  Subprograms may mention in their effects variables from
               --  units which are not directly with'ed, hence the need to
               --  browse all ALI files.

               Add_With_Clause
                 (Context_In_Spec_File,
                  Pkg_Name & Variables_Suffix);

               --  If seperate units are used, units may be with'ed in the
               --  separate unit, and not directly in the main unit, hence the
               --  need to browse all ALI files.

               Add_With_Clause
                 (Types_In_Body_File,
                  Pkg_Name & Types_In_Spec_Suffix);
               Add_With_Clause
                 (Variables_File,
                  Pkg_Name & Types_In_Body_Suffix);
               Add_With_Clause
                 (Context_In_Body_File,
                  Pkg_Name & Context_In_Spec_Suffix);
            end;
         end loop;
      end if;

      --  If the current package is a child package, add the implicit with
      --  clause from the child spec to the parent spec. Currently this is not
      --  needed due to the conservative inclusions above. Keep it commented
      --  out as the inclusion scheme will still change.

--        declare
--           Def_Unit_Name : Node_Id := Empty;
--        begin
--           case Nkind (Unit (N)) is
--              when N_Package_Declaration =>
--                 Def_Unit_Name :=
--                    Defining_Unit_Name (Specification (Unit (N)));
--
--              when N_Package_Body =>
--                 Def_Unit_Name := Defining_Unit_Name ((Unit (N)));
--
--              when others =>
--                 null;
--           end case;
--
--           if Present (Def_Unit_Name) and then
--              Nkind (Def_Unit_Name) = N_Defining_Program_Unit_Name then
--              declare
--                 Target_Name : constant String :=
--                    File_Name_Without_Suffix
--                      (Sloc (Entity (Name (Def_Unit_Name))));
--              begin
--                 Add_With_Clause
--                    (Types_File, Target_Name & Types_Suffix);
--                 Add_With_Clause
--                    (Context_File, Target_Name & Context_Suffix);
--              end;
--           end if;
--        end;
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
