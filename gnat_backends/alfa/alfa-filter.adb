------------------------------------------------------------------------------
--                                                                          --
--                         GNAT BACK-END COMPONENTS                         --
--                                                                          --
--                           A L F A . F I L T E R                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--             Copyright (C) 2011, Free Software Foundation, Inc.           --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Atree;        use Atree;
with Namet;        use Namet;
with Nlists;       use Nlists;
with Sem_Util;     use Sem_Util;
with Sinfo;        use Sinfo;
with Stand;        use Stand;

with ALFA.Definition; use ALFA.Definition;
with ALFA.Common; use ALFA.Common;

package body ALFA.Filter is

   Standard_Why_Package      : List_Of_Nodes.List :=
      List_Of_Nodes.Empty_List;
   Standard_Why_Package_Name : constant String := "_standard";

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Traverse_Subtree
     (N       : Node_Id;
      Process : access procedure (N : Node_Id));
   --  Traverse the subtree of N and call Process on selected nodes

   -----------------------------
   -- Filter_Compilation_Unit --
   -----------------------------

   procedure Filter_Compilation_Unit (N : Node_Id) is
      Prefix                 : constant String :=
         File_Name_Without_Suffix (Sloc (N));
      Types_Vars_Spec_Suffix : constant String := "__types_vars_spec";
      Types_Vars_Body_Suffix : constant String := "__types_vars_body";
      Subp_Spec_Suffix       : constant String := "__subp_spec";
      Main_Suffix            : constant String := "__package";

      Types_Vars_Spec : Why_Package :=
         Make_Empty_Why_Pack (Prefix & Types_Vars_Spec_Suffix);
      Types_Vars_Body : Why_Package :=
         Make_Empty_Why_Pack (Prefix & Types_Vars_Body_Suffix);
      Subp_Spec       : Why_Package :=
         Make_Empty_Why_Pack (Prefix & Subp_Spec_Suffix);

      Subp_Body       : Why_Package :=
         Make_Empty_Why_Pack (Prefix & Main_Suffix);

      --  All subprogram definitions should end up in this package, as it
      --  corresponds to the only Why file which is not included by other Why
      --  files, so that we will not redo the same proof more than once. In
      --  particular, subprogram bodies for expression functions, which may be
      --  originally declared in the package spec, should end up here.

      function Concat (A, B : List_Of_Nodes.List) return List_Of_Nodes.List;

      function Concat (A, B : List_Of_Nodes.List) return List_Of_Nodes.List is
         C : List_Of_Nodes.List := A;
      begin
         for N of B loop
            C.Append (N);
         end loop;
         return C;
      end Concat;

      Spec_Unit : Node_Id := Empty;
      Body_Unit : Node_Id := Empty;

   --  Start of processing for Filter_Compilation_Unit

   begin
      case Nkind (Unit (N)) is
         when N_Package_Body =>
            Spec_Unit :=
              Enclosing_Lib_Unit_Node (Corresponding_Spec (Unit (N)));
            Body_Unit := N;

         when N_Package_Declaration         |
              N_Generic_Package_Declaration =>
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

      Types_Vars_Spec.WP_Decls :=
        Concat
          (Decls_In_Spec (Alfa_Type),
           Decls_In_Spec (Alfa_Object));

      Types_Vars_Body.WP_Decls :=
        Concat (Decls_In_Body (Alfa_Type),
                Decls_In_Body (Alfa_Object));

      Subp_Spec.WP_Decls_As_Spec := Decls_In_Spec (Alfa_Subprogram_Spec);

      Subp_Body.WP_Decls_As_Spec := Decls_In_Body (Alfa_Subprogram_Spec);

      Subp_Body.WP_Decls :=
        Concat (Decls_In_Spec (Alfa_Subprogram_Body),
                Decls_In_Body (Alfa_Subprogram_Body));

      --  Take into account dependencies
      --  Add standard package only to types_vars for spec
      Add_With_Clause (Types_Vars_Spec, Standard_Why_Package_Name);
      --  Add "vertical" dependencies for a single package
      Add_With_Clause (Types_Vars_Body, Types_Vars_Spec);
      Add_With_Clause (Subp_Spec, Types_Vars_Body);
      Add_With_Clause (Subp_Body, Subp_Spec);

      --  for each with clause in the package spec, add horizontal
      --  dependencies between spec packages
      if Present (Spec_Unit) then
         declare
            Cursor : Node_Id := First (Context_Items (Spec_Unit));
         begin
            while Present (Cursor) loop
               case Nkind (Cursor) is
                  when N_With_Clause =>
                     if not Implicit_With (Cursor)
                       and then
                         not Is_From_Standard_Library
                           (Sloc (Library_Unit (Cursor)))
                     then
                        declare
                           Pkg_Name : constant String :=
                               File_Name_Without_Suffix
                                 (Sloc (Library_Unit (Cursor)));
                        begin
                           Add_With_Clause
                              (Types_Vars_Spec,
                               Pkg_Name & Types_Vars_Spec_Suffix);
                           Add_With_Clause
                              (Subp_Spec,
                               Pkg_Name & Subp_Spec_Suffix);
                        end;
                     end if;

                  when others =>
                     null;
               end case;
               Next (Cursor);
            end loop;
         end;
      end if;

      --  Add diagonal dependencies for spec -> body dependencies
      if Present (Body_Unit) then
         declare
            Cursor : Node_Id := First (Context_Items (Body_Unit));
         begin
            while Present (Cursor) loop
               case Nkind (Cursor) is
                  when N_With_Clause =>
                     declare
                        Pkg_Name : constant String :=
                                     File_Name_Without_Suffix
                                       (Sloc (Library_Unit (Cursor)));
                     begin
                        if not Implicit_With (Cursor)
                          and then
                            not Is_From_Standard_Library
                              (Sloc (Library_Unit (Cursor)))
                        then
                           Add_With_Clause
                             (Types_Vars_Body,
                              Pkg_Name & Types_Vars_Spec_Suffix);
                           Add_With_Clause
                             (Subp_Spec,
                              Pkg_Name & Types_Vars_Body_Suffix);
                           Add_With_Clause
                             (Subp_Body,
                              Pkg_Name & Subp_Spec_Suffix);
                        end if;
                     end;

                  when others =>
                     null;

               end case;
               Next (Cursor);
            end loop;
         end;
      end if;

      --  If the current package is a child package, add the implicit with
      --  clause from the child spec to the parent spec
      declare
         Def_Unit_Name : Node_Id := Empty;
      begin
         case Nkind (Unit (N)) is
            when N_Package_Declaration =>
               Def_Unit_Name :=
                  Defining_Unit_Name (Specification (Unit (N)));

            when N_Package_Body =>
               Def_Unit_Name := Defining_Unit_Name ((Unit (N)));

            when others =>
               null;
         end case;

         if Present (Def_Unit_Name) and then
            Nkind (Def_Unit_Name) = N_Defining_Program_Unit_Name then
               Add_With_Clause
                  (Types_Vars_Spec,
                   Get_Name_String (Chars (Name (Def_Unit_Name))) &
                     Types_Vars_Spec_Suffix);
         end if;
      end;

      ALFA_Compilation_Units.Append (Types_Vars_Spec);
      ALFA_Compilation_Units.Append (Types_Vars_Body);
      ALFA_Compilation_Units.Append (Subp_Spec);
      ALFA_Compilation_Units.Append (Subp_Body);
   end Filter_Compilation_Unit;

   -----------------------------
   -- Filter_Standard_Package --
   -----------------------------

   function Filter_Standard_Package return List_Of_Nodes.List is
      use List_Of_Nodes;
   begin
      if Is_Empty (Standard_Why_Package) then
         declare
            Decl          : Node_Id :=
               First (Visible_Declarations (
                 Specification (Standard_Package_Node)));
         begin
            while Present (Decl) loop
               case Nkind (Decl) is
                  when N_Full_Type_Declaration
                    | N_Subtype_Declaration =>
                     if Type_Is_In_ALFA (Unique (Defining_Entity (Decl))) then
                        Standard_Why_Package.Append (Decl);
                     end if;

                  when N_Object_Declaration =>
                     if Object_Is_In_ALFA
                       (Unique (Defining_Entity (Decl)))
                     then
                        Standard_Why_Package.Append (Decl);
                     end if;

                  when others =>
                     null;
               end case;

               Next (Decl);
            end loop;

         end;
      end if;

      return Standard_Why_Package;
   end Filter_Standard_Package;

   ----------------------
   -- Traverse_Subtree --
   ----------------------

   procedure Traverse_Subtree
     (N       : Node_Id;
      Process : access procedure (N : Node_Id))
   is
      procedure Traverse_List (L : List_Id);
      --  Traverse through the list of nodes L

      procedure Traverse_List (L : List_Id) is
         Cur : Node_Id;
      begin
         Cur := First (L);
         while Present (Cur) loop
            Traverse_Subtree (Cur, Process);
            Next (Cur);
         end loop;
      end Traverse_List;

   begin
      Process (N);

      case Nkind (N) is
         when N_Package_Declaration =>
            Traverse_List (Visible_Declarations (Specification (N)));
            Traverse_List (Private_Declarations (Specification (N)));

         when N_Package_Body =>
            Traverse_Subtree
              (Parent (Parent (Corresponding_Spec (N))), Process);
            Traverse_List (Declarations (N));

         when others =>
            null;
            --  ??? Later on complete this by raising Program_Error
            --  for unexpected cases.
      end case;
   end Traverse_Subtree;

end ALFA.Filter;
