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

with AA_Util; use AA_Util;
with Atree;   use Atree;
with Einfo;   use Einfo;
with Namet;   use Namet;
with Nlists;  use Nlists;
with Nmake;   use Nmake;
with Sinfo;   use Sinfo;
with Stand;   use Stand;
with Tbuild;  use Tbuild;

package body ALFA.Filter is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Copy_List (L : List_Id) return List_Id;
   --  Copy list L and its underlying elements using New_Copy

   procedure Make_Compilation_Unit_From_Decl
     (Decl    : Node_Id;
      Context : List_Id);
   --  Create a compilation unit for unit Decl and store it in
   --  ALFA_Compilation_Units.

   function Make_Package_Spec_From_Decls
     (Decls : List_Id;
      Name  : String) return Node_Id;
   --  Create a package spec called Name with Decls as visible declarations

   function Node_List_From_List_Of_Nodes (Nlist : List) return List_Id;
   --  Transform a standard list of nodes into a GNAT list

   procedure Traverse_Subtree
     (N       : Node_Id;
      Process : access procedure (N : Node_Id));
   --  Traverse the subtree of N and call Process on selected nodes

   ---------------
   -- Copy_List --
   ---------------

   function Copy_List (L : List_Id) return List_Id is
      Copy : constant List_Id := New_List;
      Cur  : Node_Id := First (L);
   begin
      while Present (Cur) loop
         Append (New_Copy (Cur), Copy);
         Next (Cur);
      end loop;
      return Copy;
   end Copy_List;

   --------------------
   -- Filter_Package --
   --------------------

   procedure Filter_Package (N : Node_Id) is
      Type_List      : List;
      Var_List       : List;
      Subp_Spec_List : List;
      Subp_Def_List  : List;

      procedure Bucket_Dispatch (N : Node_Id);
      --  If the Node belongs to the ALFA language, put it in one of the
      --  corresponding buckets (types, variables, subprograms).
      --  ??? TBD Also, introduce explicit type declarations for anonymous
      --  types.

      procedure Bucket_Dispatch (N : Node_Id)
      is
      begin
         case Nkind (N) is
            when N_Subprogram_Declaration =>
               if Is_In_ALFA (Defining_Unit_Name (Specification (N))) then
                  Subp_Spec_List.Append (N);
               end if;

            when N_Subprogram_Body =>
               if (Acts_As_Spec (N)
                    and then Body_Is_In_ALFA
                      (Defining_Unit_Name (Specification (N))))
                 or else
                   (not Acts_As_Spec (N)
                     and then Body_Is_In_ALFA (Corresponding_Spec (N)))
               then
                  Subp_Def_List.Append (N);
               end if;

            when N_Subtype_Declaration   |
                 N_Full_Type_Declaration =>
               if Is_In_ALFA (Defining_Identifier (N)) then
                  Type_List.Append (N);
               end if;

            when N_Object_Declaration =>
               if Is_In_ALFA (Defining_Identifier (N)) then
                  Var_List.Append (N);
               end if;

            when others =>
               null;

         end case;

      end Bucket_Dispatch;

      Ent_Name     : Name_Id;
      Context_List : constant List_Id := New_List;

   --  Start of processing for Filter_Package

   begin
      if Nkind (N) = N_Package_Body then
         Ent_Name := Chars (Corresponding_Spec (N));
      else
         Ent_Name := Chars (Defining_Unit_Name (Specification (N)));
      end if;

      Traverse_Subtree (N, Bucket_Dispatch'Access);

      declare
         Types_P : Node_Id;
         Vars_P  : Node_Id;
         Subp_P  : Node_Id;
         Defs_P  : Node_Id;

         procedure Add_Package_Decl_To_Context (N : Node_Id);

         procedure Add_Package_Decl_To_Context (N : Node_Id) is
         begin
            Append (Make_With_Clause
                    (No_Location, Defining_Unit_Name (Specification (N))),
                    Context_List);
         end Add_Package_Decl_To_Context;

      begin
         Types_P :=
           Make_Package_Spec_From_Decls
             (Decls => Node_List_From_List_Of_Nodes (Type_List),
              Name  => Name_String (Ent_Name) & "_types");
         Vars_P :=
           Make_Package_Spec_From_Decls
             (Decls => Node_List_From_List_Of_Nodes (Var_List),
              Name  => Name_String (Ent_Name) & "_vars");
         Subp_P :=
           Make_Package_Spec_From_Decls
             (Decls => Node_List_From_List_Of_Nodes (Subp_Spec_List),
              Name  => Name_String (Ent_Name) & "_subp");
         Defs_P :=
           Make_Package_Spec_From_Decls
             (Decls => Node_List_From_List_Of_Nodes (Subp_Def_List),
              Name  => Name_String (Ent_Name));

         Add_Package_Decl_To_Context (Standard_Package_Node);
         Make_Compilation_Unit_From_Decl (Decl    => Types_P,
                                          Context => Copy_List (Context_List));
         Add_Package_Decl_To_Context (Types_P);
         Make_Compilation_Unit_From_Decl (Decl    => Vars_P,
                                          Context => Copy_List (Context_List));
         Add_Package_Decl_To_Context (Vars_P);
         Make_Compilation_Unit_From_Decl (Decl    => Subp_P,
                                          Context => Copy_List (Context_List));
         Add_Package_Decl_To_Context (Subp_P);
         Make_Compilation_Unit_From_Decl (Decl    => Defs_P,
                                          Context => Context_List);
      end;
   end Filter_Package;

   -------------------------------------
   -- Make_Compilation_Unit_From_Decl --
   -------------------------------------

   procedure Make_Compilation_Unit_From_Decl
     (Decl    : Node_Id;
      Context : List_Id) is
   begin
      ALFA_Compilation_Units.Append (
        Make_Compilation_Unit (No_Location,
          Context_Items   => Context,
          Private_Present => False,
          Unit            => Decl,
          Aux_Decls_Node  =>
            Make_Compilation_Unit_Aux (No_Location)));
   end Make_Compilation_Unit_From_Decl;

   ----------------------------------
   -- Make_Package_Spec_From_Decls --
   ----------------------------------

   function Make_Package_Spec_From_Decls
     (Decls : List_Id;
      Name  : String) return Node_Id
   is
      Ent     : Entity_Id;
      End_Lab : Node_Id;

   begin
      Ent :=
        Make_Defining_Identifier (No_Location,
          Chars => New_Name_Id (Name));
      End_Lab := New_Occurrence_Of (Ent, No_Location);

      return
        Make_Package_Declaration (No_Location,
          Specification =>
            Make_Package_Specification (No_Location,
              Defining_Unit_Name   => Ent,
              Visible_Declarations => Decls,
              End_Label            => End_Lab));
   end Make_Package_Spec_From_Decls;

   ----------------------------------
   -- Node_List_From_List_Of_Nodes --
   ----------------------------------

   function Node_List_From_List_Of_Nodes (Nlist : List) return List_Id is
      L : List_Id;

   begin
      L := New_List;
      for N of Nlist loop
         Append (New_Copy (N), L);
      end loop;

      return L;
   end Node_List_From_List_Of_Nodes;

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
