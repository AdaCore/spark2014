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
with Lib.Xref;
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

   -----------------------------
   -- Filter_Compilation_Unit --
   -----------------------------

   procedure Filter_Compilation_Unit (N : Node_Id) is
      Types_Vars_Spec_List : List;
      Types_Vars_Body_List : List;
      Subp_Spec_List       : List;
      Subp_Body_List       : List;

      procedure Bucket_Dispatch
         (N         : Node_Id;
         Types_Vars : in out List;
         Subp       : in out List);
      --  If the Node belongs to the ALFA language, put it in one of the
      --  corresponding buckets (types or variables, subprograms) in argument.
      --  Also, introduce explicit type declarations for anonymous types.

      procedure Dispatch_Spec (N : Node_Id);
      --  Dispatch types, vars, subprogram decls to the corresponding buckets
      --  for specifications.

      procedure Dispatch_Body (N : Node_Id);
      --  Dispatch types, vars, subprograms to the corresponding buckets
      --  for bodies.

      procedure Transform_Subtype_Indication
         (N         : Node_Id;
          Type_List : in out List);
      --  Generate a type definition that corresponds to the given subtype
      --  indication.

      ---------------------
      -- Bucket_Dispatch --
      ---------------------

      procedure Bucket_Dispatch
         (N         : Node_Id;
         Types_Vars : in out List;
         Subp       : in out List)
      is
      begin
         case Nkind (N) is
            when N_Subprogram_Declaration =>
               if Is_In_ALFA (Defining_Unit_Name (Specification (N))) then
                  Subp.Append (N);
               end if;

            when N_Subprogram_Body =>
               if (Acts_As_Spec (N)
                    and then Body_Is_In_ALFA
                      (Defining_Unit_Name (Specification (N))))
                 or else
                   (not Acts_As_Spec (N)
                     and then Body_Is_In_ALFA (Corresponding_Spec (N)))
               then
                  Subp.Append (N);
               end if;

            when N_Full_Type_Declaration =>
               if Is_In_ALFA (Defining_Identifier (N)) then
                  declare
                     Def : constant Node_Id := Type_Definition (N);
                  begin
                  --  We need to check for anonymous types and subtypes here
                     case Nkind (Def) is
                        when N_Unconstrained_Array_Definition =>
                           --  only check for the component type
                           Transform_Subtype_Indication
                             (Subtype_Indication (Component_Definition (Def)),
                              Types_Vars);
                        when N_Constrained_Array_Definition =>
                           declare
                              Cur_Indexed : Node_Id :=
                                 First (Discrete_Subtype_Definitions (Def));
                           begin
                              while Nkind (Cur_Indexed) /= N_Empty loop
                                 Transform_Subtype_Indication
                                    (Cur_Indexed,
                                     Types_Vars);
                                 Next (Cur_Indexed);
                              end loop;
                              Transform_Subtype_Indication
                                (Subtype_Indication
                                   (Component_Definition (Def)),
                                    Types_Vars);
                           end;
                        when others =>
                           null;
                     end case;
                  end;
                  Types_Vars.Append (N);
               end if;

            when N_Subtype_Declaration =>
               if Is_In_ALFA (Defining_Identifier (N)) then
                  Types_Vars.Append (N);
               end if;

            when N_Object_Declaration =>
               --  Local variables introduced by the compiler should remain
               --  local.

               if (Comes_From_Source (Original_Node (N))
                   or else Nkind_In (Parent (N), N_Package_Specification,
                                     N_Package_Body))
                 and then Is_In_ALFA (Defining_Identifier (N))
               then
                  Types_Vars.Append (N);
               end if;

            when others =>
               null;

         end case;

      end Bucket_Dispatch;

      ----------------------------------
      -- Transform_Subtype_Indication --
      ----------------------------------

      procedure Transform_Subtype_Indication
         (N         : Node_Id;
          Type_List : in out List)
      is
         Orig : constant Node_Id := Original_Node (N);
      begin
         --  If the node has been rewritten, and the original node
         --  is an ident, do nothing
         if  Orig /= N and then Nkind (Orig) = N_Identifier then
            null;
         else
            case Nkind (N) is
               when N_Identifier =>
                  --  The type is already a simple name, do nothing
                  null;
               when N_Subtype_Indication | N_Range =>
                  declare
                     --  assume an integer subtype for now
                     --  Rng     : constant Node_Id :=
                     --     Range_Expression (Constraint (N));
                     --  New_Def : constant Node_Id :=
                     --     Make_Signed_Integer_Type_Definition
                     --       (Sloc => Sloc (N),
                     --        Low_Bound => Low_Bound (Rng),
                     --        High_Bound => Low_Bound (Rng));
                  begin
                     Type_List.Append
                       (Make_Subtype_Declaration
                          (Sloc (N),
                           New_Copy (Etype (N)),
                           False,
                           New_Copy (N)));
                  end;
               when others =>
                  null;
            end case;
         end if;
      end Transform_Subtype_Indication;

      Ent_Name     : Name_Id;
      Spec_Unit    : Node_Id := Empty;

      -------------------
      -- Dispatch_Spec --
      -------------------

      procedure Dispatch_Spec (N : Node_Id) is
      begin
         Bucket_Dispatch (N, Types_Vars_Spec_List, Subp_Spec_List);
      end Dispatch_Spec;

      -------------------
      -- Dispatch_Body --
      -------------------

      procedure Dispatch_Body (N : Node_Id) is
      begin
         Bucket_Dispatch (N, Types_Vars_Body_List, Subp_Body_List);
      end Dispatch_Body;

   --  Start of processing for Filter_Compilation_Unit

   begin
      if Nkind (Unit (N)) = N_Package_Body then
         Ent_Name  := Chars (Corresponding_Spec (Unit (N)));
         Spec_Unit := Parent (Parent (Parent (Corresponding_Spec (Unit (N)))));
      else
         Ent_Name := Chars (Defining_Unit_Name (Specification (Unit (N))));
      end if;

      if Present (Spec_Unit) then
         Lib.Xref.ALFA.Traverse_Compilation_Unit
           (Spec_Unit, Dispatch_Spec'Unrestricted_Access);
      end if;

      Lib.Xref.ALFA.Traverse_Compilation_Unit
        (N, Dispatch_Body'Unrestricted_Access);

      declare
         Types_Vars_Spec_P       : Node_Id;
         Types_Vars_Body_P       : Node_Id;
         Subp_Spec_P             : Node_Id;
         Subp_Body_P             : Node_Id;
         Context_Types_Vars_Spec : constant List_Id := New_List;
         Context_Types_Vars_Body : constant List_Id := New_List;
         Context_Subp_Spec       : constant List_Id := New_List;
         Context_Subp_Body       : constant List_Id := New_List;
         Types_Vars_Spec_Suffix  : constant String := "__types_vars_spec";
         Types_Vars_Body_Suffix  : constant String := "__types_vars_body";
         Subp_Spec_Suffix        : constant String := "__subp_spec";

         procedure Add_Package_Decl (L : List_Id; N : Node_Id);
         procedure Add_Package_Decl (L : List_Id; Name : String);

         ----------------------
         -- Add_Package_Decl --
         ----------------------

         procedure Add_Package_Decl (L : List_Id; N : Node_Id)
         is
         begin
            Append (Make_With_Clause
                    (No_Location, Defining_Unit_Name (Specification (N))),
                    L);
         end Add_Package_Decl;

         procedure Add_Package_Decl (L : List_Id; Name : String)
         is
         begin
            Append (
               Make_With_Clause
                  (No_Location,
                   Make_Identifier (No_Location, New_Name_Id (Name))),
               L);
         end Add_Package_Decl;

      begin
         Types_Vars_Spec_P :=
           Make_Package_Spec_From_Decls
             (Decls => Node_List_From_List_Of_Nodes (Types_Vars_Spec_List),
              Name  => Name_String (Ent_Name) & Types_Vars_Spec_Suffix);
         Types_Vars_Body_P :=
           Make_Package_Spec_From_Decls
             (Decls => Node_List_From_List_Of_Nodes (Types_Vars_Body_List),
              Name  => Name_String (Ent_Name) & Types_Vars_Body_Suffix);
         Subp_Spec_P :=
           Make_Package_Spec_From_Decls
             (Decls => Node_List_From_List_Of_Nodes (Subp_Spec_List),
              Name  => Name_String (Ent_Name) & Subp_Spec_Suffix);
         Subp_Body_P :=
           Make_Package_Spec_From_Decls
             (Decls => Node_List_From_List_Of_Nodes (Subp_Body_List),
              Name  => Name_String (Ent_Name));

         --  Take into account dependencies
         --  Add standard package only to types_vars for spec
         Add_Package_Decl (Context_Types_Vars_Spec, Standard_Package_Node);
         --  Add "vertical" dependencies for a single package
         Add_Package_Decl (Context_Types_Vars_Body, Types_Vars_Spec_P);
         Add_Package_Decl (Context_Subp_Spec, Types_Vars_Body_P);
         Add_Package_Decl (Context_Subp_Body, Subp_Spec_P);

         --  for each with clause in the package spec, add horizontal
         --  dependencies between spec packages
         if Present (Spec_Unit) then
            declare
               Cursor : Node_Id := First (Context_Items (Spec_Unit));
            begin
               while Present (Cursor) loop
                  declare
                     Pkg_Name : constant Name_Id := Chars (Name (Cursor));
                  begin
                     if not Implicit_With (Cursor) then
                        Add_Package_Decl
                          (Context_Types_Vars_Spec,
                           Name_String (Pkg_Name) & Types_Vars_Spec_Suffix);
                        Add_Package_Decl
                          (Context_Subp_Spec,
                           Name_String (Pkg_Name) & Subp_Spec_Suffix);
                     end if;
                     Next (Cursor);
                  end;
               end loop;
            end;
         end if;

         --  Add diagonal dependencies for spec -> body dependencies
         declare
            Cursor : Node_Id := First (Context_Items (N));
         begin
            while Present (Cursor) loop
               declare
                  Pkg_Name : constant Name_Id := Chars (Name (Cursor));
               begin
                  if not Implicit_With (Cursor) then
                     Add_Package_Decl
                       (Context_Types_Vars_Body,
                        Name_String (Pkg_Name) & Types_Vars_Spec_Suffix);
                     Add_Package_Decl
                       (Context_Subp_Spec,
                        Name_String (Pkg_Name) & Types_Vars_Body_Suffix);
                     Add_Package_Decl
                       (Context_Subp_Body,
                        Name_String (Pkg_Name) & Subp_Spec_Suffix);
                  end if;
                  Next (Cursor);
               end;
            end loop;
         end;

         Make_Compilation_Unit_From_Decl (Decl    => Types_Vars_Spec_P,
                                          Context => Context_Types_Vars_Spec);
         Make_Compilation_Unit_From_Decl (Decl    => Types_Vars_Body_P,
                                          Context => Context_Types_Vars_Body);
         Make_Compilation_Unit_From_Decl (Decl    => Subp_Spec_P,
                                          Context => Context_Subp_Spec);
         Make_Compilation_Unit_From_Decl (Decl    => Subp_Body_P,
                                          Context => Context_Subp_Body);
      end;
   end Filter_Compilation_Unit;

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
