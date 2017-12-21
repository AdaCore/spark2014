------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W _ V I S I B I L I T Y                        --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--                   Copyright (C) 2018, Altran UK Limited                  --
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
------------------------------------------------------------------------------

with Ada.Containers.Hashed_Maps;
with Atree;                      use Atree;
with Common_Containers;          use Common_Containers;
with Einfo;                      use Einfo;
with Flow_Refinement;            use Flow_Refinement;
with Nlists;                     use Nlists;
with Sem_Util;                   use Sem_Util;
with Sinfo;                      use Sinfo;
with Stand;                      use Stand;

package body Flow_Visibility is

   type Hierarchy_Info_T is record
      Is_Package  : Boolean;
      Is_Private  : Boolean;
      Is_Instance : Boolean;
      Is_Nested   : Boolean;
      Parent      : Entity_Id;
      Template    : Entity_Id;
      Container   : Flow_Scope;
   end record;

   package Hierarchy_Info_Maps is new
     Ada.Containers.Hashed_Maps (Key_Type        => Entity_Id,
                                 Element_Type    => Hierarchy_Info_T,
                                 Hash            => Node_Hash,
                                 Equivalent_Keys => "=",
                                 "="             => "=");

   Hierarchy_Info : Hierarchy_Info_Maps.Map;

   Standard_Scope : constant Hierarchy_Info_T :=
     (Is_Package  => True,
      Is_Private  => False,
      Is_Instance => False,
      Is_Nested   => False,
      Parent      => Empty,
      Template    => Empty,
      Container   => Null_Flow_Scope);

   function Invariant (Info : Hierarchy_Info_T) return Boolean with Ghost;

   function Make_Info (N : Node_Id) return Hierarchy_Info_T
   with Post => Invariant (Make_Info'Result);

   function Is_Child (Info : Hierarchy_Info_T) return Boolean;
   pragma Unreferenced (Is_Child);

   generic
      with procedure Process (N : Node_Id);
   procedure Traverse_Compilation_Unit (Unit_Node : Node_Id);
   --  Call Process on all declarations within compilation unit CU. Unlike the
   --  standard frontend traversal, this one traverses into stubs; unlike the
   --  generated globals traversal, this one traverses into generic units.

   --------------
   -- Is_Child --
   --------------

   function Is_Child (Info : Hierarchy_Info_T) return Boolean is
   begin
      return not Info.Is_Private
        and then not Info.Is_Nested
        and then Present (Info.Parent)
        and then Info.Parent /= Standard_Standard;
   end Is_Child;

   ---------------
   -- Invariant --
   ---------------

   function Invariant (Info : Hierarchy_Info_T) return Boolean is
   begin
      return
       (if not Info.Is_Package then not Info.Is_Private)
        and then
       (if Info.Is_Private then not Info.Is_Nested)
        and then
       (if Info.Is_Nested then
          not Info.Is_Private
          and then No (Info.Parent)
          and then Info.Container /= Null_Flow_Scope
        else
          Present (Info.Parent)
          and then Info.Container = Null_Flow_Scope);
   end Invariant;

   ----------------
   -- Is_Visible --
   ----------------

   function Is_Visible
     (Looking_From : Flow_Scope;
      Looking_At   : Flow_Scope)
      return Boolean
   is
      pragma Unreferenced (Looking_From);
      pragma Unreferenced (Looking_At);
   begin
      return False;
   end Is_Visible;

   ---------------
   -- Make_Info --
   ---------------

   function Make_Info (N : Node_Id) return Hierarchy_Info_T is

      E : constant Entity_Id := Defining_Entity (N);

      Is_Package  : Boolean;
      Is_Private  : Boolean;
      Parent      : Entity_Id;

      Is_Instance : Boolean;
      Template    : Entity_Id;

      Is_Nested   : Boolean;
      Container   : Flow_Scope;

   begin
      if Ekind (E) in E_Package | E_Generic_Package then
         Is_Package := True;

         if Is_Child_Unit (E) and then Is_Private_Descendant (E) then
            Is_Private := True;
            Parent     := Scope (E);
            pragma Assert (Hierarchy_Info.Contains (Parent));
         elsif Get_Flow_Scope (N) = Null_Flow_Scope then
            Is_Private := False;
            Parent     := Standard_Standard;
         else
            Is_Private := False;
            Parent     := Empty;
         end if;

         if Is_Generic_Instance (E) then
            Is_Instance := True;
            Template    := Generic_Parent (Specification (N));
            pragma Assert (Hierarchy_Info.Contains (Template));
         else
            Is_Instance := False;
            Template    := Empty;
         end if;

      else
         pragma Assert (Ekind (E) = E_Protected_Type);

         Is_Package  := False;
         Is_Instance := False;
         Is_Private  := False;
         Parent      := Empty;
         Template    := Empty;
      end if;

      Container := Get_Flow_Scope (N);
      Is_Nested := Container /= Null_Flow_Scope;

      return (Is_Package  => Is_Package,
              Is_Private  => Is_Private,
              Is_Instance => Is_Instance,
              Is_Nested   => Is_Nested,
              Parent      => Parent,
              Template    => Template,
              Container   => Container);
   end Make_Info;

   --------------------------
   -- Register_Flow_Scopes --
   --------------------------

   procedure Register_Flow_Scopes (Unit_Node : Node_Id) is
      procedure Processx (N : Node_Id)
        with Pre => Nkind (N) in N_Generic_Package_Declaration
                               | N_Package_Declaration
                               | N_Protected_Type_Declaration;

      -------------
      -- Process --
      -------------

      procedure Processx (N : Node_Id) is
      begin
         Hierarchy_Info.Insert (Defining_Entity (N), Make_Info (N));
      end Processx;

      procedure Traverse is new Traverse_Compilation_Unit (Processx);

   --  Start of processing for Build_Graph

   begin
      if Unit_Node = Standard_Package_Node then
         Hierarchy_Info.Insert (Standard_Standard, Standard_Scope);
      else
         Traverse (Unit_Node);
      end if;
   end Register_Flow_Scopes;

   -------------------------------
   -- Traverse_Compilation_Unit --
   -------------------------------

   procedure Traverse_Compilation_Unit (Unit_Node : Node_Id)
   is
      procedure Traverse_Declaration_Or_Statement   (N : Node_Id);
      procedure Traverse_Declarations_And_HSS       (N : Node_Id);
      procedure Traverse_Declarations_Or_Statements (L : List_Id);
      procedure Traverse_Handled_Statement_Sequence (N : Node_Id);
      procedure Traverse_Package_Body               (N : Node_Id);
      procedure Traverse_Visible_And_Private_Parts  (N : Node_Id);
      procedure Traverse_Protected_Body             (N : Node_Id);
      procedure Traverse_Subprogram_Body            (N : Node_Id);
      procedure Traverse_Task_Body                  (N : Node_Id);

      --  Traverse corresponding construct, calling Process on all declarations

      ---------------------------------------
      -- Traverse_Declaration_Or_Statement --
      ---------------------------------------

      procedure Traverse_Declaration_Or_Statement (N : Node_Id) is
      begin
         --  Call Process on all interesting declarations and traverse

         case Nkind (N) is
            when N_Package_Declaration
               | N_Generic_Package_Declaration
            =>
               Process (N);
               Traverse_Visible_And_Private_Parts (Specification (N));

            when N_Package_Body =>
               Traverse_Package_Body (N);

            when N_Package_Body_Stub =>
               Traverse_Package_Body (Get_Body_From_Stub (N));

            when N_Subprogram_Body =>
               Traverse_Subprogram_Body (N);

            when N_Entry_Body =>
               Traverse_Subprogram_Body (N);

            when N_Subprogram_Body_Stub =>
               Traverse_Subprogram_Body (Get_Body_From_Stub (N));

            when N_Protected_Body =>
               Traverse_Protected_Body (N);

            when N_Protected_Body_Stub =>
               Traverse_Protected_Body (Get_Body_From_Stub (N));

            when N_Protected_Type_Declaration =>
               Process (N);
               Traverse_Visible_And_Private_Parts (Protected_Definition (N));

            when N_Task_Type_Declaration =>

               --  Task type definition is optional (unlike protected type
               --  definition, which is mandatory).

               declare
                  Task_Def : constant Node_Id := Task_Definition (N);

               begin
                  if Present (Task_Def) then
                     Traverse_Visible_And_Private_Parts (Task_Def);
                  end if;
               end;

            when N_Task_Body =>
               Traverse_Task_Body (N);

            when N_Task_Body_Stub =>
               Traverse_Task_Body (Get_Body_From_Stub (N));

            when N_Block_Statement =>
               Traverse_Declarations_And_HSS (N);

            when N_If_Statement =>

               --  Traverse the statements in the THEN part

               Traverse_Declarations_Or_Statements (Then_Statements (N));

               --  Loop through ELSIF parts if present

               if Present (Elsif_Parts (N)) then
                  declare
                     Elif : Node_Id := First (Elsif_Parts (N));

                  begin
                     while Present (Elif) loop
                        Traverse_Declarations_Or_Statements
                          (Then_Statements (Elif));
                        Next (Elif);
                     end loop;
                  end;
               end if;

               --  Finally traverse the ELSE statements if present

               Traverse_Declarations_Or_Statements (Else_Statements (N));

            when N_Case_Statement =>

               --  Process case branches

               declare
                  Alt : Node_Id := First (Alternatives (N));

               begin
                  loop
                     Traverse_Declarations_Or_Statements (Statements (Alt));
                     Next (Alt);
                     exit when No (Alt);
                  end loop;
               end;

            when N_Extended_Return_Statement =>
               Traverse_Handled_Statement_Sequence
                 (Handled_Statement_Sequence (N));

            when N_Loop_Statement =>
               Traverse_Declarations_Or_Statements (Statements (N));

            --  ??? Generic declarations are NOT ignored

            when others =>
               null;
         end case;
      end Traverse_Declaration_Or_Statement;

      -----------------------------------
      -- Traverse_Declarations_And_HSS --
      -----------------------------------

      procedure Traverse_Declarations_And_HSS (N : Node_Id) is
      begin
         Traverse_Declarations_Or_Statements (Declarations (N));
         Traverse_Handled_Statement_Sequence (Handled_Statement_Sequence (N));
      end Traverse_Declarations_And_HSS;

      -----------------------------------------
      -- Traverse_Declarations_Or_Statements --
      -----------------------------------------

      procedure Traverse_Declarations_Or_Statements (L : List_Id) is
         N : Node_Id := First (L);

      begin
         --  Loop through statements or declarations

         while Present (N) loop
            Traverse_Declaration_Or_Statement (N);
            Next (N);
         end loop;
      end Traverse_Declarations_Or_Statements;

      -----------------------------------------
      -- Traverse_Handled_Statement_Sequence --
      -----------------------------------------

      procedure Traverse_Handled_Statement_Sequence (N : Node_Id) is
         Handler : Node_Id;

      begin
         if Present (N) then
            Traverse_Declarations_Or_Statements (Statements (N));

            if Present (Exception_Handlers (N)) then
               Handler := First (Exception_Handlers (N));
               while Present (Handler) loop
                  Traverse_Declarations_Or_Statements (Statements (Handler));
                  Next (Handler);
               end loop;
            end if;
         end if;
      end Traverse_Handled_Statement_Sequence;

      ---------------------------
      -- Traverse_Package_Body --
      ---------------------------

      procedure Traverse_Package_Body (N : Node_Id) is
      begin
         Traverse_Declarations_Or_Statements (Declarations (N));
         Traverse_Handled_Statement_Sequence (Handled_Statement_Sequence (N));
      end Traverse_Package_Body;

      -----------------------------
      -- Traverse_Protected_Body --
      -----------------------------

      procedure Traverse_Protected_Body (N : Node_Id) is
      begin
         Traverse_Declarations_Or_Statements (Declarations (N));
      end Traverse_Protected_Body;

      ------------------------------
      -- Traverse_Subprogram_Body --
      ------------------------------

      procedure Traverse_Subprogram_Body (N : Node_Id) renames
         Traverse_Declarations_And_HSS;

      ------------------------
      -- Traverse_Task_Body --
      ------------------------

      procedure Traverse_Task_Body (N : Node_Id) renames
         Traverse_Declarations_And_HSS;

      ----------------------------------------
      -- Traverse_Visible_And_Private_Parts --
      ----------------------------------------

      procedure Traverse_Visible_And_Private_Parts (N : Node_Id) is
      begin
         Traverse_Declarations_Or_Statements (Visible_Declarations (N));
         Traverse_Declarations_Or_Statements (Private_Declarations (N));
      end Traverse_Visible_And_Private_Parts;

   --  Start of processing for Traverse_Compilation_Unit

   begin
      Traverse_Declaration_Or_Statement (Unit_Node);
   end Traverse_Compilation_Unit;

end Flow_Visibility;
