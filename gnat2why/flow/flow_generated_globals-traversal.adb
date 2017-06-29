------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--     F L O W . G E N E R A T E D _ G L O B A L S . T R A V E R S A L      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                 Copyright (C) 2016-2017, Altran UK Limited               --
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

with Ada.Text_IO;
with Nlists;       use Nlists;
with Sem_Util;     use Sem_Util;
with Sinfo;        use Sinfo;
with SPARK_Util;   use SPARK_Util;
with Flow_Utility; use Flow_Utility;

package body Flow_Generated_Globals.Traversal is

   Debug : constant Boolean := False;
   --  Control debug output
   --  ??? rename

   Root : Entity_Id := Empty;

   Constants : Node_Lists.List;
   --  Constants declared in the current compilation unit; needed to decide
   --  wheather they have variable input and so can appear in the generated
   --  Global.

   generic
      with procedure Process (N : Node_Id) is <>;
   procedure Traverse_Compilation_Unit (CU : Node_Id);
   --  Call Process on all declarations within compilation unit CU. Unlike in
   --  standard front end traversal traverses into stubs, but not into generic
   --  units and stops while hitting the SPARK_Mode boundary.
   --
   --  ??? shamelessly stolen from Lib.Xref.SPARK_Specific which does not
   --  respect the SPARK_Mode boundary.

   ----------------
   -- Build_Tree --
   ----------------

   procedure Build_Tree (CU : Node_Id) is

      function Parent_Scope (E : Entity_Id) return Entity_Id
        with Pre  => Ekind (E) in Container_Scope | E_Constant,
             Post => Ekind (Parent_Scope'Result) in Container_Scope;

      procedure Process (N : Node_Id);
      --  Process declaration to build the hierarchical scope structure

      procedure Traverse is new Traverse_Compilation_Unit (Process);

      ------------------
      -- Parent_Scope --
      ------------------

      function Parent_Scope (E : Entity_Id) return Entity_Id is
         P : Entity_Id := Scope (E);
      begin
         while Ekind (P) not in Container_Scope
           or else Is_Wrapper_Package (P)
         loop
            P := Scope (P);
         end loop;

         return P;
      end Parent_Scope;

      -------------
      -- Process --
      -------------

      procedure Process (N : Node_Id) is

         procedure Insert (E : Entity_Id)
         with Pre => Ekind (E) in Container_Scope;

         ------------
         -- Insert --
         ------------

         procedure Insert (E : Entity_Id) is
         begin
            if not Is_Wrapper_Package (E)
              and then not (Ekind (E) = E_Procedure
                              and then Is_Eliminated (E)
                              and then not Comes_From_Source (E))
            then
               declare
                  P : constant Entity_Id := Parent_Scope (E);
               begin
                  if Present (Root) then
                     case Container_Scope (Ekind (E)) is
                        when E_Function | E_Procedure | Entry_Kind =>
                           Scope_Map (P).Subprograms.Append (E);

                        when E_Package | E_Protected_Type | E_Task_Type =>
                           Scope_Map (P).Packages.Append (E);
                     end case;
                  else
                     Root := E;
                  end if;

                  if Debug then
                     Ada.Text_IO.Put_Line
                       (Unique_Name (P) & P'Img &
                          " -> " &
                          Unique_Name (E) & E'Img &
                          " (" & Scope_Map.Length'Img & " )");
                  end if;

                  Scope_Map.Insert (Key      => E,
                                    New_Item => (Packages        => <>,
                                                 Subprograms     => <>,
                                                 Parent          => P));
               end;
            end if;
         end Insert;

      --  Start of processing for Process

      begin
         case Nkind (N) is
            when N_Entry_Declaration          |
                 N_Package_Declaration        |
                 N_Protected_Type_Declaration |
                 N_Subprogram_Declaration     |
                 N_Task_Type_Declaration      =>
               Insert (Defining_Entity (N));

            when N_Subprogram_Body =>
               if Acts_As_Spec (N) then
                  Insert (Defining_Entity (N));
               end if;

            when N_Subprogram_Body_Stub =>
               if No (Corresponding_Spec_Of_Stub (N)) then
                  Insert (Unique_Defining_Entity (N));
               end if;

            when N_Object_Declaration =>
               declare
                  E : constant Entity_Id := Defining_Entity (N);
               begin
                  if Ekind (E) = E_Constant
                    and then E = Unique_Entity (E)
                    and then Has_Variable_Input (E)
                    and then not Is_Part_Of_Concurrent_Object (E)
                    --  ??? the Part_Of probably shouldn't be here
                  then
                     Constants.Append (E);
                  end if;
               end;

            when others =>
               null;

         end case;
      end Process;

   --  Start of processing for Build_Tree

   begin
      Traverse (CU);
   end Build_Tree;

   ---------------
   -- Dump_Tree --
   ---------------

   procedure Dump_Tree is

      procedure Dump (E : Entity_Id);

      ----------
      -- Dump --
      ----------

      procedure Dump (E : Entity_Id) is
      begin
         for Child of Scope_Map (E) loop
            Dump (Child);
         end loop;
         Ada.Text_IO.Put_Line ("***" & Unique_Name (E));
      end Dump;

   --  Start of processing for Dump_Tree

   begin
      if Debug then
         Dump (Root);
      end if;
   end Dump_Tree;

   -------------
   -- Is_Leaf --
   -------------

   function Is_Leaf (E : Entity_Id) return Boolean is
      C : constant Nested_Scopes.Cursor := Scope_Map.Find (E);
   begin
      return Scope_Map (C).Packages.Is_Empty
        and then Scope_Map (C).Subprograms.Is_Empty;
   end Is_Leaf;

   ------------------------------------
   -- Iterate_Constants_In_Main_Unit --
   ------------------------------------

   procedure Iterate_Constants_In_Main_Unit is
   begin
      for E of Constants loop
         Process (E);
      end loop;
   end Iterate_Constants_In_Main_Unit;

   -----------------------
   -- Iterate_Main_Unit --
   -----------------------

   procedure Iterate_Main_Unit
     (Process : not null access procedure (E : Entity_Id))
   is

      procedure Wrapper (E : Entity_Id);

      -------------
      -- Wrapper --
      -------------

      procedure Wrapper (E : Entity_Id) is
      begin
         for Child of Scope_Map (E) loop
            Wrapper (Child);
         end loop;

         Process (E);
      end Wrapper;

   --  Start of processing for Iterate_Main_Unit

   begin
      --  Library-level renamings have no entities; ignore them
      if Present (Root) then
         Wrapper (Root);
      end if;
   end Iterate_Main_Unit;

   ------------------
   -- Parent_Scope --
   ------------------

   function Parent_Scope (E : Entity_Id) return Entity_Id is
     (Scope_Map (E).Parent);

   -----------------
   -- Root_Entity --
   -----------------

   function Root_Entity return Entity_Id is (Root);

   -------------------------------
   -- Traverse_Compilation_Unit --
   -------------------------------

   procedure Traverse_Compilation_Unit (CU : Node_Id)
   is
      procedure Traverse_Block                      (N : Node_Id);
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

      --------------------
      -- Traverse_Block --
      --------------------

      procedure Traverse_Block (N : Node_Id) renames
        Traverse_Declarations_And_HSS;

      ---------------------------------------
      -- Traverse_Declaration_Or_Statement --
      ---------------------------------------

      procedure Traverse_Declaration_Or_Statement (N : Node_Id) is
         function Traverse_Stub (N : Node_Id) return Boolean;
         --  Returns True iff stub N should be traversed

         function Traverse_Stub (N : Node_Id) return Boolean is
         begin
            pragma Assert (Nkind_In (N, N_Package_Body_Stub,
                                        N_Protected_Body_Stub,
                                        N_Subprogram_Body_Stub,
                                        N_Task_Body_Stub));

            return Present (Library_Unit (N));
         end Traverse_Stub;

      --  Start of processing for Traverse_Declaration_Or_Statement

      begin
         case Nkind (N) is
            when N_Package_Declaration =>
               Traverse_Visible_And_Private_Parts (Specification (N));

            when N_Package_Body =>
               Traverse_Package_Body (N);

            when N_Package_Body_Stub =>
               if Traverse_Stub (N) then
                  Traverse_Package_Body (Get_Body_From_Stub (N));
               end if;

            when N_Subprogram_Body =>
               Traverse_Subprogram_Body (N);

            when N_Entry_Body =>
               Traverse_Subprogram_Body (N);

            when N_Subprogram_Body_Stub =>
               if Traverse_Stub (N) then
                  Traverse_Subprogram_Body (Get_Body_From_Stub (N));
               end if;

            when N_Protected_Body =>
               Traverse_Protected_Body (N);

            when N_Protected_Body_Stub =>
               if Traverse_Stub (N) then
                  Traverse_Protected_Body (Get_Body_From_Stub (N));
               end if;

            when N_Protected_Type_Declaration =>
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
               if Traverse_Stub (N) then
                  Traverse_Task_Body (Get_Body_From_Stub (N));
               end if;

            when N_Block_Statement =>
               Traverse_Block (N);

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

               --  Generic declarations are ignored

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
         N : Node_Id;

      begin
         --  Loop through statements or declarations

         N := First (L);
         while Present (N) loop

            --  Call Process on all declarations

            if Nkind (N) in N_Declaration
              or else Nkind (N) in N_Later_Decl_Item
              or else Nkind (N) = N_Entry_Body
            then
               Process (N);
            end if;

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
         Spec_E : constant Entity_Id := Unique_Defining_Entity (N);

      begin
         case Ekind (Spec_E) is
            when E_Package =>
               Traverse_Declarations_Or_Statements (Declarations (N));
               Traverse_Handled_Statement_Sequence
                 (Handled_Statement_Sequence (N));

            when E_Generic_Package =>
               null;

            when others =>
               raise Program_Error;
         end case;
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

      procedure Traverse_Subprogram_Body (N : Node_Id) is
      begin
         case Ekind (Unique_Defining_Entity (N)) is
            when Entry_Kind
               | E_Function
               | E_Procedure
            =>
               Traverse_Declarations_And_HSS (N);

            when Generic_Subprogram_Kind =>
               null;

            when others =>
               raise Program_Error;
         end case;
      end Traverse_Subprogram_Body;

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

      --  Local variables

      Lu : Node_Id;
      --  ??? Library unit

   --  Start of processing for Traverse_Compilation_Unit

   begin
      --  Get Unit (checking case of subunit)

      Lu := Unit (CU);

      if Nkind (Lu) = N_Subunit then
         Lu := Proper_Body (Lu);
      end if;

      --  Do not add scopes for generic units

      if Nkind (Lu) = N_Package_Body
        and then Is_Generic_Unit (Corresponding_Spec (Lu))
      then
         return;
      end if;

      --  Call Process on all declarations

      if Nkind (Lu) in N_Declaration
        or else Nkind (Lu) in N_Later_Decl_Item
      then
         Process (Lu);
      end if;

      --  Traverse the unit

      Traverse_Declaration_Or_Statement (Lu);
   end Traverse_Compilation_Unit;

end Flow_Generated_Globals.Traversal;
