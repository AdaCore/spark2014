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
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Ada.Text_IO;
with Atree;                      use Atree;
with Common_Containers;          use Common_Containers;
with Einfo;                      use Einfo;
with Flow_Refinement;            use Flow_Refinement;
with Gnat2Why_Args;
with Graphs;
with Lib;                        use Lib;
with Namet;                      use Namet;
with Nlists;                     use Nlists;
with Rtsfind;                    use Rtsfind;
with Sem_Util;                   use Sem_Util;
with SPARK_Util;                 use SPARK_Util;
with Sinfo;                      use Sinfo;
with Stand;                      use Stand;

package body Flow_Visibility is

   ----------------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------------

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

   type Edge_Kind is (Rule0, Rule1, Rule2, Rule3, Rule4);

   function Hash (S : Flow_Scope) return Ada.Containers.Hash_Type;

   package Scope_Graphs is new
     Graphs (Vertex_Key   => Flow_Scope,
             Edge_Colours => Edge_Kind,
             Null_Key     => Null_Flow_Scope,
             Key_Hash     => Hash,
             Test_Key     => "=");

   ----------------------------------------------------------------------------
   --  Local variables
   ----------------------------------------------------------------------------

   function Standard_Scope return Flow_Scope is
     (Ent => Standard_Standard, Part => Visible_Part);
   --  ??? this should be a constant, but at the time of elaboration the
   --  Standard_Standard is not yet defined.

   Standard_Info : constant Hierarchy_Info_T :=
     (Is_Package  => True,
      Is_Private  => False,
      Is_Instance => False,
      Is_Nested   => False,
      Parent      => Empty,
      Template    => Empty,
      Container   => Null_Flow_Scope);

   Hierarchy_Info : Hierarchy_Info_Maps.Map;
   Scope_Graph    : Scope_Graphs.Graph := Scope_Graphs.Create;

   Raw_Scope_Graph : Scope_Graphs.Graph;

   ----------------------------------------------------------------------------
   --  Subprogram declarations
   ----------------------------------------------------------------------------

   function Sanitize (S : Flow_Scope) return Flow_Scope is
     (if Present (S) then S else Standard_Scope);
   --  Convert between Null_Flow_Scope (which is used in the Flow_Refinement
   --  package) to Standard_Scope (which is used here).

   function Invariant (Info : Hierarchy_Info_T) return Boolean with Ghost;

   function Make_Info (N : Node_Id) return Hierarchy_Info_T
   with Post => Invariant (Make_Info'Result);

   function Is_Child (Info : Hierarchy_Info_T) return Boolean;

   procedure Print (G : Scope_Graphs.Graph);
   --  Pretty-print visibility graph

   procedure Print_Path (From, To : Flow_Scope);
   pragma Unreferenced (Print_Path);
   --  To be used from the debugger

   ----------------------------------------------------------------------------
   --  Subprogram bodies
   ----------------------------------------------------------------------------

   ----------------------------
   -- Close_Visibility_Graph --
   ----------------------------

   procedure Close_Visibility_Graph is
   begin
      --  Print graph before adding transitive edges
      if Gnat2Why_Args.Flow_Advanced_Debug then
         Print (Scope_Graph);

         --  Retain the original graph for the Print_Path routine

         Raw_Scope_Graph := Scope_Graph;
      end if;

      Scope_Graph.Close;
   end Close_Visibility_Graph;

   ----------
   -- Hash --
   ----------

   function Hash (S : Flow_Scope) return Ada.Containers.Hash_Type is
      use type Ada.Containers.Hash_Type;
   begin
      --  Adding S.Part'Pos, which ranges from 0 to 3, should keep hash values
      --  unique, because S.Ent values of different scopes are not that close
      --  to each other.
      return Node_Hash (S.Ent) + Declarative_Part'Pos (S.Part);
   end Hash;

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
   begin
      --  The visibility graph is not reflexive; we must explicitly check for
      --  visibility between the same scopes.

      return Looking_From = Looking_At
        or else Scope_Graph.Edge_Exists (Sanitize (Looking_From),
                                         Sanitize (Looking_At));
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

      function Is_Text_IO_Special_Package (E : Entity_Id) return Boolean;
      --  Return True iff E is one of the special generic Text_IO packages,
      --  which Ada RM defines to be nested in Ada.Text_IO, but GNAT defines
      --  as its private children.

      --------------------------------
      -- Is_Text_IO_Special_Package --
      --------------------------------

      function Is_Text_IO_Special_Package (E : Entity_Id) return Boolean is
      begin
         --  ??? detection with a scope climbing might be more efficient

         for U in Ada_Text_IO_Child loop
            if Is_RTU (E, U) then
               return True;
            end if;
         end loop;

         for U in Ada_Wide_Text_IO_Child loop
            if Is_RTU (E, U) then
               return True;
            end if;
         end loop;

         for U in Ada_Wide_Wide_Text_IO_Child loop
            if Is_RTU (E, U) then
               return True;
            end if;
         end loop;

         return False;
      end Is_Text_IO_Special_Package;

   --  Start of processing for Make_Info

   begin
      --  Special Text_IO packages behave as nested within the Ada.Text_IO
      --  (that is what Ada RM A.10.1 mandates), but in GNAT they are defined
      --  as private generic children of Ada.Text_IO. We special-case them
      --  according to what the Ada RM says.

      if Ekind (E) in E_Package | E_Generic_Package then
         Is_Package := True;

         if Is_Child_Unit (E) then
            if Is_Text_IO_Special_Package (E) then
               Is_Private := False;
               Parent     := Empty;
            else
               Is_Private := Is_Private_Descendant (E);
               Parent     := Scope (E);
               pragma Assert (Hierarchy_Info.Contains (Parent));
            end if;
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
         pragma Assert (Ekind (E) in E_Protected_Type | E_Task_Type);

         Is_Package  := False;
         Is_Instance := False;
         Is_Private  := False;
         Parent      := Empty;
         Template    := Empty;
      end if;

      if Is_Child_Unit (E)
        and then Is_Text_IO_Special_Package (E)
      then
         Container := (Ent => Scope (E), Part => Visible_Part);
         Is_Nested := True;
      else
         Container := Get_Flow_Scope (N);
         Is_Nested := Container /= Null_Flow_Scope;
      end if;

      return (Is_Package  => Is_Package,
              Is_Private  => Is_Private,
              Is_Instance => Is_Instance,
              Is_Nested   => Is_Nested,
              Parent      => Parent,
              Template    => Template,
              Container   => Container);
   end Make_Info;

   -----------
   -- Print --
   -----------

   procedure Print (G : Scope_Graphs.Graph)
   is
      use Scope_Graphs;

      function NDI (G : Graph; V : Vertex_Id) return Node_Display_Info;
      --  Pretty-printing for vertices in the dot output

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : Edge_Kind) return Edge_Display_Info;
      --  Pretty-printing for edges in the dot output

      ---------
      -- NDI --
      ---------

      function NDI (G : Graph; V : Vertex_Id) return Node_Display_Info
      is
         S : constant Flow_Scope := G.Get_Key (V);

         Label : constant String :=
           Full_Source_Name (S.Ent) &
         (case S.Part is
             when Visible_Part => " (Spec)",
             when Private_Part => " (Priv)",
             when Body_Part    => " (Body)",
             when Null_Part    => raise Program_Error);

      begin
         return (Show        => True,
                 Shape       => Shape_None,
                 Colour      =>
                   To_Unbounded_String
                     (if S = Standard_Scope         then "blue"
                      elsif Is_Generic_Unit (S.Ent) then "red"
                      else ""),
                 Fill_Colour => Null_Unbounded_String,
                 Label       => To_Unbounded_String (Label));
      end NDI;

      ---------
      -- EDI --
      ---------

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : Edge_Kind) return Edge_Display_Info
      is
         pragma Unreferenced (G, A, B, Marked);
      begin
         return
           (Show   => True,
            Shape  => Edge_Normal,
            Colour => Null_Unbounded_String,
            Label  =>
              To_Unbounded_String (Natural'Image (Edge_Kind'Pos (Colour))));
      end EDI;

      Filename : constant String :=
        Get_Name_String (Chars (Main_Unit_Entity)) & "_visibility";

   --  Start of processing for Print

   begin
      G.Write_Pdf_File
        (Filename  => Filename,
         Node_Info => NDI'Access,
         Edge_Info => EDI'Access);
   end Print;

   ----------------
   -- Print_Path --
   ----------------

   procedure Print_Path (From, To : Flow_Scope) is

      Source : constant Scope_Graphs.Vertex_Id :=
        Raw_Scope_Graph.Get_Vertex (Sanitize (From));

      Target : constant Scope_Graphs.Vertex_Id :=
        Raw_Scope_Graph.Get_Vertex (Sanitize (To));

      procedure Is_Target
        (V           : Scope_Graphs.Vertex_Id;
         Instruction : out Scope_Graphs.Traversal_Instruction);

      procedure Print_Vertex (V : Scope_Graphs.Vertex_Id);

      ---------------
      -- Is_Target --
      ---------------

      procedure Is_Target
        (V           : Scope_Graphs.Vertex_Id;
         Instruction : out Scope_Graphs.Traversal_Instruction)
      is
         use type Scope_Graphs.Vertex_Id;
      begin
         Instruction :=
           (if V = Target
            then Scope_Graphs.Found_Destination
            else Scope_Graphs.Continue);
      end Is_Target;

      ------------------
      -- Print_Vertex --
      ------------------

      procedure Print_Vertex (V : Scope_Graphs.Vertex_Id) is
         S : constant Flow_Scope := Raw_Scope_Graph.Get_Key (V);
      begin
         --  Print_Flow_Scope (S);
         --  ??? the above code produces no output in gdb; use Ada.Text_IO

         if Present (S.Ent) then
            Ada.Text_IO.Put_Line
              (Full_Source_Name (S.Ent) &
                 " | " &
               (case Declarative_Part'(S.Part) is
                     when Visible_Part => "spec",
                     when Private_Part => "priv",
                     when Body_Part    => "body"));
         else
            Ada.Text_IO.Put_Line ("standard");
         end if;
      end Print_Vertex;

   --  Start of processing for Print_Path

   begin
      Scope_Graphs.Shortest_Path
        (G             => Raw_Scope_Graph,
         Start         => Source,
         Allow_Trivial => True,
         Search        => Is_Target'Access,
         Step          => Print_Vertex'Access);
   end Print_Path;

   --------------------------
   -- Register_Flow_Scopes --
   --------------------------

   procedure Register_Flow_Scopes (Unit_Node : Node_Id) is
      procedure Processx (N : Node_Id)
        with Pre => Nkind (N) in N_Generic_Package_Declaration
                               | N_Package_Declaration
                               | N_Protected_Type_Declaration
                               | N_Task_Type_Declaration;
      --  ??? remove the "x" suffix once debugging is done

      -------------
      -- Process --
      -------------

      procedure Processx (N : Node_Id) is
         E : constant Entity_Id := Defining_Entity (N);

         Info : constant Hierarchy_Info_T := Make_Info (N);

         Spec_V, Priv_V, Body_V : Scope_Graphs.Vertex_Id;
         --  Vertices for the visible (aka. "spec"), private and body parts

         Rule : Edge_Kind;
         --  Rule that causes an edge to be added; maintaining it as a global
         --  variable is not elegant, but results in a cleaner code.

         procedure Connect (Source, Target : Scope_Graphs.Vertex_Id);
         --  Add edge from Source to Target

         -------------
         -- Connect --
         -------------

         procedure Connect (Source, Target : Scope_Graphs.Vertex_Id) is
         begin
            Scope_Graph.Add_Edge (Source, Target, Rule);
         end Connect;

      --  Start of processing for Processx

      begin
         --  ??? we don't need this info (except for debug?)

         Hierarchy_Info.Insert (E, Info);

         --  Create vertices

         Scope_Graph.Add_Vertex ((Ent => E, Part => Visible_Part), Spec_V);

         if Info.Is_Package then
            Scope_Graph.Add_Vertex ((Ent => E, Part => Private_Part), Priv_V);
         end if;

         Scope_Graph.Add_Vertex ((Ent => E, Part => Body_Part), Body_V);

         --  Create edges

         --  Rule 0
         Rule := Rule0;

         if Info.Is_Package then
            Connect (Body_V, Priv_V);
            Connect (Priv_V, Spec_V);
         else
            Connect (Body_V, Spec_V);
         end if;

         --  Rule 1
         Rule := Rule1;

         if Info.Is_Instance then
            Connect
              (Spec_V,
               Scope_Graph.Get_Vertex ((Ent  => Info.Template,
                                        Part => Visible_Part)));

         elsif Info.Is_Nested then
            Connect
              (Spec_V,
               Scope_Graph.Get_Vertex (Info.Container));

         elsif Info.Is_Private then
            Connect
              (Spec_V,
               Scope_Graph.Get_Vertex ((Ent  => Info.Parent,
                                        Part => Private_Part)));

         else
            Connect
              (Spec_V,
               Scope_Graph.Get_Vertex ((Ent  => Info.Parent,
                                        Part => Visible_Part)));
         end if;

         --  Rule 2
         Rule := Rule2;

         if Info.Is_Nested then
            Connect
              (Scope_Graph.Get_Vertex (Info.Container),
               Spec_V);
         elsif Info.Is_Private then
            Connect
              (Scope_Graph.Get_Vertex ((Ent  => Info.Parent,
                                        Part => Private_Part)),
               Spec_V);
         else
            Connect
              (Scope_Graph.Get_Vertex ((Ent  => Info.Parent,
                                        Part => Visible_Part)),
               Spec_V);
         end if;

         --  Rule 3
         Rule := Rule3;

         if Info.Is_Package then
            if Info.Is_Instance then
               Connect
                 (Priv_V,
                  Scope_Graph.Get_Vertex ((Ent  => Info.Template,
                                           Part => Private_Part)));
            elsif Is_Child (Info) then
               Connect
                 (Priv_V,
                  Scope_Graph.Get_Vertex ((Ent  => Info.Parent,
                                           Part => Private_Part)));
            end if;
         end if;

         --  Rule 4
         Rule := Rule4;

         if Info.Is_Instance then
            Connect
              (Body_V,
               Scope_Graph.Get_Vertex ((Ent  => Info.Template,
                                        Part => Body_Part)));
         elsif Info.Is_Nested then
            Connect
              (Body_V,
               Scope_Graph.Get_Vertex ((Ent  => Info.Container.Ent,
                                        Part => Body_Part)));
         end if;
      end Processx;

      procedure Traverse is new Traverse_Compilation_Unit (Processx);

   --  Start of processing for Build_Graph

   begin
      if Unit_Node = Standard_Package_Node then
         Hierarchy_Info.Insert (Standard_Standard, Standard_Info);

         Scope_Graph.Add_Vertex (Standard_Scope);
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

               Process (N);

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
