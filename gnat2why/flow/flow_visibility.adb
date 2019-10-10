------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W _ V I S I B I L I T Y                        --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--                Copyright (C) 2018-2019, Altran UK Limited                --
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
with Common_Containers;          use Common_Containers;
with Einfo;                      use Einfo;
with Flow_Refinement;            use Flow_Refinement;
with Graphs;
with Nlists;                     use Nlists;
with Rtsfind;                    use Rtsfind;
with Sem_Aux;                    use Sem_Aux;
with Sem_Ch12;                   use Sem_Ch12;
with Sem_Util;                   use Sem_Util;
with SPARK_Util;                 use SPARK_Util;
with Sinfo;                      use Sinfo;
with Stand;                      use Stand;

package body Flow_Visibility is

   ----------------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------------

   package Hierarchy_Info_Maps is new
     Ada.Containers.Hashed_Maps (Key_Type        => Entity_Id,
                                 Element_Type    => Hierarchy_Info_T,
                                 Hash            => Node_Hash,
                                 Equivalent_Keys => "=",
                                 "="             => "=");

   type Edge_Kind is (Rule_Own,
                      Rule_Instance,
                      Rule_Up_Spec,
                      Rule_Down_Spec,
                      Rule_Up_Priv,
                      Rule_Up_Body);

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

   Hierarchy_Info : Hierarchy_Info_Maps.Map;
   Scope_Graph    : Scope_Graphs.Graph := Scope_Graphs.Create;

   Components : Scope_Graphs.Strongly_Connected_Components;
   --  Pre-computed strongly connected components of the visibility graph for
   --  quickly answering visibility queries.

   ----------------------------------------------------------------------------
   --  Subprogram declarations
   ----------------------------------------------------------------------------

   function Sanitize (S : Flow_Scope) return Flow_Scope is
     (if Present (S) then S else Standard_Scope);
   --  Convert between Null_Flow_Scope (which is used in the Flow_Refinement
   --  package) to Standard_Scope (which is used here).

   function Make_Info (N : Node_Id) return Hierarchy_Info_T;

   function Is_Child          (Info : Hierarchy_Info_T) return Boolean;
   function Is_Nested         (Info : Hierarchy_Info_T) return Boolean;
   function Is_Instance       (Info : Hierarchy_Info_T) return Boolean;
   function Is_Instance_Child (Info : Hierarchy_Info_T) return Boolean;
   --  Utility routines for the hierarchy data

   procedure Print (G : Scope_Graphs.Graph);
   --  Pretty-print visibility graph

   procedure Print_Path (From, To : Flow_Scope);
   pragma Unreferenced (Print_Path);
   --  To be used from the debugger

   generic
      with procedure Process (N : Node_Id);
   procedure Traverse_Compilation_Unit (Unit_Node : Node_Id);
   --  Call Process on all declarations within compilation unit CU. Unlike the
   --  standard frontend traversal, this one traverses into stubs; ??? it is
   --  now similar to the generated globals traversal.

   ----------------------------------------------------------------------------
   --  Subprogram bodies
   ----------------------------------------------------------------------------

   -------------------------
   -- Connect_Flow_Scopes --
   -------------------------

   procedure Connect_Flow_Scopes is

      procedure Connect (E : Entity_Id; Info : Hierarchy_Info_T);

      -------------
      -- Connect --
      -------------

      procedure Connect (E : Entity_Id; Info : Hierarchy_Info_T) is

         Spec_V : constant Scope_Graphs.Vertex_Id :=
           Scope_Graph.Get_Vertex ((Ent => E, Part => Visible_Part));

         Priv_V : constant Scope_Graphs.Vertex_Id :=
           (if Info.Is_Package
            then Scope_Graph.Get_Vertex ((Ent => E, Part => Private_Part))
            else Scope_Graphs.Null_Vertex);

         Body_V : constant Scope_Graphs.Vertex_Id :=
           Scope_Graph.Get_Vertex ((Ent => E, Part => Body_Part));
         --  Vertices for the visible (aka. "spec"), private and body parts

         Rule : Edge_Kind;
         --  Rule that causes an edge to be added; maintaining it as a global
         --  variable is not elegant, but results in a cleaner code.

         use type Scope_Graphs.Vertex_Id;

         procedure Connect (Source, Target : Scope_Graphs.Vertex_Id)
         with Pre => Source /= Scope_Graphs.Null_Vertex
                       and
                     Target /= Scope_Graphs.Null_Vertex
                       and
                     Source /= Target;
         --  Add edge from Source to Target

         -------------
         -- Connect --
         -------------

         procedure Connect (Source, Target : Scope_Graphs.Vertex_Id) is
         begin
            pragma Assert (not Scope_Graph.Edge_Exists (Source, Target));
            Scope_Graph.Add_Edge (Source, Target, Rule);
         end Connect;

      --  Start of processing for Connect

      begin
         ----------------------------------------------------------------------
         --  Create edges
         ----------------------------------------------------------------------

         Rule := Rule_Own;

         --  This rule is the "my own scope" rule, and is the most obvious form
         --  of visibility.

         if Info.Is_Package then
            Connect (Body_V, Priv_V);
            Connect (Priv_V, Spec_V);
         else
            Connect (Body_V, Spec_V);
         end if;

         ----------------------------------------------------------------------

         Rule := Rule_Instance;

         --  This is the "generic" rule. It deals with the special upwards
         --  visibility of generic instances. Instead of following the
         --  normal rules for this we link all our parts to the template's
         --  corresponding parts, since the template's position in the graph
         --  determines our visibility, not the location of instantiation.

         if Is_Instance (Info) then
            if Is_Instance_Child (Info) then
               Connect
                 (Spec_V,
                  Scope_Graph.Get_Vertex ((Ent  => Info.Instance_Parent,
                                           Part => Visible_Part)));

               if Info.Is_Package then
                  Connect
                    (Priv_V,
                     Scope_Graph.Get_Vertex ((Ent  => Info.Instance_Parent,
                                              Part => Private_Part)));
               end if;

            else
               Connect
                 (Spec_V,
                  Scope_Graph.Get_Vertex ((Ent  => Info.Template,
                                           Part => Visible_Part)));

               --  Generic units acquire visibility from where they are
               --  instantiated, so they can "see" subprograms used to
               --  instantiate them (when instantiated, a formal subprogram
               --  becomes a renaming). Same for formal packages.
               --
               --  ??? do something similar when Is_Instance_Child is True

               Connect
                 (Spec_V,
                  Scope_Graph.Get_Vertex
                    ((if Is_Nested (Info)
                     then Info.Container
                     else (Ent  => Info.Parent,
                           Part => (if Info.Is_Private
                                    then Private_Part
                                    else Visible_Part)))));
               --  ??? The code for the target scope is repeated in rules
               --  Rule_Up_Spec and Rule_Down_Spec; this should be refactored.

               --  Visibility of the template's private part only matters if
               --  the template itself is a child unit, but it is safe to
               --  connect it in any case (and detecting which generic is a
               --  child unit would require extra info in phase 2).

               if Info.Is_Package then
                  Connect
                    (Priv_V,
                     Scope_Graph.Get_Vertex ((Ent  => Info.Template,
                                              Part => Private_Part)));
               end if;

               Connect
                 (Body_V,
                  Scope_Graph.Get_Vertex ((Ent  => Info.Template,
                                           Part => Body_Part)));

               --  For generic subprograms instantiated in the wrapper packages
               --  we need the visibility from the instantiated subprogram body
               --  to the wrapper package body, as otherwise the
               --  Subprogram_Refinement_Is_Visible says that the instantiated
               --  generic subprogram body can't see its own refinement.
               --
               --  ??? wrapper packages were ignored in the design document,
               --  probably this should be revisited.
               --
               --  ??? we need something similar for generic child subprograms
               --  of generic parents (i.e. the Is_Instance_Child branch above)

               if not Info.Is_Package then
                  Connect
                    (Body_V,
                     Scope_Graph.Get_Vertex (Body_Scope (Info.Container)));
               end if;
            end if;
         end if;

         ----------------------------------------------------------------------

         Rule := Rule_Up_Spec;

         --  This rule deals with upwards visibility, i.e. adding a link to
         --  the nearest "enclosing" scope. Generics are dealt with separately,
         --  ??? except for generic child instantiations (they have visibility
         --  of their parent's instantiation).

         if not Is_Instance (Info) then
            Connect
              (Spec_V,
               Scope_Graph.Get_Vertex
                 ((if Is_Nested (Info)
                   then Info.Container
                   else (Ent  => Info.Parent,
                         Part => (if Info.Is_Private
                                  then Private_Part
                                  else Visible_Part)))));
         end if;

         ----------------------------------------------------------------------

         --  As mentioned before, instances break the chain so they need
         --  special treatment, and the remaining three rules just add the
         --  appropriate links. Note that although the last three are mutually
         --  exclusive, any of them might be an instance.

         ----------------------------------------------------------------------

         Rule := Rule_Down_Spec;

         --  This rule deals with downwards visibility, i.e. contributing to
         --  the visibility of the surrounding context. It is exactly the
         --  inverse of Rule_Up_Spec, except there is no special treatment for
         --  instances (since a scope does have visibility of the spec of
         --  something instantiated inside it).

         Connect
           (Scope_Graph.Get_Vertex ((if Is_Nested (Info)
                                     then Info.Container
                                     else (Ent  => Info.Parent,
                                           Part => (if Info.Is_Private
                                                    then Private_Part
                                                    else Visible_Part)))),
            Spec_V);

         ----------------------------------------------------------------------

         Rule := Rule_Up_Priv;

         --  This rule deals with upwards visibility for the private part of a
         --  child package or subprogram. It doesn't apply to instances.

         if Is_Child (Info)
           and then not Is_Instance (Info)
         then
            Connect
              ((if Info.Is_Package
                then Priv_V
                else Body_V),
               Scope_Graph.Get_Vertex ((Ent  => Info.Parent,
                                        Part => Private_Part)));
         end if;

         ----------------------------------------------------------------------

         Rule := Rule_Up_Body;

         --  Finally, this rule deals with the upwards visibility for the body
         --  of a nested package. A nested scope will have visibility of its
         --  enclosing scope's body, since it is impossible to complete the
         --  body anywhere else. Again, it doesn't apply to instances.

         if Is_Nested (Info)
           and then not Is_Instance (Info)
         then
            Connect
              (Body_V,
               Scope_Graph.Get_Vertex ((Ent  => Info.Container.Ent,
                                        Part => Body_Part)));
         end if;
      end Connect;

   --  Start of processing for Connect_Flow_Scopes

   begin
      for C in Hierarchy_Info.Iterate loop
         declare
            E    : Entity_Id renames Hierarchy_Info_Maps.Key (C);
            Info : Hierarchy_Info_T renames Hierarchy_Info (C);
         begin
            Connect (E, Info);
         end;
      end loop;

      --  Release memory to the provers
      --  ??? Hierarchy_Info.Clear;

      --  At this point we could compute a transitive closure, but that can
      --  take huge amount of memory. This is because typically the visibility
      --  graph has many vertices and all of them are connected to all the
      --  enclosing scopes (up to Standard); however, the visibility paths
      --  are short and can be quickly discovered.

      --  In phase 1 we print the graph (if requested), but keep the hirarchy
      --  info for writing it to the ALI file; in phase 2 we clear the info,
      --  as it is no longer needed (while the graph is still needed for failed
      --  check explanations).

      if Gnat2Why_Args.Global_Gen_Mode then
         if Gnat2Why_Args.Flow_Advanced_Debug then
            Print (Scope_Graph);
         end if;
      else
         Hierarchy_Info.Clear;
         Hierarchy_Info.Reserve_Capacity (0);
      end if;

      Components := Scope_Graph.SCC;

      --  Sanity check: all vertices should be now connected to Standard

      declare
         Standard : constant Scope_Graphs.Vertex_Id :=
           Scope_Graph.Get_Vertex ((Ent  => Standard_Standard,
                                    Part => Visible_Part))
           with Ghost;

         use Scope_Graphs;

      begin
         pragma Assert
           (for all V of Scope_Graph.Get_Collection (All_Vertices) =>
               (if V /= Standard
                then Scope_Graph.Edge_Exists (Components, V, Standard)));
      end;

   end Connect_Flow_Scopes;

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

   --------------
   -- Is_Child --
   --------------

   function Is_Child (Info : Hierarchy_Info_T) return Boolean is
     (Present (Info.Parent));

   -----------------
   -- Is_Instance --
   -----------------

   function Is_Instance (Info : Hierarchy_Info_T) return Boolean is
     (Present (Info.Template));

   -----------------------
   -- Is_Instance_Child --
   -----------------------

   function Is_Instance_Child (Info : Hierarchy_Info_T) return Boolean is
     (Present (Info.Instance_Parent));

   ---------------
   -- Is_Nested --
   ---------------

   function Is_Nested (Info : Hierarchy_Info_T) return Boolean is
     (Present (Info.Container));

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
        or else Scope_Graph.Edge_Exists
          (Components,
           Sanitize (Looking_From),
           Sanitize (Looking_At));
   end Is_Visible;

   ---------------
   -- Make_Info --
   ---------------

   function Make_Info (N : Node_Id) return Hierarchy_Info_T is
      Def_E : constant Entity_Id := Defining_Entity (N);

      E : constant Entity_Id :=
        (if Nkind (N) = N_Private_Type_Declaration
         then DIC_Procedure (Def_E)
         elsif Nkind (N) = N_Full_Type_Declaration
         then Invariant_Procedure (Def_E)
         else Def_E);

      Is_Package      : Boolean;
      Is_Private      : Boolean;
      Parent          : Entity_Id;
      Instance_Parent : Entity_Id;
      Template        : Entity_Id;
      Container       : Flow_Scope;

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
               Is_Private :=
                 Nkind (Atree.Parent (N)) = N_Compilation_Unit
                   and then
                 Private_Present (Atree.Parent (N));
               Parent     := Scope (E);
            end if;
         elsif Get_Flow_Scope (N) = Null_Flow_Scope then
            Is_Private := False;
            Parent     := Standard_Standard;
         else
            Is_Private := False;
            Parent     := Empty;
         end if;

      else
         pragma Assert (Ekind (E) in Entry_Kind
                                   | E_Function
                                   | E_Procedure
                                   | E_Protected_Type
                                   | E_Task_Type
                                   | Generic_Subprogram_Kind);

         Is_Package := False;
         Is_Private :=
           Is_Compilation_Unit (E)
             and then
           Private_Present (Enclosing_Comp_Unit_Node (E));

         if Is_Compilation_Unit (E) then
            if Ekind (E) in E_Function | E_Procedure
              and then Is_Generic_Instance (E)
            then
               Parent := Empty;
            else
               Parent := Scope (E);
            end if;
         else
            Parent := Empty;
         end if;
      end if;

      if Is_Generic_Instance (E)
        and then not Is_Wrapper_Package (E)
      then
         Template := Generic_Parent (Specification (N));

         --  Deal with instances of child instances; this is based on frontend
         --  Install_Parent_Private_Declarations.

         if Is_Child_Unit (Template)
           and then Is_Generic_Unit (Scope (Template))
         then
            declare
               Child_Inst : constant Entity_Id :=
                 (if Ekind (E) = E_Package
                  then E
                  else Defining_Entity (Atree.Parent (Subprogram_Spec (E))));
               --  If the child instance is a package, we can directly pass it
               --  to Get_Unit_Instantiation_Node; when it is a subprogram, we
               --  must get its wrapper package. Typically it is just the Scope
               --  of E, except for instance-as-compilation-unit, where we need
               --  to retrieve the wrapper package syntactically.

               pragma Assert
                 (Ekind (E) = E_Package
                    or else
                  (Ekind (E) in E_Function | E_Procedure
                   and then Is_Wrapper_Package (Child_Inst)));

               Inst_Node : constant Node_Id :=
                 Get_Unit_Instantiation_Node (Child_Inst);

            begin
               pragma Assert (Nkind (Inst_Node) in N_Generic_Instantiation);
               --  The original frontend routine expects formal packages too,
               --  but in the backend we only instantiations, because formal
               --  packages have been expanded to renamings of instances.

               pragma Assert (Nkind (Name (Inst_Node)) = N_Expanded_Name);
               --  When analysing the generic parent body, frontend expects the
               --  child to be named either as "P.C" (N_Expanded_Name) or "C"
               --  (N_Identifier); when analysing its instance in the backend
               --  we only see N_Expanded_Name.

               Instance_Parent := Entity (Prefix (Name (Inst_Node)));

               pragma Assert (Ekind (Instance_Parent) = E_Package);

               if Present (Renamed_Entity (Instance_Parent)) then
                  Instance_Parent := Renamed_Entity (Instance_Parent);

                  pragma Assert (Ekind (Instance_Parent) = E_Package);

               end if;
            end;
         else
            Instance_Parent := Empty;
         end if;
      else
         Template        := Empty;
         Instance_Parent := Empty;
      end if;

      if Is_Child_Unit (E)
        and then Is_Text_IO_Special_Package (E)
      then
         Container := (Ent => Scope (E), Part => Visible_Part);
      else
         Container := Get_Flow_Scope (N);
      end if;

      -------------------------------------------------------------------------
      --  Invariant
      --
      --  This is intentonally a sequance of pragmas and not a Boolean-value
      --  function, because with pragmas if one of the conditions fails, it
      --  is easier to know which one.
      -------------------------------------------------------------------------

      pragma Assert (Present (Container) or else Present (Parent));
      --  Everything is nested or else has a parent

      pragma Assert (not (Is_Private and Present (Container)));
      --  Being "private" can only apply to non-nested packages

      pragma Assert (if Present (Template) then Is_Generic_Unit (Template));
      --  Template, if present, is a generic unit

      pragma Assert (if Present (Parent)
                     then Ekind (Parent) in E_Package | E_Generic_Package);
      --  Parent, if present, must be a package or a generic package

      -------------------------------------------------------------------------

      return (Is_Package      => Is_Package,
              Is_Private      => Is_Private,
              Parent          => Parent,
              Instance_Parent => Instance_Parent,
              Template        => Template,
              Container       => Container);
   end Make_Info;

   -----------
   -- Print --
   -----------

   procedure Print (G : Scope_Graphs.Graph)
   is
      use Scope_Graphs;

      Show_Empty_Subprogram_Bodies : constant Boolean := False;
      --  A debug flag fow showing/hiding subprograms with bo bodies (e.g. when
      --  the body is in another compilation unit, especially in a predefined
      --  one, like System; or when the subprogram is abstract). Those bodies
      --  make the graph harder to read.
      --  ??? perhaps we should not create vertices for those bodies in the
      --  first place.

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

         Show : Boolean;

      begin
         if S.Part = Body_Part
           and then Ekind (S.Ent) in E_Function | E_Procedure
           and then No (Subprogram_Body_Entity (S.Ent))
         then
            pragma Assert (G.In_Neighbour_Count (V) = 0);
            Show := Show_Empty_Subprogram_Bodies;
         else
            Show := True;
         end if;

         return (Show        => Show,
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
         pragma Unreferenced (B, Marked, Colour);

         S : constant Flow_Scope := G.Get_Key (A);

         Show : Boolean;

      begin
         if Ekind (S.Ent) in E_Function | E_Procedure
           and then S.Part = Body_Part
           and then No (Subprogram_Body_Entity (S.Ent))
         then
            pragma Assert (G.In_Neighbour_Count (A) = 0);
            Show := Show_Empty_Subprogram_Bodies;
         else
            Show := True;
         end if;

         return
           (Show   => Show,
            Shape  => Edge_Normal,
            Colour => Null_Unbounded_String,
            Label  => Null_Unbounded_String);
         --  ??? Label should reflect the Colour argument, but the current
         --  names of the rules are too long and produce unreadable graphs.
      end EDI;

      Filename : constant String :=
        Unique_Name (Unique_Main_Unit_Entity) & "_visibility";

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
        Scope_Graph.Get_Vertex (Sanitize (From));

      Target : constant Scope_Graphs.Vertex_Id :=
        Scope_Graph.Get_Vertex (Sanitize (To));

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
         S : constant Flow_Scope := Scope_Graph.Get_Key (V);
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
        (G             => Scope_Graph,
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
      with Pre => Nkind (N) in N_Entry_Declaration
                             | N_Generic_Declaration
                             | N_Package_Declaration
                             | N_Protected_Type_Declaration
                             | N_Subprogram_Declaration
                             | N_Subprogram_Body_Stub
                             | N_Task_Type_Declaration
                             | N_Abstract_Subprogram_Declaration
                  or else (Nkind (N) = N_Subprogram_Body
                           and then Acts_As_Spec (N))
                  or else (Nkind (N) = N_Private_Type_Declaration
                           and then Has_Own_DIC (Defining_Entity (N)))
                  or else (Nkind (N) = N_Full_Type_Declaration
                           and then Has_Own_Invariants (Defining_Entity (N)));
      --  ??? remove the "x" suffix once debugging is done

      -------------
      -- Process --
      -------------

      procedure Processx (N : Node_Id) is
         Def_E : constant Entity_Id := Defining_Entity (N);

         E : constant Entity_Id :=
           (if Nkind (N) = N_Private_Type_Declaration
            then DIC_Procedure (Def_E)
            elsif Nkind (N) = N_Full_Type_Declaration
            then Invariant_Procedure (Def_E)
            else Def_E);

         Info : constant Hierarchy_Info_T := Make_Info (N);

         Spec_V, Priv_V, Body_V : Scope_Graphs.Vertex_Id;
         --  Vertices for the visible (aka. "spec"), private and body parts

      begin
         if Is_Eliminated (E) then
            --  ??? when returning early we don't need the Info constant
            return;
         end if;

         --  ??? we don't need this info (except for debug?)

         Hierarchy_Info.Insert (E, Info);

         ----------------------------------------------------------------------
         --  Create vertices
         ----------------------------------------------------------------------

         Scope_Graph.Add_Vertex ((Ent => E, Part => Visible_Part), Spec_V);

         if Info.Is_Package then
            Scope_Graph.Add_Vertex ((Ent => E, Part => Private_Part), Priv_V);
         end if;

         Scope_Graph.Add_Vertex ((Ent => E, Part => Body_Part), Body_V);
      end Processx;

      procedure Traverse is new Traverse_Compilation_Unit (Processx);

   --  Start of processing for Build_Graph

   begin
      if Unit_Node = Standard_Package_Node then

         --  The Standard package is special: create vertices for its
         --  visible and private parts and connect them. This package declares
         --  no subprograms or abstract states, so we don't need a vertex for
         --  its body part.
         --
         --  This is based on the Ada RM 10.1.1(1): "Each library unit (except
         --  Standard) has a parent unit, which is a library package or generic
         --  library package."

         Scope_Graph.Add_Vertex
           ((Ent => Standard_Standard, Part => Visible_Part));

         Scope_Graph.Add_Vertex
           ((Ent => Standard_Standard, Part => Private_Part));

         Scope_Graph.Add_Edge
           ((Ent => Standard_Standard, Part => Private_Part),
            (Ent => Standard_Standard, Part => Visible_Part),
            Rule_Own);
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
            when N_Package_Declaration =>
               Process (N);
               Traverse_Visible_And_Private_Parts (Specification (N));

            when N_Generic_Package_Declaration =>
               Process (N);

            when N_Package_Body =>
               if Ekind (Unique_Defining_Entity (N)) /= E_Generic_Package then
                  Traverse_Package_Body (N);
               end if;

            when N_Package_Body_Stub =>
               if Ekind (Unique_Defining_Entity (N)) /= E_Generic_Package then
                  Traverse_Package_Body (Get_Body_From_Stub (N));
               end if;

            when N_Entry_Declaration
               | N_Generic_Subprogram_Declaration
               | N_Subprogram_Declaration
               | N_Abstract_Subprogram_Declaration
            =>
               --  ??? abstract subprograms have no bodies
               Process (N);

            when N_Subprogram_Body =>
               if Acts_As_Spec (N) then
                  Process (N);
               end if;

               if not Is_Generic_Subprogram (Unique_Defining_Entity (N)) then
                  Traverse_Subprogram_Body (N);
               end if;

            when N_Entry_Body =>
               Traverse_Subprogram_Body (N);

            when N_Subprogram_Body_Stub =>
               if Is_Subprogram_Stub_Without_Prior_Declaration (N) then
                  Process (N);
               end if;

               if not Is_Generic_Subprogram (Unique_Defining_Entity (N)) then
                  Traverse_Subprogram_Body (Get_Body_From_Stub (N));
               end if;

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

            when N_Private_Type_Declaration =>
               --  Both private and full view declarations might be represented
               --  by N_Private_Type_Declaration; the former comes from source,
               --  the latter comes from rewriting.

               if Comes_From_Source (N) then
                  declare
                     T : constant Entity_Id := Defining_Entity (N);

                  begin
                     if Has_Own_DIC (T)
                       and then Present (DIC_Procedure (T))
                     then
                        Process (N);
                     end if;
                  end;
               end if;

            when N_Full_Type_Declaration =>
               declare
                  T : constant Entity_Id := Defining_Entity (N);

               begin
                  --  For Type_Invariant'Class there will be no invariant
                  --  procedure; we ignore it, because this aspect is not
                  --  supported in SPARK anyway.

                  if Has_Own_Invariants (T)
                    and then Present (Invariant_Procedure (T))
                  then
                     Process (N);
                  end if;
               end;

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

   -------------------------
   -- Iterate_Flow_Scopes --
   -------------------------

   procedure Iterate_Flow_Scopes is
   begin
      for C in Hierarchy_Info.Iterate loop
         Process (Hierarchy_Info_Maps.Key (C), Hierarchy_Info (C));
      end loop;

      --  Release data that is no longer needed

      Hierarchy_Info.Clear;
      Hierarchy_Info.Reserve_Capacity (0);
   end Iterate_Flow_Scopes;

end Flow_Visibility;
