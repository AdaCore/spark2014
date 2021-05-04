------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                            V I S I B I L I T Y                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2018-2021, Altran UK Limited                --
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
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Ada.Text_IO;
with Flow.Dynamic_Memory;
with Gnat2Why_Args;
with Graphs;
with Sem_Util;

package body Flow_Generated_Globals.Phase_2.Visibility is

   Debug_Visibility : constant Boolean := False;

   Null_Name_Scope : constant Name_Scope := (Null_Entity_Name, Null_Part);
   --  Just like Empty, but for Name_Scope

   function Hash (S : Name_Scope) return Ada.Containers.Hash_Type
   with Pre => S /= Null_Name_Scope;

   type Edge_Kind is (Rule_Own,
                      Rule_Instance,
                      Rule_Up_Spec,
                      Rule_Down_Spec,
                      Rule_Up_Priv,
                      Rule_Up_Body);
   --  ??? same as in phase 1

   package Scope_Graphs is new
     Graphs (Vertex_Key   => Name_Scope,
             Edge_Colours => Edge_Kind,
             Null_Key     => Null_Name_Scope,
             Key_Hash     => Hash,
             Test_Key     => "=");

   package Name_Info_Maps is new
     Ada.Containers.Hashed_Maps (Key_Type        => Entity_Name,
                                 Element_Type    => Name_Info_T,
                                 Hash            => Name_Hash,
                                 Equivalent_Keys => "=",
                                 "="             => "=");

   Hierarchy_Info : Name_Info_Maps.Map;
   Scope_Graph    : Scope_Graphs.Graph := Scope_Graphs.Create;

   Components : Scope_Graphs.Strongly_Connected_Components;
   --  Pre-computed strongly connected components of the visibility graph for
   --  quickly answering visibility queries.

   Children : Name_Graphs.Map;
   Nested   : Name_Graphs.Map;
   --  ??? those should be maps from Entity_Name -> Name_Lists.List, just like
   --  in Flow_Generated_Globals.Traversal. Also, they are not used now, but
   --  the intention is to mimick the top-down traversal from phase 1, in
   --  particular, to synthesize the Initializes of a parent package with
   --  Part_Ofs its state located in its private children.

   function Present (E : Any_Entity_Name) return Boolean is
     (E /= Null_Entity_Name);

   function Is_Child          (Info : Name_Info_T) return Boolean;
   function Is_Nested         (Info : Name_Info_T) return Boolean;
   function Is_Instance       (Info : Name_Info_T) return Boolean;
   function Is_Instance_Child (Info : Name_Info_T) return Boolean;
   --  Utility routines for the hierarchy data

   function Body_Scope (S : Name_Scope) return Name_Scope;

   procedure Dump (E : Entity_Name; Info : Name_Info_T);

   procedure Print (G : Scope_Graphs.Graph);
   --  Pretty-print visibility graph

   procedure Print_Path (From, To : Name_Scope);
   pragma Unreferenced (Print_Path);
   --  To be used from the debugger

   function Scope (EN : Entity_Name) return Entity_Name;

   ----------------
   -- Body_Scope --
   ----------------

   function Body_Scope (S : Name_Scope) return Name_Scope is
   begin
      return (Ent => S.Ent, Part => Body_Part);
   end Body_Scope;

   -------------------------
   -- Connect_Name_Scopes --
   -------------------------

   procedure Connect_Name_Scopes is

      procedure Connect (E : Entity_Name; Info : Name_Info_T);

      -------------
      -- Connect --
      -------------

      procedure Connect (E : Entity_Name; Info : Name_Info_T) is

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
                    (if Is_Nested (Info)
                     then Info.Container
                     else (Ent  => Info.Parent,
                           Part => (if Info.Is_Private
                                    then Private_Part
                                    else Visible_Part))));
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
                 (if Is_Nested (Info)
                  then Info.Container
                  else (Ent  => Info.Parent,
                        Part => (if Info.Is_Private
                                 then Private_Part
                                 else Visible_Part))));
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
           (Scope_Graph.Get_Vertex (if Is_Nested (Info)
                                    then Info.Container
                                    else (Ent  => Info.Parent,
                                          Part => (if Info.Is_Private
                                                   then Private_Part
                                                   else Visible_Part))),
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
      --  The Standard package is special: create vertices for its visible and
      --  private parts and connect them. This package declares no subprograms
      --  or abstract states, so we don't need a vertex for its body part.
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

      for C in Hierarchy_Info.Iterate loop
         declare
            E    : Entity_Name renames Name_Info_Maps.Key (C);
            Info : Name_Info_T renames Hierarchy_Info (C);
         begin
            Connect (E, Info);
         end;
      end loop;

      --  At this point we could compute a transitive closure, but that appear
      --  slower than checking a path existence (and the closure can take huge
      --  amount of memory). This is because typically the visibility graph has
      --  many vertices and all of them are connected to all the enclosing
      --  scopes (up to Standard); however, the visibility paths are short.

      --  Print graph
      if Gnat2Why_Args.Flow_Advanced_Debug then
         Print (Scope_Graph);
      end if;

      Components := Scope_Graph.SCC;

      --  Release memory to the provers
      Hierarchy_Info.Clear;
      Hierarchy_Info.Reserve_Capacity (0);

      --  Sanity check: all vertices should be now connected to Standard

      declare
         Standard_Spec : constant Name_Scope := (Ent  => Standard_Standard,
                                                 Part => Visible_Part)
           with Ghost;

         Standard : constant Scope_Graphs.Vertex_Id :=
           Scope_Graph.Get_Vertex (Standard_Spec)
           with Ghost;

         use Scope_Graphs;

      begin
         pragma Assert
           (for all V of Scope_Graph.Get_Collection (All_Vertices) =>
              (if V /= Standard
               then Scope_Graph.Edge_Exists (Components, V, Standard)));
      end;

   end Connect_Name_Scopes;

   ----------
   -- Dump --
   ----------

   procedure Dump (E : Entity_Name; Info : Name_Info_T) is
      use Ada.Text_IO;
   begin
      if Debug_Visibility then
         Put (">>> " & To_String (E));
         if Is_Child (Info) then
            Put (" (child of " & To_String (Info.Parent) & ")");
         elsif Is_Nested (Info) then
            Put (" (nested in " & To_String (Info.Container.Ent) & ")");
         end if;
         New_Line;
      end if;
   end Dump;

   --------------
   -- Is_Child --
   --------------

   function Is_Child (Info : Name_Info_T) return Boolean is
     (Present (Info.Parent));

   -----------------
   -- Is_Instance --
   -----------------

   function Is_Instance (Info : Name_Info_T) return Boolean is
     (Present (Info.Template));

   -----------------------
   -- Is_Instance_Child --
   -----------------------

   function Is_Instance_Child (Info : Name_Info_T) return Boolean is
     (Present (Info.Instance_Parent));

   ---------------
   -- Is_Nested --
   ---------------

   function Is_Nested (Info : Name_Info_T) return Boolean is
     (Info.Container /= Null_Name_Scope);

   ----------
   -- Hash --
   ----------

   function Hash (S : Name_Scope) return Ada.Containers.Hash_Type is
      use type Ada.Containers.Hash_Type;
   begin
      return 17 * Name_Hash (S.Ent) + 13 * Declarative_Part'Pos (S.Part);
   end Hash;

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
         S : constant Name_Scope := G.Get_Key (V);

         Label : constant String :=
           To_String (S.Ent) &
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
                     (if S.Ent = Standard_Standard then "blue"
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
         pragma Unreferenced (G, A, B, Marked, Colour);

      begin
         return
           (Show   => True,
            Shape  => Edge_Normal,
            Colour => Null_Unbounded_String,
            Label  => Null_Unbounded_String);
         --  ??? Label should reflect the Colour argument, but the current
         --  names of the rules are too long and produce unreadable graphs.
      end EDI;

      Filename : constant String :=
        Sem_Util.Unique_Name (Main_Unit_Entity) & "_visibility_2";

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

   procedure Print_Path (From, To : Name_Scope) is

      Source : constant Scope_Graphs.Vertex_Id :=
        Scope_Graph.Get_Vertex (From);

      Target : constant Scope_Graphs.Vertex_Id :=
        Scope_Graph.Get_Vertex (To);

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
         S : constant Name_Scope := Scope_Graph.Get_Key (V);
      begin
         --  Print_Flow_Scope (S);
         --  ??? the above code produces no output in gdb; use Ada.Text_IO

         Ada.Text_IO.Put_Line
           (To_String (S.Ent) &
              " | " &
            (case Declarative_Part'(S.Part) is
                  when Visible_Part => "spec",
                  when Private_Part => "priv",
                  when Body_Part    => "body"));
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

   -------------------------
   -- Register_Name_Scope --
   -------------------------

   procedure Register_Name_Scope (E : Entity_Name; Info : Name_Info_T) is
      Spec_V, Priv_V, Body_V : Scope_Graphs.Vertex_Id;
      --  Vertices for the visible (aka. "spec"), private and body parts

      Inserted : Boolean;
      Position : Name_Info_Maps.Cursor;

      procedure Add (Map      : in out Name_Graphs.Map;
                     Key      : Entity_Name;
                     New_Item : Entity_Name);

      ---------
      -- Add --
      ---------

      procedure Add (Map      : in out Name_Graphs.Map;
                     Key      : Entity_Name;
                     New_Item : Entity_Name)
      is
         Inserted : Boolean;
         Position : Name_Graphs.Cursor;

      begin
         Map.Insert (Key      => Key,
                     Position => Position,
                     Inserted => Inserted);

         Map (Position).Insert (New_Item);
      end Add;

   --  Start of processing for Register_Name_Scope

   begin
      --  We first need info for all vertices and then we connect them

      Hierarchy_Info.Insert (Key      => E,
                             New_Item => Info,
                             Position => Position,
                             Inserted => Inserted);

      ----------------------------------------------------------------------
      --  Create vertices
      ----------------------------------------------------------------------

      if Inserted then
         Scope_Graph.Add_Vertex ((Ent => E, Part => Visible_Part), Spec_V);

         if Info.Is_Package then
            Scope_Graph.Add_Vertex ((Ent => E, Part => Private_Part), Priv_V);
         end if;

         Scope_Graph.Add_Vertex ((Ent => E, Part => Body_Part), Body_V);

         --  Populate containers for the hierarchical traversal

         if Is_Child (Info) then
            Add (Map => Children, Key => Info.Parent, New_Item => E);
         elsif Is_Nested (Info) then
            Add (Map => Nested, Key => Info.Container.Ent, New_Item => E);
         end if;

         pragma Debug (Dump (E, Info));
      else
         pragma Assert (Hierarchy_Info (Position) = Info);
      end if;
   end Register_Name_Scope;

   ----------------------------------------------------------------------------
   --  Utilities
   ----------------------------------------------------------------------------

   ---------------------------------
   -- State_Refinement_Is_Visible --
   ---------------------------------

   function State_Refinement_Is_Visible
     (State : Entity_Name;
      From  : Name_Scope)
      return Boolean
   is
      Looking_At : constant Name_Scope :=
        (Ent => Scope (State), Part => Body_Part);

   begin
      --  ??? The From = Looking_At is not used (because it might only happen
      --  when Up/Down projecting an abstract state to the scope of its
      --  package, which can only happen when it appears on the RHS of
      --  the Initializes contract, which is not allowed). But let's
      --  keep it for now, to be on the safe side, as I don't know
      --  what Non_Trivial_Path_Exists says when called with the same vertices.

      return State /= To_Entity_Name (Flow.Dynamic_Memory.Heap_State)
        and then
          (From = Looking_At
           or else Scope_Graph.Edge_Exists
             (Components,
              Scope_Graph.Get_Vertex (From),
              Scope_Graph.Get_Vertex (Looking_At)));
   end State_Refinement_Is_Visible;

   ------------------------
   -- Part_Of_Is_Visible --
   ------------------------

   function Part_Of_Is_Visible
     (State : Entity_Name;
      From  : Name_Scope)
      return Boolean
   is
      Looking_At : constant Name_Scope :=
        (Ent => Scope (State), Part => Private_Part);

   begin
      --  ??? see the comment about From = Looking_At

      return State /= To_Entity_Name (Flow.Dynamic_Memory.Heap_State)
        and then
          (From = Looking_At
           or else Scope_Graph.Edge_Exists
             (Components,
              Scope_Graph.Get_Vertex (From),
              Scope_Graph.Get_Vertex (Looking_At)));
   end Part_Of_Is_Visible;

   -----------
   -- Scope --
   -----------

   function Scope (EN : Entity_Name) return Entity_Name is

      use Ada.Strings;
      use Ada.Strings.Fixed;

      S : constant String := To_String (EN);
      J : constant Natural := Index (Source  => S,
                                     Pattern => "__",
                                     From    => S'Last,
                                     Going   => Backward);
      --  Given "xxx__yyy__zzz" we trim the trailing "__zzz"

   begin
      return To_Entity_Name (S (S'First .. J - 1));
   end Scope;

end Flow_Generated_Globals.Phase_2.Visibility;
