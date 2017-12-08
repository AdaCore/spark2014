------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W . R E F I N E M E N T                        --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--               Copyright (C) 2013-2017, Altran UK Limited                 --
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

with Ada.Containers;                 use Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;

with Lib;                            use Lib;
with Namet;                          use Namet;
with Nlists;                         use Nlists;
with Output;                         use Output;
with Sem_Aux;                        use Sem_Aux;
with Sprint;                         use Sprint;

with Common_Iterators;               use Common_Iterators;
with SPARK_Frame_Conditions;         use SPARK_Frame_Conditions;
with SPARK_Util;                     use SPARK_Util;
with SPARK_Util.External_Axioms; use SPARK_Util.External_Axioms;
with SPARK_Util.Subprograms;         use SPARK_Util.Subprograms;

with Flow_Debug;                     use Flow_Debug;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Utility;                   use Flow_Utility;

package body Flow_Refinement is

   function Get_Enclosing_Body_Flow_Scope (S : Flow_Scope) return Flow_Scope
   with Pre => S.Part = Body_Part;
   --  Returns the flow scope of the enclosing package or concurrent object if
   --  it exists and the null scope otherwise.
   --  ??? this should be merged into Get_Enclosing_Body_Flow_Scope

   ----------------
   -- Is_Visible --
   ----------------

   function Is_Visible (Target_Scope : Flow_Scope;
                        Looking_From : Flow_Scope)
                        return Boolean
   is
      --  Returns True iff the target scope is visible from S. We do this by
      --  moving up the scope DAG from S and testing if we have reached the
      --  target scope. If we hit the top (the null scope) without finding it,
      --  we return False.
      --
      --  The scope DAG may look like a twisty maze, but it is actually
      --  reasonably easy to traverse upwards. The only complication is when we
      --  deal with a private part, in which case we need to quickly check one
      --  extra scope (the visible part), but then we continue as normal.
      --
      --     S is...     Next node is...
      --     =======     ===============
      --     X|body      X|private
      --     X|private   X|visible             (check this first)
      --                 enclosing_scope (S)   (then continue here)
      --     X|visible   enclosing_scope (S)
      --
      --  The enclosing scope of S is computed by Get_Enclosing_Flow_Scope and
      --  is either:
      --
      --     1. The first parent (just going up the AST) of S which is a
      --        package/concurrent type (this deals with nested packages)
      --
      --     2. The first Scope (see einfo.ads) which is a package/concurrent
      --        type (this deals with public and private children)
      --
      --     3. null (if we have hit Standard)
      --
      --  The visibility is the same as before, i.e.
      --     S.Section = Enclosing_Scope (S).Section
      --  unless S is a private descendant, in which case it is always "priv".

      S : Flow_Scope renames Looking_From;

      Context : Flow_Scope;
   begin
      --  Go upwards from S (the scope we are in) and see if we end up in
      --  Target_Scope (what we're checking if we can see).
      Context := S;

      Climbing : while Present (Context) loop
         if Context.Ent = Target_Scope.Ent then
            --  Check visibility between different parts of the same entity
            if (case Context.Part is
                   when Body_Part    =>
                      True,

                   when Private_Part =>
                      Target_Scope.Part in Private_Part | Visible_Part,

                   when Visible_Part =>
                      Target_Scope.Part = Visible_Part,

                   when others       =>
                      raise Program_Error)
            then
               return True;
            else
               exit Climbing;
            end if;
         else
            case Context.Part is
               when Body_Part =>
                  declare
                     Enclosing_Body_Scope : constant Flow_Scope :=
                       Get_Enclosing_Body_Flow_Scope (Context);
                  begin
                     Context := (if Present (Enclosing_Body_Scope)
                                 then Enclosing_Body_Scope
                                 else Private_Scope (Context));
                  end;

               when Private_Part | Visible_Part =>
                  Context := Get_Enclosing_Flow_Scope (Context);

               when others =>
                  raise Program_Error;

            end case;
         end if;
      end loop Climbing;

      --  Check if Target_Scope is generally visible
      Context := Target_Scope;
      while Context /= Null_Flow_Scope loop
         case Declarative_Part'(Context.Part) is
            when Visible_Part =>
               Context := Get_Enclosing_Flow_Scope (Context);

            when Body_Part | Private_Part =>
               exit;
         end case;
      end loop;

      if Context = Null_Flow_Scope then
         return True;
      end if;

      --  Check if Target_Scope is nested within S
      pragma Assert (Target_Scope /= Null_Flow_Scope);

      return Target_Scope.Part = Visible_Part
         and then Is_Visible (Get_Enclosing_Flow_Scope (Target_Scope), S);
   end Is_Visible;

   function Is_Visible (N : Node_Id;
                        S : Flow_Scope)
                        return Boolean
   is
      Target_Scope : constant Flow_Scope := Get_Flow_Scope (N);
   begin
      return Is_Visible (Target_Scope, S);
   end Is_Visible;

   function Is_Visible (EN : Entity_Name;
                        S  : Flow_Scope)
                        return Boolean
   is
      E : constant Entity_Id := Find_Entity (EN);
   begin
      return (Present (E)
              and then Is_Visible (E, S));
   end Is_Visible;

   function Is_Visible (F : Flow_Id;
                        S : Flow_Scope)
                        return Boolean
   is
     (case F.Kind is
         when Direct_Mapping | Record_Field => Is_Visible (F.Node, S),
         when others                        => raise Program_Error);

   -------------------------
   -- Is_Globally_Visible --
   -------------------------

   function Is_Globally_Visible (N : Node_Id) return Boolean is
     (Is_Visible (N, Null_Flow_Scope));

   ---------------------------------
   -- Is_Visible_From_Other_Units --
   ---------------------------------

   function Is_Visible_From_Other_Units (N : Node_Id) return Boolean is

      Looking_Scop : constant Flow_Scope :=
        (if Is_Child_Unit (Main_Unit_Entity)
         then Get_Flow_Scope (Main_Unit_Entity)
         else Null_Flow_Scope);
      --  External scope for deciding "global" visibility of N
      --  ??? needs more testing for nodes in child units, e.g. bodies of child
      --  subprograms

   begin
      return Is_Visible (N, Looking_Scop);
   end Is_Visible_From_Other_Units;

   ------------------------------
   -- Get_Enclosing_Flow_Scope --
   ------------------------------

   function Get_Enclosing_Flow_Scope (S : Flow_Scope) return Flow_Scope is
   begin
      return
        (if Is_Child_Unit (S.Ent)
         then (Ent  => Scope (S.Ent),
               Part => (if Is_Private_Descendant (S.Ent)
                        then Private_Part
                        else S.Part))
         else Get_Flow_Scope (Unit_Declaration_Node (S.Ent)));
      --  Call to Get_Flow_Scope on a declaration node returns the scope where
      --  S.Ent is declared, not the scope of the S.Ent itself.
   end Get_Enclosing_Flow_Scope;

   -----------------------------------
   -- Get_Enclosing_Body_Flow_Scope --
   -----------------------------------

   function Get_Enclosing_Body_Flow_Scope (S : Flow_Scope) return Flow_Scope is
   begin
      --  Top-level (generic) and child package bodies are nested immediately
      --  in the Standard package.
      --  ??? is this really what want for child packages?
      if Is_Compilation_Unit (S.Ent) then
         return Null_Flow_Scope;

      --  Other body scopes are nested in the bodies of their enclosing scopes

      else
         declare
            Enclosing_Scope : constant Flow_Scope :=
              Get_Enclosing_Flow_Scope ((S.Ent, Visible_Part));
         begin
            --  Typically bodies that are not compilation units are nested in
            --  other bodies.

            if Present (Enclosing_Scope) then
               return (Ent  => Enclosing_Scope.Ent,
                       Part => Body_Part);

            --  Except for (generic) package bodies declared immediately in the
            --  bodies of top-level subprograms.

            else
               pragma Assert (Is_Subprogram (Main_Unit_Entity));
               return Null_Flow_Scope;
            end if;
         end;
      end if;
   end Get_Enclosing_Body_Flow_Scope;

   --------------------
   -- Get_Flow_Scope --
   --------------------

   function Get_Flow_Scope (N : Node_Id) return Flow_Scope
   is
      Context      : Node_Id := N;
      Prev_Context : Node_Id := Empty;

   begin
      loop
         case Nkind (Context) is
            --  Borders between subprogram stubs and their proper bodies are
            --  traversed transparently.

            when N_Subunit =>
               pragma Assert
                 (Nkind (Proper_Body (Context)) = N_Subprogram_Body);

               Context := Corresponding_Stub (Context);

               pragma Assert
                 (Nkind (Context) = N_Subprogram_Body_Stub);

            --  Borders between other stubs should not be traversed, because
            --  the proper bodies act as flow scopes.

            when N_Package_Body_Stub
               | N_Protected_Body_Stub
               | N_Task_Body_Stub
            =>
               raise Program_Error;

            when N_Package_Body =>
               --  For bodies of instances of generic packages we want the spec
               --  of the corresponding generic; for ordinary bodies, we want
               --  the original spec.

               declare
                  Context_Spec : constant Entity_Id :=
                    Unique_Defining_Entity (Context);

                  pragma Assert (Ekind (Context_Spec) = E_Package);

                  Orig_Spec : Entity_Id;

               begin
                  if Is_Generic_Instance (Context_Spec) then
                     Orig_Spec := Generic_Parent
                       (Package_Specification (Context_Spec));
                     pragma Assert (Ekind (Orig_Spec) = E_Generic_Package);
                  else
                     Orig_Spec := Context_Spec;
                  end if;

                  return (Ent  => Orig_Spec,
                          Part => Body_Part);
               end;

            when N_Protected_Body
               | N_Task_Body
            =>
               return (Ent  => Unique_Defining_Entity (Context),
                       Part => Body_Part);

            when N_Protected_Definition
               | N_Task_Definition
            =>
               --  Concurrent types have visible and private parts, but as
               --  far as state refinement it concerned, this does not matter.
               --
               --  ??? shall we eliminate concurrent types from Flow_Scope
               --  altogether?
               --
               --  ??? Defining_Entity doesn't work for concurrent definition;
               --  we need to call Parent to get to their declarations (there
               --  is no point in fixing this before the above ??? is decided).
               return (Ent  => Defining_Entity (Parent (Context)),
                       Part => Visible_Part);

            when N_Package_Specification =>
               declare
                  Gen_Par : constant Entity_Id := Generic_Parent (Context);
                  --  For checking if Context is an instance of generic package

                  Ent  : Entity_Id;
                  Part : Declarative_Part;
                  --  Components of the result

               begin
                  --  For an instance of a generic package we want the generic;
                  --  for an ordinary package, we want the package itself.
                  if Present (Gen_Par) then
                     Ent := Gen_Par;
                     pragma Assert (Ekind (Ent) = E_Generic_Package);
                  else
                     Ent := Defining_Entity (Context);
                     pragma Assert (Ekind (Ent) = E_Package);
                  end if;

                  --  We have to decide if we come from visible or private part
                  pragma Assert (Present (Prev_Context)
                                 and then Context = Parent (Prev_Context));

                  --  For an expression function we want to get the same
                  --  Flow_Scope we would get if it was a function with a body.
                  --  For this we pretend that expression functions declared in
                  --  package spec are in package body.

                  if Nkind (Prev_Context) = N_Subprogram_Body
                    and then Was_Expression_Function (Prev_Context)
                  then
                     Part := Body_Part;

                  --  If we came from the package entity ifself, or from its
                  --  contract, then the previous context is not a list member.
                  --  Those cases are handled as the visible part, we only need
                  --  a dedicated check for the private part.

                  elsif Is_List_Member (Prev_Context)
                    and then List_Containing (Prev_Context) =
                             Private_Declarations (Context)
                  then
                     Part := Private_Part;
                  else
                     Part := Visible_Part;
                  end if;

                  return (Ent  => Ent,
                          Part => Part);
               end;

            --  We only see N_Aspect_Specification here when Get_Flow_Scope is
            --  called on an abstract state. We want to return the Visible_Part
            --  of the package that introduces the abstract state.

            when N_Aspect_Specification =>
               pragma Assert (Ekind (N) = E_Abstract_State);

               pragma Assert
                 (Nkind (Parent (Context)) = N_Package_Declaration);

               return (Ent  => Defining_Entity (Parent (Context)),
                       Part => Visible_Part);

            --  Front end rewrites aspects into pragmas with empty parents. In
            --  such cases we jump to the entity of the aspect.

            when N_Pragma =>
               Prev_Context := Context;

               if From_Aspect_Specification (Context) then
                  Context := Corresponding_Aspect (Context);
                  pragma Assert (Nkind (Context) = N_Aspect_Specification);
                  Context := Entity (Context);
               else
                  Context := Parent (Context);
               end if;

            when N_Subprogram_Body =>
               --  For bodies that come from instances of generic subprograms
               --  we divert the traversal to where the generic subprogram body
               --  is defined.

               if Is_Generic_Instance (Unique_Defining_Entity (Context)) then
                  declare
                     Instance : constant Entity_Id :=
                       Corresponding_Spec (Context);

                     pragma Assert (Is_Subprogram (Instance));

                     Generic_Spec : constant Entity_Id :=
                       Generic_Parent (Subprogram_Specification (Instance));

                     pragma Assert (Is_Generic_Subprogram (Generic_Spec));

                     Generic_Decl : constant Node_Id :=
                       Parent (Subprogram_Specification (Generic_Spec));

                     pragma Assert (Nkind (Generic_Decl) =
                                      N_Generic_Subprogram_Declaration);

                     Generic_Body : constant Entity_Id :=
                       Corresponding_Body (Generic_Decl);

                     pragma Assert (Ekind (Generic_Body) = E_Subprogram_Body);

                  begin
                     Prev_Context := Subprogram_Body (Generic_Body);
                     Context      := Parent (Prev_Context);
                  end;

               --  For bodies of ordinary subprograms we simply up-traverse

               else
                  Prev_Context := Context;
                  Context      := Parent (Context);
               end if;

               --  In both cases the previous context should point to the
               --  subprogram body, either generic or ordinary.

               pragma Assert (Nkind (Prev_Context) = N_Subprogram_Body);

            when N_Subprogram_Declaration =>
               --  For declarations that come from instances of generic
               --  subprograms we divert the traversal to where the generic
               --  subprogram is declared (similar to what we do for their
               --  bodies).
               if Is_Generic_Instance (Defining_Entity (Context)) then
                  declare
                     Instance : constant Entity_Id :=
                       Defining_Entity (Context);

                     pragma Assert (Is_Subprogram (Instance));

                     Generic_Spec : constant Entity_Id :=
                       Generic_Parent (Subprogram_Specification (Instance));

                     pragma Assert (Is_Generic_Subprogram (Generic_Spec));

                     Generic_Decl : constant Node_Id :=
                       Parent (Subprogram_Specification (Generic_Spec));

                     pragma Assert (Nkind (Generic_Decl) =
                                      N_Generic_Subprogram_Declaration);

                  begin
                     Prev_Context := Generic_Decl;
                     Context      := Parent (Prev_Context);
                  end;

               --  For ordinary subprograms we simply up-traverse

               else
                  Prev_Context := Context;
                  Context      := Parent (Context);
               end if;

            when others =>
               Prev_Context := Context;
               Context      := Parent (Context);
         end case;

         exit when No (Context);
      end loop;

      return Null_Flow_Scope;
   end Get_Flow_Scope;

   --------------------------------------
   -- Subprogram_Refinement_Is_Visible --
   --------------------------------------

   function Subprogram_Refinement_Is_Visible (E : Entity_Id;
                                              S : Flow_Scope)
                                              return Boolean
   is
      Body_E : constant Entity_Id := Get_Body_Entity (E);

   begin
      return Present (Body_E)
        and then Is_Visible (Get_Flow_Scope (Body_E), S);
   end Subprogram_Refinement_Is_Visible;

   ---------------------------------
   -- State_Refinement_Is_Visible --
   ---------------------------------

   function State_Refinement_Is_Visible (E : Checked_Entity_Id;
                                         S : Flow_Scope)
                                         return Boolean
   is
     ((Present (S.Ent)
       and then Is_Private_Descendant (S.Ent)
       and then Is_Visible (Private_Scope (Get_Flow_Scope (E)), S))
      or else
      (Entity_Body_In_SPARK (Scope (E))
       and then Is_Visible (Body_Scope (Get_Flow_Scope (E)), S)));

   function State_Refinement_Is_Visible (EN : Entity_Name;
                                         S  : Flow_Scope)
                                         return Boolean
   is
      E : constant Entity_Id := Find_Entity (EN);
   begin
      return (Present (E)
              and then State_Refinement_Is_Visible (E, S));
   end State_Refinement_Is_Visible;

   function State_Refinement_Is_Visible (F : Flow_Id;
                                         S : Flow_Scope)
                                         return Boolean
   is
     (case F.Kind is
         when Direct_Mapping =>
            State_Refinement_Is_Visible (F.Node, S),
         when others =>
            raise Program_Error);

   ------------------------
   -- Is_Fully_Contained --
   ------------------------

   function Is_Fully_Contained (State   : Entity_Id;
                                Outputs : Node_Sets.Set)
                                return Boolean
   is
      --  ??? Respect SPARK_Mode barrier, see Expand_Abstract_State
     ((for all C of Iter (Refinement_Constituents (State))
       => Outputs.Contains (C))
        and then
      (for all C of Iter (Part_Of_Constituents (State))
       => Outputs.Contains (C)));

   function Is_Fully_Contained (State   : Entity_Name;
                                Outputs : Name_Sets.Set)
                                return Boolean
   is
     (Name_Sets.Is_Subset (Subset => Get_Constituents (State),
                           Of_Set => Outputs));

   function Is_Fully_Contained (State   : Flow_Id;
                                Outputs : Flow_Id_Sets.Set)
                                return Boolean
   is
     (case State.Kind is
         when Direct_Mapping =>
            Is_Fully_Contained (State.Node, To_Node_Set (Outputs)),
         when others =>
            raise Program_Error);

   ----------------
   -- Up_Project --
   ----------------

   procedure Up_Project (Vars      :     Node_Sets.Set;
                         Scope     :     Flow_Scope;
                         Projected : out Node_Sets.Set;
                         Partial   : out Node_Sets.Set)
   is
   begin
      Projected.Clear;
      Partial.Clear;

      for Var of Vars loop
         if Is_Constituent (Var) then
            declare
               State : constant Entity_Id := Encapsulating_State (Var);

            begin
               if State_Refinement_Is_Visible (State, Scope) then
                  Projected.Include (Var);
               else
                  Partial.Include (State);
               end if;
            end;
         else
            Projected.Include (Var);
         end if;
      end loop;
   end Up_Project;

   procedure Up_Project (Vars         :     Name_Sets.Set;
                         Folded_Scope :     Flow_Scope;
                         Projected    : out Name_Sets.Set;
                         Partial      : out Name_Sets.Set)
   is
   begin
      Projected.Clear;
      Partial.Clear;

      for Var of Vars loop
         if GG_Is_Constituent (Var) then
            declare
               State : constant Entity_Name := GG_Encapsulating_State (Var);

            begin
               if State_Refinement_Is_Visible (State, Folded_Scope) then
                  Projected.Include (Var);
               else
                  Partial.Include (State);
               end if;
            end;
         else
            Projected.Include (Var);
         end if;
      end loop;
   end Up_Project;

   procedure Up_Project (Vars      :     Flow_Id_Sets.Set;
                         Scope     :     Flow_Scope;
                         Projected : out Flow_Id_Sets.Set;
                         Partial   : out Flow_Id_Sets.Set)
   is
   begin
      Projected.Clear;
      Partial.Clear;

      for Var of Vars loop
         if Is_Constituent (Var) then
            pragma Assert (Var.Kind in Direct_Mapping | Record_Field);
            declare
               Projected_Entity, Partial_Entity : Node_Sets.Set;

            begin
               --  Since we only up-project Flow_Ids with constituents that are
               --  internally represented by Entity_Id, we can reuse the
               --  existing logic for up-projecting those. For this we call the
               --  variant for Node_Sets with singleton set; this gives a
               --  singleton set a result (with either a projected or
               --  unmodified constituent).
               --
               --  ??? repetition of code for Entity_Id/Entity_Name/Flow_Id and
               --  their sets and maps deserves a non-trivial rewrite.

               Up_Project (Node_Sets.To_Set (Get_Direct_Mapping_Id (Var)),
                           Scope, Projected_Entity, Partial_Entity);

               --  Either Projected_Entity is empty and Partial_Entity is a
               --  singleton set, or the other way round.
               pragma Assert
                 (Projected_Entity.Length + Partial_Entity.Length = 1);

               if Partial_Entity.Is_Empty then
                  Projected.Include (Var);
               else
                  Partial.Include (Encapsulating_State (Var));
               end if;
            end;
         else
            Projected.Include (Var);
         end if;
      end loop;
   end Up_Project;

   procedure Up_Project (Vars           :     Global_Nodes;
                         Projected_Vars : out Global_Nodes;
                         Scope          : Flow_Scope)
   is
      use type Node_Sets.Set;

      Projected, Partial : Node_Sets.Set;

   begin
      Up_Project (Vars.Inputs, Scope, Projected, Partial);
      Projected_Vars.Inputs := Projected or Partial;

      Up_Project (Vars.Outputs, Scope, Projected, Partial);
      for State of Partial loop
         if not Is_Fully_Contained (State, Vars.Outputs) then
            Projected_Vars.Inputs.Include (State);
         end if;
      end loop;
      Projected_Vars.Outputs := Projected or Partial;

      Up_Project (Vars.Proof_Ins, Scope, Projected, Partial);
      Projected_Vars.Proof_Ins :=
        (Projected or Partial) -
        (Projected_Vars.Inputs or Projected_Vars.Outputs);
   end Up_Project;

   procedure Up_Project (Vars           :     Global_Names;
                         Projected_Vars : out Global_Names;
                         Scope          : Flow_Scope)
   is
      use type Name_Sets.Set;

      Projected, Partial : Name_Sets.Set;

   begin
      Up_Project (Vars.Inputs, Scope, Projected, Partial);
      Projected_Vars.Inputs := Projected or Partial;

      Up_Project (Vars.Outputs, Scope, Projected, Partial);
      for State of Partial loop
         if not Is_Fully_Contained (State, Vars.Outputs) then
            Projected_Vars.Inputs.Include (State);
         end if;
      end loop;
      Projected_Vars.Outputs := Projected or Partial;

      Up_Project (Vars.Proof_Ins, Scope, Projected, Partial);
      Projected_Vars.Proof_Ins :=
        (Projected or Partial) -
        (Projected_Vars.Inputs or Projected_Vars.Outputs);
   end Up_Project;

   procedure Up_Project (Vars           :     Global_Flow_Ids;
                         Projected_Vars : out Global_Flow_Ids;
                         Scope          : Flow_Scope)
   is
      use type Flow_Id_Sets.Set;

      Projected, Partial : Flow_Id_Sets.Set;

   begin
      Up_Project (Vars.Inputs, Scope, Projected, Partial);
      Projected_Vars.Inputs := Projected or Partial;

      Up_Project (Vars.Outputs, Scope, Projected, Partial);
      for State of Partial loop
         if not Is_Fully_Contained (State, Vars.Outputs) then
            Projected_Vars.Inputs.Include (Change_Variant (State, In_View));
         end if;
      end loop;
      Projected_Vars.Outputs := Projected or Partial;

      Up_Project (Vars.Proof_Ins, Scope, Projected, Partial);
      Projected_Vars.Proof_Ins :=
        (Projected or Partial) -
        (Projected_Vars.Inputs or
           Change_Variant (Projected_Vars.Outputs, In_View));
   end Up_Project;

   procedure Up_Project (Vars           : Dependency_Maps.Map;
                         Projected_Vars : out Dependency_Maps.Map;
                         Scope          : Flow_Scope)
   is
      use type Flow_Id_Sets.Set;

      function Constituents_Are_Partially_Mentioned (State : Flow_Id;
                                                     Deps  : Flow_Id_Sets.Set)
                                                     return Boolean;
      --  Returns True in case at least one, but not all, of the constituents
      --  of State are an input in the dependecy relation or in case the input
      --  in the dependency relation is null and not all the constitutents of
      --  State are outputs in the dependency relation.

      ------------------------------------------
      -- Constituents_Are_Partially_Mentioned --
      ------------------------------------------

      function Constituents_Are_Partially_Mentioned (State : Flow_Id;
                                                     Deps  : Flow_Id_Sets.Set)
                                                     return Boolean
      is
         Constituents_Written : Flow_Id_Sets.Set;
         --  Contains the constituents that are outputs of the dependency map

         function Contains_Some_Constituents return Boolean;
         --  Returns True iff Deps contains some constituents of State

         --------------------------------
         -- Contains_Some_Constituents --
         --------------------------------

         function Contains_Some_Constituents return Boolean
         is
            --  ??? Do the same of Expand_Abstract_State
           (for some C of Iter (Refinement_Constituents (State.Node))
              => Deps.Contains (Direct_Mapping_Id (C))
            or else
           (for some C of Iter (Part_Of_Constituents (State.Node))
              => Deps.Contains (Direct_Mapping_Id (C))));

      --  Start of processing for Constituents_Are_Partially_Mentioned

      begin
         --  Collect outputs in the dependency relations that are constituents
         --  of an abstract state.
         for C in Vars.Iterate loop
            declare
               Var : Flow_Id renames Dependency_Maps.Key (C);

            begin
               if Is_Constituent (Var) then
                  Constituents_Written.Insert (Var);
               end if;
            end;
         end loop;

         return
           (Contains_Some_Constituents
            and then not Is_Fully_Contained (State, Deps))
           or else
             (Deps.Is_Empty
              and then not Is_Fully_Contained (State, Constituents_Written));
      end Constituents_Are_Partially_Mentioned;

   --  Start of processing for Up_Project

   begin
      --  Up project the dependency relation and add a self dependency on an
      --  abstract state if not all of its constituents are used.
      for C in Vars.Iterate loop
         declare
            Var  : Flow_Id          renames Dependency_Maps.Key (C);
            Deps : Flow_Id_Sets.Set renames Vars (C);

            Projected_Var      : Flow_Id;
            Projected, Partial : Flow_Id_Sets.Set;
            Projected_Deps     : Flow_Id_Sets.Set;

            Position : Dependency_Maps.Cursor;
            Unused   : Boolean;

         begin
            Up_Project (Deps, Scope, Projected, Partial);
            Projected_Deps := Projected or Partial;

            --  Reuse set-based up-projection routine with a singleton set, for
            --  which the result is also a singleton set.
            Up_Project (Flow_Id_Sets.To_Set (Var), Scope, Projected, Partial);
            pragma Assert (Partial.Length + Projected.Length = 1);

            Projected_Var := (if Projected.Is_Empty
                              then Partial (Partial.First)
                              else Projected (Projected.First));

            --  If Projected_Var is an abstract state and not all of its
            --  constituents are mentioned in the dependency relation then we
            --  add it as in input in the dependency relation.
            if Is_Abstract_State (Projected_Var)
              and then Constituents_Are_Partially_Mentioned (Projected_Var,
                                                             Deps)
            then
               Projected_Deps.Include (Projected_Var);
            end if;

            --  Insert {Projected_Var -> Projected_Deps} into Projected_Vars
            --  without crashing if the mapping is already there.

            Projected_Vars.Insert (Key      => Projected_Var,
                                   Position => Position,
                                   Inserted => Unused);

            Projected_Vars (Position).Union (Projected_Deps);
         end;
      end loop;
   end Up_Project;

   -----------------------
   -- Get_Contract_Node --
   -----------------------

   function Get_Contract_Node (E : Entity_Id;
                               S : Flow_Scope;
                               C : Contract_T)
                               return Node_Id
   is
      Prag : Node_Id;

   begin
      if Subprogram_Refinement_Is_Visible (E, S) then
         Prag :=
           Find_Contract
             (E,
              (case C is
                  when Global_Contract  => Pragma_Refined_Global,
                  when Depends_Contract => Pragma_Refined_Depends));
      else
         Prag := Empty;
      end if;

      if No (Prag) then
         Prag :=
           Find_Contract (E,
                          (case C is
                              when Global_Contract  => Pragma_Global,
                              when Depends_Contract => Pragma_Depends));
      end if;

      return Prag;
   end Get_Contract_Node;

   ----------------------------
   -- Default_Initialization --
   ----------------------------

   function Default_Initialization (Typ        : Entity_Id;
                                    Scope      : Flow_Scope;
                                    Ignore_DIC : Boolean := False)
                                    return Default_Initialization_Kind
   is
      Init : Default_Initialization_Kind;

      FDI : Boolean := False;
      NDI : Boolean := False;
      --  Two flags used to designate whether a record type has at least one
      --  fully default initialized component and/or one not fully default
      --  initialized component.

      procedure Process_Component (Rec_Prot_Comp : Entity_Id);
      --  Process component Rec_Prot_Comp of a record or protected type

      -----------------------
      -- Process_Component --
      -----------------------

      procedure Process_Component (Rec_Prot_Comp : Entity_Id) is
         Comp : Entity_Id := Rec_Prot_Comp;
      begin
         --  The components of discriminated subtypes are not marked as source
         --  entities because they are technically "inherited" on the spot. To
         --  handle such components, use the original record component defined
         --  in the parent type.

         if Present (Original_Record_Component (Comp)) then
            Comp := Original_Record_Component (Comp);
         end if;

         --  Do not process internally generated components except for _parent
         --  which represents the ancestor portion of a derived type.

         if Comes_From_Source (Comp)
           or else Chars (Comp) = Name_uParent
         then
            Init := Default_Initialization (Base_Type (Etype (Comp)),
                                            Scope,
                                            Ignore_DIC);

            --  A component with mixed initialization renders the whole
            --  record/protected type mixed.

            if Init = Mixed_Initialization then
               FDI := True;
               NDI := True;

            --  The component is fully default initialized when its type
            --  is fully default initialized or when the component has an
            --  initialization expression. Note that this has precedence
            --  given that the component type may lack initialization.

            elsif Init = Full_Default_Initialization
              or else Present (Expression (Parent (Comp)))
            then
               FDI := True;

            --  Components with no possible initialization are ignored

            elsif Init = No_Possible_Initialization then
               null;

            --  The component has no full default initialization

            else
               NDI := True;
            end if;
         end if;
      end Process_Component;

      --  Local variables

      Comp   : Entity_Id;
      Result : Default_Initialization_Kind;

   --  Start of processing for Default_Initialization

   begin
      --  For types that are not in SPARK we trust the declaration. This means
      --  that if we find a Default_Initial_Condition aspect we trust it.

      if Ignore_DIC
        and then Full_View_Not_In_SPARK (Typ)
      then
         return Default_Initialization (Typ, Scope);
      end if;

      --  If we are considering implicit initializations and
      --  Default_Initial_Condition was specified for the type, take it into
      --  account.

      if not Ignore_DIC
        and then Has_Own_DIC (Typ)
      then
         declare
            Prag : constant Node_Id   :=
              Get_Pragma (Typ, Pragma_Default_Initial_Condition);

         begin
            --  The pragma has an argument. If NULL, this indicates a value of
            --  the type is not default initialized. Otherwise, a value of the
            --  type should be fully default initialized.

            if Present (Prag) then
               declare
                  Pragma_Assoc : constant List_Id :=
                    Pragma_Argument_Associations (Prag);

               begin
                  if Present (Pragma_Assoc)
                    and then Nkind (Get_Pragma_Arg (First (Pragma_Assoc))) =
                               N_Null
                  then
                     Result := No_Default_Initialization;
                  else
                     Result := Full_Default_Initialization;
                  end if;
               end;

            --  Otherwise the pragma appears without an argument, indicating
            --  a value of the type if fully default initialized.

            else
               Result := Full_Default_Initialization;
            end if;
         end;

      --  We assume access types to be not initialized as they are not in SPARK
      --  ??? In theory we shouldn't arrive here because we shouldn't analyse
      --  types that are not in SPARK.

      elsif Is_Access_Type (Typ) then
         Result := Full_Default_Initialization;

      --  A scalar type subject to aspect/pragma Default_Value is
      --  fully default initialized.

      elsif Is_Scalar_Type (Typ)
        and then Is_Scalar_Type (Base_Type (Typ))
        and then Present (Default_Aspect_Value (Base_Type (Typ)))
      then
         Result := Full_Default_Initialization;

      --  A scalar type whose base type is private may still be subject to
      --  aspect/pragma Default_Value, so it depends on the base type.

      elsif Is_Scalar_Type (Typ)
        and then Is_Private_Type (Base_Type (Typ))
      then
         pragma Assert (Entity_In_SPARK (Base_Type (Typ)));
         Result := Default_Initialization (Base_Type (Typ),
                                           Scope,
                                           Ignore_DIC);

      --  A derived type is only initialized if its base type and any
      --  extensions that it defines are fully default initialized.

      elsif Is_Derived_Type (Typ) then
         --  If the type does inherit a default initial condition then we take
         --  it into account.

         if not Ignore_DIC
           and then Has_Inherited_DIC (Typ)
         then
            pragma Assert (Entity_In_SPARK (Etype (Typ)));
            Result := Default_Initialization (Etype (Typ),
                                              Scope,
                                              Ignore_DIC);
         else
            declare
               Type_Def : Node_Id := Empty;
               Rec_Part : Node_Id := Empty;

            begin
               --  If Typ is an Itype, it may not have an Parent field pointing
               --  to a corresponding declaration. In that case, there is no
               --  record extension part to check for default initialization.
               --  Similarly, if the corresponding declaration is not a full
               --  type declaration for a derived type definition, there is no
               --  extension part to check.

               if Present (Parent (Typ))
                 and then Nkind (Parent (Typ)) = N_Full_Type_Declaration
               then
                  Type_Def := Type_Definition (Parent (Typ));
                  if Nkind (Type_Def) = N_Derived_Type_Definition then
                     Rec_Part := Record_Extension_Part (Type_Def);
                  end if;
               end if;

               --  If there is an extension part then we need to look into it
               --  in order to determine initialization of the type.

               if Present (Rec_Part) then

                  --  If the extension part is visible from the current scope
                  --  the we analyse it.

                  if Is_Visible (Rec_Part, Scope) then

                     --  If the extension is null then initialization of this
                     --  type is equivalent to the initialization for its
                     --  Etype.

                     if Null_Present (Rec_Part) then
                        pragma Assert (Entity_In_SPARK (Etype (Typ)));
                        Result := Default_Initialization (Etype (Typ),
                                                          Scope,
                                                          Ignore_DIC);

                     --  If the extension is not null then we need to analyse
                     --  it.

                     else
                        --  When the derived type has extensions we check both
                        --  the base type and the extensions.
                        declare
                           Base_Initialized : Default_Initialization_Kind;
                           Ext_Initialized  : Default_Initialization_Kind;
                        begin
                           pragma Assert (Entity_In_SPARK (Etype (Typ)));
                           Base_Initialized :=
                             Default_Initialization (Etype (Typ),
                                                     Scope,
                                                     Ignore_DIC);

                           if Is_Tagged_Type (Typ) then
                              Comp := First_Non_Pragma
                                (Component_Items (Component_List (Rec_Part)));
                           else
                              Comp := First_Non_Pragma
                                        (Component_Items (Rec_Part));
                           end if;

                           --  Inspect all components of the extension

                           if Present (Comp) then
                              while Present (Comp) loop
                                 if Ekind (Defining_Identifier (Comp)) =
                                   E_Component
                                 then
                                    Process_Component
                                      (Defining_Identifier (Comp));
                                 end if;

                                 Next_Non_Pragma (Comp);
                              end loop;

                              --  Detect a mixed case of initialization

                              if FDI and NDI then
                                 Ext_Initialized := Mixed_Initialization;

                              elsif FDI then
                                 Ext_Initialized :=
                                   Full_Default_Initialization;

                              elsif NDI then
                                 Ext_Initialized := No_Default_Initialization;

                              --  The type either has no components or they
                              --  are all internally generated. The extensions
                              --  are trivially fully default initialized

                              else
                                 Ext_Initialized :=
                                   Full_Default_Initialization;
                              end if;

                              --  The extension is null, there is nothing to
                              --  initialize.

                           else
                              if Ignore_DIC then
                                 --  The extensions are trivially fully default
                                 --  initialized.
                                 Ext_Initialized :=
                                   Full_Default_Initialization;
                              else
                                 Ext_Initialized :=
                                   No_Possible_Initialization;
                              end if;
                           end if;

                           if Base_Initialized = Full_Default_Initialization
                             and then Ext_Initialized =
                               Full_Default_Initialization
                           then
                              Result := Full_Default_Initialization;
                           else
                              Result := No_Default_Initialization;
                           end if;
                        end;
                     end if;

                  --  If the extension is not visible then we assume there is
                  --  no default initialization as we cannot see the extension

                  else
                     Result := No_Default_Initialization;
                  end if;

               --  If there is no extension then we analyse initialization for
               --  the Etype.
               else
                  pragma Assert (Entity_In_SPARK (Etype (Typ)));
                  Result := Default_Initialization (Etype (Typ),
                                                    Scope,
                                                    Ignore_DIC);
               end if;
            end;
         end if;

      --  The initialization status of a private type depends on its full view

      elsif Is_Private_Type (Typ) then
         declare
            Full_V : constant Entity_Id := Full_View (Typ);

         begin
            --  If continue analysing the full view of the private type only if
            --  it is visible from the Scope and its full view is in SPARK.

            if Present (Full_V)
              and then Is_Visible (Full_V, Scope)
              and then not Full_View_Not_In_SPARK (Typ)
            then
               pragma Assert (Entity_In_SPARK (Full_V));

               Result := Default_Initialization (Full_V,
                                                 Scope,
                                                 Ignore_DIC);
            else
               Result := No_Default_Initialization;
            end if;
         end;

      --  Task types are always fully default initialized

      elsif Is_Task_Type (Typ) then
         Result := Full_Default_Initialization;

      --  An array type subject to aspect/pragma Default_Component_Value is
      --  fully default initialized. Otherwise its initialization status is
      --  that of its component type.

      elsif Is_Array_Type (Typ) then
         if Present (Default_Aspect_Component_Value
                     (if Is_Partial_View (Base_Type (Typ))
                        then Full_View (Base_Type (Typ))
                        else Base_Type (Typ)))
         then
            Result := Full_Default_Initialization;
         else
            Result := Default_Initialization (Component_Type (Typ),
                                              Scope,
                                              Ignore_DIC);
         end if;

      --  Record types and protected types offer several initialization options
      --  depending on their components (if any).

      elsif Is_Record_Type (Typ) or else Is_Protected_Type (Typ) then
         Comp := First_Entity (Typ);

         --  Inspect all components

         if Present (Comp) then
            while Present (Comp) loop
               if Ekind (Comp) = E_Component then
                  Process_Component (Comp);
               end if;

               Next_Entity (Comp);
            end loop;

            --  Detect a mixed case of initialization

            if FDI and NDI then
               Result := Mixed_Initialization;

            elsif FDI then
               Result := Full_Default_Initialization;

            elsif NDI then
               Result := No_Default_Initialization;

            --  The type either has no components or they are all
            --  internally generated.

            else
               if Ignore_DIC then
                  --  The record is considered to be trivially fully
                  --  default initialized.
                  Result := Full_Default_Initialization;
               else
                  Result := No_Possible_Initialization;
               end if;
            end if;

         --  The type is null, there is nothing to initialize.

         else
            if Ignore_DIC then
               --  We consider the record to be trivially fully
               --  default initialized.
               Result := Full_Default_Initialization;
            else
               Result := No_Possible_Initialization;
            end if;
         end if;

      --  The type has no default initialization

      else
         Result := No_Default_Initialization;
      end if;

      --  In specific cases, we'd rather consider the type as having no
      --  default initialization (which is allowed in SPARK) rather than
      --  mixed initialization (which is not allowed).

      if Result = Mixed_Initialization then

         --  If the type is one for which an external axiomatization
         --  is provided, it is fine if the implementation uses mixed
         --  initialization. This is the case for formal containers in
         --  particular.

         if Type_Based_On_Ext_Axioms (Typ) then
            Result := No_Default_Initialization;

         --  If the type is private or class wide, it is fine if the
         --  implementation uses mixed initialization. An error will be issued
         --  when analyzing the implementation if it is in a SPARK part of the
         --  code.

         elsif Is_Private_Type (Typ) or else Is_Class_Wide_Type (Typ) then
            Result := No_Default_Initialization;
         end if;
      end if;

      return Result;
   end Default_Initialization;

   ------------------
   -- Down_Project --
   ------------------

   function Down_Project (Var : Entity_Id;
                          S   : Flow_Scope)
                          return Node_Sets.Set
   is
      P : Node_Sets.Set;

      procedure Expand (E : Entity_Id);
      --  Include the abstract state E into P if its refinement is not visible,
      --  otherwise we include all of its consitituents.

      ------------
      -- Expand --
      ------------

      procedure Expand (E : Entity_Id) is
      begin
         if Ekind (E) = E_Abstract_State then
            declare
               Pkg : constant Entity_Id := Scope (E);

            begin
               if Entity_Body_In_SPARK (Pkg)
                 and then State_Refinement_Is_Visible (E, S)
               then
                  --  ??? do the same as in Expand_Abstract_State

                  if not Has_Null_Refinement (E) then
                     for C of Iter (Refinement_Constituents (E)) loop
                        if Is_Visible (C, S) then
                           Expand (C);
                        else
                           P.Include (E);
                           return;
                        end if;
                     end loop;
                  end if;
               else
                  P.Include (E);
               end if;
            end;

         else
            P.Include (E);
         end if;
      end Expand;

   --  Start of processing for Down_Project

   begin
      Expand (Var);

      return P;
   end Down_Project;

   function Down_Project (Vars : Node_Sets.Set;
                          S    : Flow_Scope)
                          return Node_Sets.Set
   is
      P : Node_Sets.Set;
   begin
      for V of Vars loop
         P.Union (Down_Project (V, S));
      end loop;

      return P;
   end Down_Project;

   function Down_Project (Var : Flow_Id;
                          S   : Flow_Scope)
                          return Flow_Id_Sets.Set
   is
   begin
      case Var.Kind is
         when Direct_Mapping =>
            return
              To_Flow_Id_Set (Down_Project (Get_Direct_Mapping_Id (Var), S),
                              View => Var.Variant);
         when Magic_String =>
            return Flow_Id_Sets.To_Set (Var);
         when others =>
            raise Program_Error;
      end case;
   end Down_Project;

   function Down_Project (Vars : Flow_Id_Sets.Set;
                          S    : Flow_Scope)
                          return Flow_Id_Sets.Set
   is
      P : Flow_Id_Sets.Set;
   begin
      for V of Vars loop
         P.Union (Down_Project (V, S));
      end loop;
      return P;
   end Down_Project;

   -------------------------
   -- Find_In_Initializes --
   -------------------------

   function Find_In_Initializes (E : Checked_Entity_Id) return Entity_Id is
      State : constant Entity_Id := Encapsulating_State (E);

      Target_Ent : constant Entity_Id :=
        (if Present (State) and then Scope (E) = Scope (State)
         then State
         else Unique_Entity (E)); --  ??? why unique entity?
      --  What we are searching for. Either the entity itself, or, if this
      --  entity is a constituent of an abstract state of its immediately
      --  enclosing package, that abstract state.

      P : Entity_Id := E;

   begin
      while not Is_Package_Or_Generic_Package (P) loop
         pragma Assert (Ekind (P) /= E_Package_Body);
         P := Scope (P);
      end loop;

      --  ??? a simple traversal like in Find_Global better fits here

      declare
         M : constant Dependency_Maps.Map := Parse_Initializes (P);

      begin
         for Initialized_Var in M.Iterate loop
            declare
               F : Flow_Id renames Dependency_Maps.Key (Initialized_Var);
            begin
               --  The package whose state variable E is known by an Entity_Id
               --  must itself be known by an Entity_Id, but the left-hand
               --  sides of its Initializes aspect might include objects from
               --  the package body that are promoted to implicit abstract
               --  states.
               pragma Assert (F.Kind in Direct_Mapping | Magic_String);

               if F.Kind = Direct_Mapping
                 and then Get_Direct_Mapping_Id (F) = Target_Ent
               then
                  return Target_Ent;
               end if;
            end;
         end loop;
      end;

      return Empty;
   end Find_In_Initializes;

   -----------------------------------
   -- Is_Initialized_At_Elaboration --
   -----------------------------------

   function Is_Initialized_At_Elaboration (E : Checked_Entity_Id;
                                           S : Flow_Scope)
                                           return Boolean
   is
      Trace : constant Boolean := False;
      --  Enable this for some tracing output

      function Common_Ancestor (A, B : Flow_Scope) return Flow_Scope;
      --  Return the common ancestor of both flow scopes

      ---------------------
      -- Common_Ancestor --
      ---------------------

      function Common_Ancestor (A, B : Flow_Scope) return Flow_Scope is

         package Scope_Lists is new
           Ada.Containers.Doubly_Linked_Lists (Element_Type => Flow_Scope);

         function Heritage (S : Flow_Scope) return Scope_Lists.List
           with Post => not Heritage'Result.Is_Empty and then
                        No (Heritage'Result.First_Element) and then
                        Heritage'Result.Last_Element = S;
         --  Determine all ancestors of S up to and including Standard

         --------------
         -- Heritage --
         --------------

         function Heritage (S : Flow_Scope) return Scope_Lists.List is

            function Ancestor (S : Flow_Scope) return Flow_Scope
              with Pre => Present (S);
            --  Determine the immediate ancestor of S

            --------------
            -- Ancestor --
            --------------

            function Ancestor (S : Flow_Scope) return Flow_Scope is
            begin
               case Declarative_Part'(S.Part) is
                  when Body_Part =>
                     return Private_Scope (S);

                  when Private_Part | Visible_Part =>
                     return Get_Enclosing_Flow_Scope (S);
               end case;
            end Ancestor;

            Context : Flow_Scope := S;
            L       : Scope_Lists.List;

         --  Start of processing for Heritage

         begin
            loop
               L.Prepend (Context);
               exit when No (Context);
               Context := Ancestor (Context);
            end loop;

            return L;
         end Heritage;

         L1 : constant Scope_Lists.List := Heritage (A);
         L2 : constant Scope_Lists.List := Heritage (B);

         C1 : Scope_Lists.Cursor := L1.First;
         C2 : Scope_Lists.Cursor := L2.First;

         Last_Common_Ancestor : Scope_Lists.Cursor;

      --  Start of processing for Common_Ancestor

      begin
         loop
            pragma Loop_Invariant (L1 (C1) = L2 (C2));

            Last_Common_Ancestor := C1;

            Scope_Lists.Next (C1);
            Scope_Lists.Next (C2);

            if Scope_Lists.Has_Element (C1)
              and then Scope_Lists.Has_Element (C2)
              and then L1 (C1) = L2 (C2)
            then
               null;
            else
               return L1 (Last_Common_Ancestor);
            end if;
         end loop;
      end Common_Ancestor;

      Ent  : Entity_Id  := E;
      Ptr  : Flow_Scope := Get_Flow_Scope (E);
      Init : Boolean;

      Common_Scope : constant Flow_Scope := Common_Ancestor (Ptr, S);

   --  Start of processing for Is_Initialized_At_Elaboration

   begin
      if Trace then
         Write_Str ("Query: ");
         Sprint_Node (E);
         Write_Str (" from scope ");
         Print_Flow_Scope (S);
         Write_Eol;

         Write_Str ("   -> common scope: ");
         Print_Flow_Scope (Common_Scope);
         Write_Eol;
      end if;

      loop
         if Trace then
            Write_Str ("   -> looking at ");
            Sprint_Node (Ent);
            Write_Eol;
         end if;

         case Ekind (Ent) is
            when E_Abstract_State =>
               null;

            when E_Constant       =>
               --  Constants are always initialized at elaboration
               return True;

            when E_Variable       =>
               if Is_Concurrent_Type (Etype (Ent)) then
                  --  Instances of a protected type are always fully default
                  --  initialized.
                  --  ??? arrays and record with protected types too
                  return True;
               elsif Is_Part_Of_Concurrent_Object (Ent) then
                  --  Variables that are Part_Of a concurrent type are always
                  --  fully default initialized.
                  return True;
               elsif Is_Predefined_Initialized_Variable (Ent) then
                  --  We don't have many predefined units with an Initializes
                  --  contract, but we still want to know if their variables
                  --  are initialized.
                  return True;
               end if;

            when others           =>
               raise Program_Error;
         end case;

         Init := Present (Find_In_Initializes (Ent));

         if Ptr.Ent in Common_Scope.Ent | S.Ent then
            if Trace then
               Write_Line ("   -> in common scope or home");
            end if;

            if Ekind (Ent) = E_Variable and then
              Present (Encapsulating_State (Ent)) and then
              Get_Flow_Scope (Encapsulating_State (Ent)).Ent = Ptr.Ent
            then
               if Trace then
                  Write_Line ("   -> looking up");
               end if;
               Init := Present (Find_In_Initializes
                                  (Encapsulating_State (Ent)));
            end if;
            return Init;
         end if;

         Ent := Encapsulating_State (Ent);
         if Present (Ent) then
            Ptr := Get_Flow_Scope (Ent);
         else
            return Init;
         end if;
      end loop;

   end Is_Initialized_At_Elaboration;

   --------------------------------------------
   -- Mentions_State_With_Visible_Refinement --
   --------------------------------------------

   function Mentions_State_With_Visible_Refinement
     (N     : Node_Id;
      Scope : Flow_Scope)
      return Boolean
   is
      function Proc (N : Node_Id) return Traverse_Result;
      --  Traversal procedure; returns Abandon when we find an abstract state
      --  whose refinement is visible from Scope.

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) in N_Identifier | N_Expanded_Name then
            declare
               E : constant Entity_Id := Entity (N);
            begin
               if Present (E)
                 and then Ekind (E) = E_Abstract_State
                 and then State_Refinement_Is_Visible (E, Scope)
               then
                  return Abandon;
               end if;
            end;
         end if;

         --  Keep looking...
         return OK;
      end Proc;

      function Find_Abstract_State is new Traverse_Func (Process => Proc);

   --  Start of processing for Mentions_State_With_Visible_Refinement

   begin
      return Find_Abstract_State (N) = Abandon;
   end Mentions_State_With_Visible_Refinement;

   -----------------------
   -- Refinement_Needed --
   -----------------------

   function Refinement_Needed (E : Entity_Id) return Boolean is
      Depends_N : constant Node_Id :=
        Find_Contract (E, Pragma_Depends);
      Global_N  : constant Node_Id :=
        Find_Contract (E, Pragma_Global);

      Refined_Depends_N : constant Node_Id :=
        Find_Contract (E, Pragma_Refined_Depends);
      Refined_Global_N  : constant Node_Id :=
        Find_Contract (E, Pragma_Refined_Global);

      B_Scope : constant Flow_Scope := Get_Flow_Scope (Get_Body_Entity (E));

   begin
      return
        --  1) No Global and no Depends aspect
        (No (Global_N) and then No (Depends_N))

          or else

        --  2) Global refers to state abstraction with visible refinement but
        --     no Refined_Global is present.
        (Present (Global_N) and then
         No (Refined_Global_N) and then
         No (Refined_Depends_N) and then  -- ???
         Mentions_State_With_Visible_Refinement (Global_N, B_Scope))

          or else

        --  3) Depends refers to state abstraction with visible refinement but
        --     no Refined_Depends is present.
        (Present (Depends_N) and then
         No (Refined_Depends_N) and then
         No (Refined_Global_N) and then  -- ???
         Mentions_State_With_Visible_Refinement (Depends_N, B_Scope));
   end Refinement_Needed;

   -----------------------------------
   -- Nested_Within_Concurrent_Type --
   -----------------------------------

   function Nested_Within_Concurrent_Type (T : Type_Id;
                                           S : Flow_Scope)
                                           return Boolean
   is (Present (S) and then Sem_Util.Scope_Within_Or_Same (S.Ent, T));

   -------------------------------------
   -- Is_Boundary_Subprogram_For_Type --
   -------------------------------------

   function Is_Boundary_Subprogram_For_Type (Subprogram : Subprogram_Id;
                                             Typ        : Type_Id)
                                             return Boolean
   is
     (Scope_Within_Or_Same (Scope (Subprogram), Scope (Typ))
      and then Is_Globally_Visible (Subprogram));

end Flow_Refinement;
