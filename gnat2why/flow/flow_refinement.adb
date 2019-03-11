------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W . R E F I N E M E N T                        --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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

with Nlists;                         use Nlists;
with Output;                         use Output;
with Sem_Aux;                        use Sem_Aux;
with Sprint;                         use Sprint;

with Common_Iterators;               use Common_Iterators;
with SPARK_Frame_Conditions;         use SPARK_Frame_Conditions;
with SPARK_Util;                     use SPARK_Util;
with SPARK_Util.Subprograms;         use SPARK_Util.Subprograms;

with Flow_Debug;                     use Flow_Debug;
with Flow_Utility;                   use Flow_Utility;
with Flow_Visibility;

package body Flow_Refinement is

   ----------------
   -- Is_Visible --
   ----------------

   function Is_Visible (Target_Scope : Flow_Scope;
                        Looking_From : Flow_Scope)
                        return Boolean
   is
   begin
      --  As far as flow analysis is concerned, there are no generics, only
      --  instances, so we should not ask about visibility of generic units.
      --  (The locations of generics and their instances impact visibility,
      --  but this already captured in the visibility graph.)

      pragma Assert (if Present (Target_Scope)
                     then not Is_Generic_Unit (Target_Scope.Ent));

      pragma Assert (if Present (Looking_From)
                     then not Is_Generic_Unit (Looking_From.Ent));

      return Flow_Visibility.Is_Visible
        (Looking_From => Looking_From,
         Looking_At   => Target_Scope);
      --  ??? this routine only flips the order or parameters between what is
      --  more readable in flow and what the underlying Edge_Exists expects.
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

   function Is_Visible_From_Other_Units (E : Entity_Id) return Boolean is

      Looking_At : constant Flow_Scope :=
        (Ent => E, Part => Visible_Part);
      --  We don't use Get_Flow_Scope here because top-level subprograms
      --  declared directly in the .adb file have all their Node_Ids belonging
      --  the body and Get_Flow_Scope would (rightly) return the body scope.

      Main_Entity : constant Entity_Id := Unique_Main_Unit_Entity;
      --  Main entity of the current compilation unit, which by its very nature
      --  is visible from any unit that WITHs it; in other words, there always
      --  exists some other compilation unit which can see this entity.

      Looking_From : constant Flow_Scope :=
        (Ent  => Main_Entity,
         Part => (if Ekind (Main_Entity) = E_Package
                  then Private_Part
                  else Visible_Part));
      --  If E itself is visible from the main entity of this unit, then it can
      --  be also seen from the other units. If the main entity is a package,
      --  then we check visibility from its private part, because anything
      --  declared in the private part can be seen from a private child unit.

   begin
      return Is_Visible (Looking_At, Looking_From);
   end Is_Visible_From_Other_Units;

   ------------------------------
   -- Get_Enclosing_Flow_Scope --
   ------------------------------

   function Get_Enclosing_Flow_Scope (S : Flow_Scope) return Flow_Scope is
   begin
      return
        (if Is_Child_Unit (S.Ent)
         then (Ent  => Scope (S.Ent),
               Part => (if Private_Present (Enclosing_Comp_Unit_Node (S.Ent))
                        then Private_Part
                        else S.Part))
         else Get_Flow_Scope (Unit_Declaration_Node (S.Ent)));
      --  Call to Get_Flow_Scope on a declaration node returns the scope where
      --  S.Ent is declared, not the scope of the S.Ent itself.
   end Get_Enclosing_Flow_Scope;

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
            --  We only come to subunits from their proper bodies when queried
            --  on where the body is located, which is really a query of where
            --  the corresponding stub is located. To give this answer we
            --  restart the query at where the stub is.

            when N_Subunit =>
               pragma Assert
                 (Prev_Context = Proper_Body (Context));

               Prev_Context := Empty;
               Context      := Corresponding_Stub (Context);

               pragma Assert (Nkind (Context) in N_Body_Stub);

            --  Borders between other stubs should not be traversed, because
            --  the proper bodies act as flow scopes.

            when N_Package_Body_Stub
               | N_Protected_Body_Stub
               | N_Subprogram_Body_Stub
               | N_Task_Body_Stub
            =>
               --  Ada RM 10.1.3(13): A body_stub shall appear immediately
               --  within the declarative_part of a compilation unit body.
               --  [This rule does not apply within an instance of a generic
               --  unit. (but this should be transparently eliminated when
               --  frontend instantiates a generic body].

               if Present (Prev_Context) then
                  return (Ent  => Unique_Defining_Entity (Context),
                          Part => Body_Part);
               else
                  Prev_Context := Context;
                  Context      := Parent (Context);
               end if;

            when N_Entry_Body
               | N_Package_Body
               | N_Protected_Body
               | N_Subprogram_Body
               | N_Task_Body
            =>
               declare
                  E : constant Entity_Id := Unique_Defining_Entity (Context);

               begin
                  if Present (Prev_Context) then
                     if Ekind (E) = E_Procedure
                       and then (Is_DIC_Procedure (E)
                                 or else Is_Invariant_Procedure (E))
                     then
                        --  ??? redirect to where the type is declared
                        Context :=
                          Declaration_Node (Etype (First_Formal (E)));
                     else
                        return (Ent  => E,
                                Part => Body_Part);
                     end if;
                  else
                     if Ekind (E) = E_Procedure
                       and then (Is_DIC_Procedure (E)
                                 or else Is_Invariant_Procedure (E))
                     then
                        --  ??? redirect to where the type is declared
                        Context :=
                          Declaration_Node (Etype (First_Formal (E)));
                     else
                        Prev_Context := Context;
                        Context      := Parent (Context);
                     end if;
                  end if;
               end;

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
                  Ent  : constant Entity_Id := Defining_Entity (Context);
                  Part : Declarative_Part;
                  --  Components of the result

               begin
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

            --  Front end rewrites aspects into pragmas with empty parents. In
            --  such cases we jump to the entity of the aspect.

            when N_Pragma =>
               --  Pretend that pre- and postconditions are attached to the
               --  body; this makes no difference for flow analysis (which
               --  relies on the FA.S_Scope and FA.B_Scope that are set before
               --  analysing any subprogram), but is needed for proof (which
               --  simply calls Get_Flow_Scope as needed).

               if Get_Pragma_Id (Context) in Pragma_Contract_Cases
                                           | Pragma_Initial_Condition
                                           | Pragma_Precondition
                                           | Pragma_Postcondition
               then
                  if From_Aspect_Specification (Context) then
                     return (Ent  => Entity (Corresponding_Aspect (Context)),
                             Part => Body_Part);
                  else
                     return (Ent  => Unique_Defining_Entity (Parent (Context)),
                             Part => Body_Part);
                  end if;
               end if;

               Prev_Context := Context;

               if From_Aspect_Specification (Context) then
                  Context := Corresponding_Aspect (Context);
                  pragma Assert (Nkind (Context) = N_Aspect_Specification);
                  Context := Entity (Context);
               else
                  Context := Parent (Context);
               end if;

            when N_Entry_Declaration
               | N_Subprogram_Declaration
               | N_Abstract_Subprogram_Declaration
            =>
               if Present (Prev_Context) then
                  return (Ent  => Defining_Entity (Context),
                          Part => Visible_Part);
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
      Body_N : constant Node_Id := Get_Body (E);
      --  The outer-most node of the body of E, so that its Get_Flow_Scope will
      --  return the scope where the body appears, not the scope of the body
      --  itself.

   begin
      return Present (Body_N)
        and then Is_Visible (Get_Flow_Scope (Body_N), S);
   end Subprogram_Refinement_Is_Visible;

   ---------------------------------
   -- State_Refinement_Is_Visible --
   ---------------------------------

   function State_Refinement_Is_Visible (E : Checked_Entity_Id;
                                         S : Flow_Scope)
                                         return Boolean
   is
   begin
      --  State refinement is visible iff the body of its enclosing package is
      --  visible.

      return
        Is_Visible (Target_Scope => (Ent => Scope (E), Part => Body_Part),
                    Looking_From => S);
   end State_Refinement_Is_Visible;

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
                                Outputs : Node_Sets.Set;
                                Scop    : Flow_Scope)
                                return Boolean
   is
   begin
      return Node_Sets.Is_Subset (Subset =>
                                    Down_Project (State, Body_Scope (Scop)),
                                  Of_Set => Outputs);
   end Is_Fully_Contained;

   function Is_Fully_Contained (State   : Flow_Id;
                                Outputs : Flow_Id_Sets.Set;
                                Scop    : Flow_Scope)
                                return Boolean
   is
     (case State.Kind is
         when Direct_Mapping =>
            Is_Fully_Contained (State.Node, To_Node_Set (Outputs), Scop),
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

            --  We project depending on whether the constituent is visible (and
            --  not its enclosing state refinement), because when projecting to
            --  a private part of a package spec where that constituent is
            --  declared (as a Part_Of an abstract state) we want the
            --  constituent, which is the most precise result we can get.

            if Is_Visible (Var, Scope) then
               Projected.Include (Var);
            else
               Partial.Include (Encapsulating_State (Var));
            end if;
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
         if Var.Kind = Direct_Mapping
           and then Is_Constituent (Get_Direct_Mapping_Id (Var))
         then
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
         if not Is_Fully_Contained (State, Vars.Outputs, Scope) then
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
         if not Is_Fully_Contained (State, Vars.Outputs, Scope) then
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

   procedure Up_Project (Deps           : Dependency_Maps.Map;
                         Projected_Deps : out Dependency_Maps.Map;
                         Scope          : Flow_Scope)
   is
      LHS_Constituents : Flow_Id_Sets.Set;
      --  Constituents that are appear on the LHS of the dependency map

      Non_Null_RHSs : Flow_Id_Sets.Set;
      --  Entities that appear on the RHS of non-null projected clauses

      Null_Clause : Dependency_Maps.Cursor;
      --  Position of the "null => ..." clause

      Visible_Views  : Flow_Id_Sets.Set;
      Projection_Map : Flow_Id_Surjection.Map;

      function Visible_View (F : Flow_Id) return Flow_Id
      with Pre  => Present (F),
           Post => Present (Visible_View'Result);

      ------------------
      -- Visible_View --
      ------------------

      function Visible_View (F : Flow_Id) return Flow_Id is
         Projected, Partial : Flow_Id_Sets.Set;

      begin
         if Is_Constituent (F) then
            Up_Project (Flow_Id_Sets.To_Set (F), Scope, Projected, Partial);
            pragma Assert (Partial.Length + Projected.Length = 1);

            return (if Projected.Is_Empty
                    then Partial (Partial.First)
                    else Projected (Projected.First));
         else
            return F;
         end if;
      end Visible_View;

   --  Start of processing for Up_Project

   begin
      --  First, up-project all items in the dependency map to their most
      --  precise representation that is visible from Scope.

      for Clause in Deps.Iterate loop
         declare
            LHS : Flow_Id renames Dependency_Maps.Key (Clause);
            RHS : Flow_Id_Sets.Set renames Deps (Clause);

            procedure Add_Mapping (Item : Flow_Id);
            --  Add mapping from Item to its most precise representation

            -----------------
            -- Add_Mapping --
            -----------------

            procedure Add_Mapping (Item : Flow_Id) is
               Repr : constant Flow_Id := Visible_View (Item);

            begin
               Projection_Map.Include (Key      => Item,
                                       New_Item => Repr);

               Visible_Views.Include (Repr);
            end Add_Mapping;

         begin
            if Present (LHS) then
               Add_Mapping (LHS);
            end if;

            for RHS_Item of RHS loop
               Add_Mapping (RHS_Item);
            end loop;
         end;
      end loop;

      --  The most precise representation might violate SPARK RM 7.2.6(7), i.e.
      --  we might get both a constituent and its encapsulating abstract state.
      --  We climb the abstract state hierarchy and if get an abstract state
      --  that appears in the contract we subsitute the target with that
      --  abstract state.

      for Mapping in Projection_Map.Iterate loop
         declare
            Source : Flow_Id renames Flow_Id_Surjection.Key (Mapping);
            Target : Flow_Id renames Projection_Map (Mapping);

            pragma Unreferenced (Source);
            --  This is for debug

            Repr : Flow_Id := Target;

         begin
            while Is_Constituent (Repr) loop
               Repr := Encapsulating_State (Repr);
               if Present (Repr) then
                  if Visible_Views.Contains (Repr) then
                     Target := Repr;
                  end if;
               else
                  exit;
               end if;
            end loop;
         end;
      end loop;

      --  Collect constituents from the LHS of the dependency map; we will
      --  use them to decide whether to add a self-dependency on their
      --  encapsulating abstract states for states that are partially-written.

      for Clause in Deps.Iterate loop
         declare
            Var : Flow_Id renames Dependency_Maps.Key (Clause);

         begin
            if Is_Constituent (Var) then
               LHS_Constituents.Insert (Var);
            end if;
         end;
      end loop;

      --  Up-project the dependency relation and add a self-dependency for
      --  abstract states that are partially-written.

      for Clause in Deps.Iterate loop
         declare
            LHS : Flow_Id          renames Dependency_Maps.Key (Clause);
            RHS : Flow_Id_Sets.Set renames Deps (Clause);

            Projected_RHS    : Flow_Id_Sets.Set;
            Projected_Clause : Dependency_Maps.Cursor;

            Unused : Boolean;

         begin
            for Item of RHS loop
               Projected_RHS.Include (Projection_Map (Item));
            end loop;

            --  If the LHS was up-projected to an abstract state then the RHS
            --  require a special processing.

            if Present (LHS) and then LHS /= Projection_Map (LHS) then
               declare
                  LHS_State : constant Flow_Id := Projection_Map (LHS);

               begin
                  --  If State represents a partial-write of an abstract state
                  --  (i.e. if not all of the constituents appear on the LHSs),
                  --  then add the state itself to the RHS; i.e. the unmodified
                  --  constituents behave as if they would be updated with
                  --  their old values.

                  if not Is_Fully_Contained (LHS_State, LHS_Constituents,
                                             Scope)
                  then
                     Projected_RHS.Include (LHS_State);
                  end if;

                  --  Insert {State -> Projected_RHS} into Projected_Deps
                  --  without crashing if State is already in the map (i.e.
                  --  it was inserted when up-projecting another constituent).

                  Projected_Deps.Insert (Key      => LHS_State,
                                         Position => Projected_Clause,
                                         Inserted => Unused);
               end;

            --  Otherwise, the LHS was transparently projected and will be used
            --  as it was.

            else
               declare
                  LHS_Object : constant Flow_Id :=
                    (if Present (LHS)
                     then Projection_Map (LHS)
                     else Null_Flow_Id);

               begin
                  Projected_Deps.Insert (Key      => LHS_Object,
                                         Position => Projected_Clause,
                                         Inserted => Unused);

                  if Present (LHS_Object) then
                     Non_Null_RHSs.Union (Projected_RHS);
                  end if;
               end;
            end if;

            Projected_Deps (Projected_Clause).Union (Projected_RHS);
         end;
      end loop;

      --  Postprocessing required by the SPARK RM 6.1.5(13): "An entity denoted
      --  by an input which is in an input_list of a null_dependency_clause
      --  shall not be denoted by an input in another input_list of the same
      --  dependency_relation."

      Null_Clause := Projected_Deps.Find (Null_Flow_Id);

      if Dependency_Maps.Has_Element (Null_Clause) then
         Projected_Deps (Null_Clause).Difference (Non_Null_RHSs);

         --  ??? it is tempting to remove the "null => null" clause here, just
         --  like it is in Compute_Dependency_Relation, but apparently this
         --  cause crashes when processing unconstrained record types
      end if;

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
                  if not Has_Null_Refinement (E) then
                     for C of Iter (Refinement_Constituents (E)) loop
                        Expand (C);
                     end loop;
                  end if;
               else
                  for C of Iter (Part_Of_Constituents (E)) loop
                     if Is_Visible (C, S) then
                        Expand (C);
                     end if;
                  end loop;

                  P.Insert (E);
               end if;
            end;

         else
            P.Insert (E);
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
      Scop : constant Entity_Id := Scope (E);

   begin
      --  For E to occur in the Initializes contract, it must be declared
      --  immediately within its enclosing package (or its body).

      if Ekind (Scop) = E_Package then
         declare
            M : constant Dependency_Maps.Map :=
              Parse_Initializes (Scop, Get_Flow_Scope (Scop));

            State : constant Entity_Id := Encapsulating_State (E);

            Target_Ent : constant Entity_Id :=
              (if Present (State) and then Scope (E) = Scope (State)
               then State
               else Unique_Entity (E)); --  ??? why unique entity?

            --  What we are searching for. Either the entity itself, or,
            --  if this entity is a constituent of an abstract state of
            --  its immediately enclosing package, that abstract state.

         begin
            for Initialized_Var in M.Iterate loop
               declare
                  F : Flow_Id renames Dependency_Maps.Key (Initialized_Var);

               begin
                  --  The package whose state variable E is known by an
                  --  Entity_Id must itself be known by an Entity_Id, but the
                  --  left-hand sides of its Initializes aspect might include
                  --  objects from the package body that are promoted to
                  --  implicit abstract states.
                  pragma Assert (F.Kind in Direct_Mapping
                                         | Magic_String
                                         | Null_Value);

                  if F.Kind = Direct_Mapping
                    and then Get_Direct_Mapping_Id (F) = Target_Ent
                  then
                     return Target_Ent;
                  end if;
               end;
            end loop;
         end;

         return Empty;

      --  Otherwise, it comes from a declaration block in the package body
      --  statements or is an arbitrarily placed internal object that comes
      --  from inlining for proof.

      else
         pragma Assert (Ekind (Scop) = E_Block or else Is_Internal (E));

         return Empty;
      end if;
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
               elsif Is_Predefined_Initialized_Entity (Ent) then
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
        (No (Global_N) and then No (Depends_N) and then not Is_Pure (E))

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
