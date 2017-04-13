------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      S P A R K _ D E F I N I T I O N                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                      Copyright (C) 2011-2017, AdaCore                    --
--                   Copyright (C) 2016-2017, Altran UK Limited             --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Strings.Unbounded;           use Ada.Strings.Unbounded;
with Ada.Text_IO;                     use Ada.Text_IO;
with Aspects;                         use Aspects;
with Assumption_Types;                use Assumption_Types;
with Common_Iterators;                use Common_Iterators;
with Elists;                          use Elists;
with Errout;                          use Errout;
with Exp_Util;                        use Exp_Util;
with Gnat2Why.Annotate;               use Gnat2Why.Annotate;
with Gnat2Why_Args;
with Gnat2Why.Assumptions;            use Gnat2Why.Assumptions;
with Gnat2Why.Util;
with Namet;                           use Namet;
with Nlists;                          use Nlists;
with Nmake;                           use Nmake;
with Opt;                             use Opt;
with Restrict;                        use Restrict;
with Rident;                          use Rident;
with Sem_Aux;                         use Sem_Aux;
with Sem_Disp;                        use Sem_Disp;
with Sem_Prag;                        use Sem_Prag;
with Sem_Util;                        use Sem_Util;
with Snames;                          use Snames;
with SPARK_Util.External_Axioms;      use SPARK_Util.External_Axioms;
with SPARK_Util.Types;                use SPARK_Util.Types;
with Stand;                           use Stand;
with Tbuild;
with Uintp;                           use Uintp;
with Urealp;                          use Urealp;

package body SPARK_Definition is

   -----------------------------------------
   -- Marking of Entities in SPARK or Not --
   -----------------------------------------

   --  This pass detects which entities are in SPARK and which are not, based
   --  on the presence of SPARK_Mode pragmas in the source, and the violations
   --  of SPARK restrictions. Entities that are not in SPARK may still be
   --  translated in Why, although differently than entities in SPARK
   --  (variables not in SPARK are still declared in case they appear in Global
   --  contracts).

   --  As definitions of entities may be recursive, this pass follows
   --  references to entities not yet marked to decide whether they are in
   --  SPARK or not. We remember which entities are being marked, to avoid
   --  looping. So an entity may be marked at the point where it is declared,
   --  or at some previous point, because it was referenced from another
   --  entity. (This is specially needed for Itypes and class-wide types, which
   --  may not have an explicit declaration, or one that is attached to the
   --  AST.)

   --  Any violation of SPARK rules results in the current toplevel subprogram
   --  (unit subprogram, or subprogram only contained in packages all the
   --  way to the unit level) to be not in SPARK, as well as everything it
   --  defines locally.

   --  An error is raised if an entity that has a corresponding SPARK_Mode
   --  pragma of On is determined to be not in SPARK.

   --  Each entity is added to the list of entities Entity_List. The
   --  translation will depend on the status (in SPARK or not) of each entity,
   --  and on where the entity is declared (in the current unit or not).

   --  A subprogram spec can be in SPARK even if its body is not in SPARK.

   --  Except for private types and deferred constants, a unique entity is used
   --  for multiple views of the same entity. For example, the entity attached
   --  to a subprogram body or a body stub is not used.

   --  Private types are always in SPARK (except currently record (sub)type
   --  with private part), even if the underlying type is not in SPARK. This
   --  allows operations which do not depend on the underlying type to be in
   --  SPARK, which is the case in client code that does not have access to the
   --  underlying type. Since only the partial view of a private type is used
   --  in the AST (except at the point of declaration of the full view), even
   --  when visibility over the full view is needed, the nodes that need this
   --  full view are treated specially, so that they are in SPARK only if the
   --  most underlying type is in SPARK. This most underlying type is the last
   --  type obtained by taking:
   --  . for a private type, its underlying type
   --  . for a record subtype, its base type
   --  . for any other type, the type itself
   --  until reaching a non-private type that is not a record subtype.

   --  Partial views of deferred constants may be in SPARK even if their full
   --  view is not in SPARK. This is the case if the type of the constant is
   --  in SPARK, while its initializing expression is not.

   -------------------------------------
   -- Adding Entities for Translation --
   -------------------------------------

   Emit_Messages : Boolean := True;
   --  Messages are emitted only if this flag is set

   Current_SPARK_Pragma : Node_Id;
   --  The current applicable SPARK_Mode pragma, if any, to reference in error
   --  messages when a violation is encountered.

   Current_Protected_Type : Entity_Id := Empty;
   --  Set to protected type entity when marking inside the type to detect
   --  internal calls.

   Current_Delayed_Aspect_Type : Entity_Id := Empty;
   --  When processing delayed aspect type (e.g. Predicate) this is set to the
   --  delayed type itself; used to reference the type in the error message.

   Violation_Detected : Boolean;
   --  Set to True when a violation is detected

   Inside_Actions : Boolean;
   --  Set to True when traversing actions (statements introduced by the
   --  compiler inside expressions), which require a special translation.
   --  Those entities are stored in Actions_Entity_Set.

   procedure Initialize;
   --  Initialize internal global variables; must be called before marking next
   --  compilation.

   function SPARK_Pragma_Is (Mode : Opt.SPARK_Mode_Type) return Boolean
   with Global => (Input => (Current_SPARK_Pragma,
                             Current_Delayed_Aspect_Type));
   --  Returns True iff Current_SPARK_Pragma is not Empty, and corresponds to
   --  the given Mode.

   --  There are two possibilities when marking an entity, depending on whether
   --  this is in the context of a toplevel subprogram body or not. In the
   --  first case, violations are directly attached to the toplevel subprogram
   --  entity, and local entities are added or not as a whole, after the
   --  subprogram body has been fully marked. In the second case, violations
   --  are attached to the entity itself, which is directly added to the lists
   --  for translation after marking.

   function SPARK_Pragma_Of_Type (E : Entity_Id) return Node_Id with
     Pre => Is_Type (E);
   --  Return SPARK_Pragma that applies to type E
   --
   --  SPARK_Pragma cannot be directly specified for types nor declare blocks
   --  but comes from the most immediate scope where pragma SPARK_Mode can be
   --  attached. Then, for SPARK_Pragma coming from package entity (either body
   --  or spec) it may be the pragma given for private/statements section.

   Entity_List : Node_Lists.List;
   --  List of entities that should be translated to Why3. This list contains
   --  non-package entities in SPARK and packages with explicit SPARK_Mode =>
   --  On. VCs should be generated only for entities in the current unit. Each
   --  entity may be attached to a declaration or not (for Itypes).

   Entity_Set : Hashed_Node_Sets.Set;
   --  Set of all entities marked so far. It contains entities from both the
   --  current compilation unit and other units.

   Entities_In_SPARK : Hashed_Node_Sets.Set;
   --  Entities in SPARK. An entity is added to this set if, after marking,
   --  no violations where attached to the corresponding scope. Standard
   --  entities are individually added to this set.

   Bodies_In_SPARK : Hashed_Node_Sets.Set;
   --  Unique defining entities whose body is marked in SPARK; for kinds of
   --  entities in this set see the contract of Entity_Body_In_SPARK.

   Bodies_Compatible_With_SPARK : Hashed_Node_Sets.Set;
   --  Unique defining entities for expression functions whose body does not
   --  contain SPARK violations. Entities that are in this set and not in
   --  Bodies_In_SPARK are expression functions that are compatible with
   --  SPARK and subject to SPARK_Mode of Auto. Thus, their body should not
   --  be analyzed for AoRTE, but it can be used as implicit postcondition
   --  for analyzing calls to the function. This ensures that GNATprove treats
   --  similarly a subprogram with an explicit postcondition and an expression
   --  function with an implicit postcondition when they are subject to
   --  SPARK_Mode of Auto.

   Full_Views_Not_In_SPARK : Node_Maps.Map;
   --  Maps type entities in SPARK whose full view was declared in a private
   --  part with SPARK_Mode => Off or a subtype or derived type of such an
   --  entity to its first ancester in SPARK.

   Delayed_Type_Aspects : Node_Maps.Map;
   --  Stores subprograms from aspects of types whose analysis should be
   --  delayed until the end of the analysis and maps them either to their
   --  SPARK_Mode entity if there is one or to their type entity in discovery
   --  mode.

   Loop_Entity_Set : Hashed_Node_Sets.Set;
   --  Set of entities defined in loops before the invariant, which may require
   --  a special translation. See gnat2why.ads for details.

   Actions_Entity_Set : Hashed_Node_Sets.Set;
   --  Set of entities defined in actions which require a special translation.
   --  See gnat2why.ads for details.

   function Entity_In_SPARK (E : Entity_Id) return Boolean
     renames Entities_In_SPARK.Contains;

   function Entity_Marked (E : Entity_Id) return Boolean
     renames Entity_Set.Contains;

   function Entity_Body_In_SPARK (E : Entity_Id) return Boolean
     renames Bodies_In_SPARK.Contains;

   function Entity_Body_Compatible_With_SPARK (E : Entity_Id) return Boolean
     renames Bodies_Compatible_With_SPARK.Contains;

   function Full_View_Not_In_SPARK (E : Entity_Id) return Boolean
     renames Full_Views_Not_In_SPARK.Contains;

   function Is_Loop_Entity (E : Entity_Id) return Boolean
     renames Loop_Entity_Set.Contains;

   function Is_Actions_Entity (E : Entity_Id) return Boolean
     renames Actions_Entity_Set.Contains;

   procedure Discard_Underlying_Type (T : Entity_Id);
   --  Mark T's underlying type as seen and store T as its partial view

   ------------------------------
   -- Body_Statements_In_SPARK --
   ------------------------------

   function Body_Statements_In_SPARK (E : Entity_Id) return Boolean is
   begin
      if Entity_Body_In_SPARK (E) then
         declare
            Prag : constant Node_Id :=
              SPARK_Aux_Pragma (Defining_Entity (Package_Body (E)));
         begin
            return
              (if Present (Prag)
               then Get_SPARK_Mode_From_Annotation (Prag) /= Off);
         end;
      else
         return False;
      end if;
   end Body_Statements_In_SPARK;

   --------------------------
   -- Entity_Spec_In_SPARK --
   --------------------------

   function Entity_Spec_In_SPARK (E : Entity_Id) return Boolean is
      Prag : constant Node_Id := SPARK_Pragma (E);

   begin
      return
        Present (Prag) and then
        Get_SPARK_Mode_From_Annotation (Prag) = Opt.On;
   end Entity_Spec_In_SPARK;

   ---------------------------
   -- Private_Spec_In_SPARK --
   ---------------------------

   function Private_Spec_In_SPARK (E : Entity_Id) return Boolean is
   begin
      return
        Entity_Spec_In_SPARK (E) and then
        Get_SPARK_Mode_From_Annotation (SPARK_Aux_Pragma (E)) /= Off;
   end Private_Spec_In_SPARK;

   ----------------------
   -- SPARK Violations --
   ----------------------

   procedure Mark_Unsupported
     (Msg        : String;
      N          : Node_Id;
      Extra_Name : Name_Id := No_Name;
      Extra_Num  : Uint    := No_Uint;
      Extra_Node : Node_Id := Empty;
      Cont_Msg   : String  := "")
   with
     Pre => (Extra_Name /= No_Name) = (for some C of Msg => C = '%') and then
            (Extra_Num  /= No_Uint) = (for some C of Msg => C = '^') and then
            (Extra_Node /= Empty)   = (for some C of Msg => C = '}'),
     Global => (Output => Violation_Detected,
                Input  => Current_SPARK_Pragma);
   --  Mark node N as an unsupported SPARK construct. An error message is
   --  issued if current SPARK_Mode is On.
   --
   --  Extra parameters correspond to special characters in the Msg string and
   --  precondition (which is slightly less restrictive than it should) checks
   --  that they are set correctly.
   --
   --  Cont_Msg is a continuous message when specified.

   procedure Mark_Violation
     (Msg           : String;
      N             : Node_Id;
      SRM_Reference : String := "")
   with Global => (Output => Violation_Detected,
                   Input  => Current_SPARK_Pragma);
   --  Mark node N as a violation of SPARK. An error message pointing to the
   --  current SPARK_Mode pragma/aspect is issued if current SPARK_Mode is On.
   --  If SRM_Reference is set, the reference to the SRM is appended to the
   --  error message.

   procedure Mark_Violation
     (N    : Node_Id;
      From : Entity_Id)
   with Global => (Output => Violation_Detected,
                   Input  => Current_SPARK_Pragma);
   --  Mark node N as a violation of SPARK, due to the use of entity From which
   --  is not in SPARK. An error message is issued if current SPARK_Mode is On.

   procedure Mark_Violation_In_Tasking
     (N : Node_Id)
   with Pre => not Is_SPARK_Tasking_Configuration,
        Global => (Output => Violation_Detected,
                   Input  => Current_SPARK_Pragma);
   --  Mark node N as a violation of SPARK because of unsupported tasking
   --  configuration. An error message is issued if current SPARK_Mode is On.

   procedure Mark_Violation_Of_SPARK_Mode (N : Node_Id)
   with Global => (Input => (Current_SPARK_Pragma,
                             Current_Delayed_Aspect_Type));
   --  Issue an error continuation message for node N with the location of the
   --  violated SPARK_Mode pragma/aspect.

   Ravenscar_Profile_Result : Boolean := False;
   --  This switch memoizes the result of Ravenscar_Profile function calls for
   --  improved efficiency. Valid only if Ravenscar_Profile_Cached is True.
   --  Note: if this switch is ever set True, it is never turned off again.

   Ravenscar_Profile_Cached : Boolean := False;
   --  This flag is set to True if the Ravenscar_Profile_Result contains the
   --  correct cached result of Ravenscar_Profile calls.

   function GNATprove_Tasking_Profile return Boolean;
   --  Tests if configuration pragmas and restrictions corresponding to the
   --  tasking profile supported by the GNATprove (which is in the middle
   --  between the Ravenscar profile and GNAT Extended Ravenscar profile) are
   --  currently in effect (set by pragma Profile or by an appropriate set of
   --  individual Restrictions pragmas). Returns True only if all the required
   --  settings are set.

   function Sequential_Elaboration return Boolean;
   --  Check if Partition_Elaboration_Policy is set to Sequential

   function Is_SPARK_Tasking_Configuration return Boolean;
   --  Check tasking configuration required by SPARK and possibly mark
   --  violation on node N.

   ------------------------------------
   -- Is_SPARK_Tasking_Configuration --
   ------------------------------------

   function Is_SPARK_Tasking_Configuration return Boolean is
     (GNATprove_Tasking_Profile and then Sequential_Elaboration);

   ----------------------
   -- Inhibit_Messages --
   ----------------------

   procedure Inhibit_Messages is
   begin
      --  This procedure can be called only once, before the marking itself
      pragma Assert (Emit_Messages and then Entity_Set.Is_Empty);

      Emit_Messages := False;
   end Inhibit_Messages;

   -------------------------------
   -- GNATprove_Tasking_Profile --
   -------------------------------

   --  Check that the current settings match those in
   --  Sem_Prag.Set_Ravenscar_Profile.
   --  ??? Older versions of Ada are also supported to ease reuse once this
   --  code is moved to Restrict package.

   function GNATprove_Tasking_Profile return Boolean is
      Prefix_Entity   : Entity_Id;
      Selector_Entity : Entity_Id;
      Prefix_Node     : Node_Id;
      Node            : Node_Id;

      Profile : Profile_Data renames Profile_Info (GNAT_Extended_Ravenscar);
      --  A minimal settings required for tasking constructs to be allowed in
      --  SPARK.

      function Restriction_No_Dependence (Unit : Node_Id) return Boolean;
      --  Check if restriction No_Dependence is set for Unit.

      -------------------------------
      -- Restriction_No_Dependence --
      -------------------------------

      function Restriction_No_Dependence (Unit : Node_Id) return Boolean is
         function Same_Unit (U1, U2 : Node_Id) return Boolean;
         --  Returns True iff U1 and U2 represent the same library unit. Used
         --  for handling of No_Dependence => Unit restriction case.
         --  ??? This duplicates the code from Restrict package.

         ---------------
         -- Same_Unit --
         ---------------

         function Same_Unit (U1, U2 : Node_Id) return Boolean is
         begin
            if Nkind (U1) = N_Identifier and then Nkind (U2) = N_Identifier
            then
               return Chars (U1) = Chars (U2);

            elsif Nkind (U1) in N_Selected_Component | N_Expanded_Name and then
                  Nkind (U2) in N_Selected_Component | N_Expanded_Name
            then
               return Same_Unit (Prefix (U1), Prefix (U2))
                 and then
                   Same_Unit (Selector_Name (U1), Selector_Name (U2));
            else
               return False;
            end if;
         end Same_Unit;

      --  Start of processing for Restriction_No_Dependence

      begin
         --  Loop to look for entry

         for J in No_Dependences.First .. No_Dependences.Last loop

            --  Entry is in table

            if Same_Unit (Unit, No_Dependences.Table (J).Unit) then
               return True;
            end if;

         end loop;

         --  Entry is not in table

         return False;
      end Restriction_No_Dependence;

   --  Start of processing for Ravenscar_Profile

   begin
      if Ravenscar_Profile_Cached then
         return Ravenscar_Profile_Result;

      else
         Ravenscar_Profile_Result := True;
         Ravenscar_Profile_Cached := True;

         --  pragma Task_Dispatching_Policy (FIFO_Within_Priorities)

         if Task_Dispatching_Policy /= 'F' then
            Ravenscar_Profile_Result := False;
            return False;
         end if;

         --  pragma Locking_Policy (Ceiling_Locking)

         if Locking_Policy /= 'C' then
            Ravenscar_Profile_Result := False;
            return False;
         end if;

         --  pragma Detect_Blocking

         if not Detect_Blocking then
            Ravenscar_Profile_Result := False;
            return False;
         end if;

         declare
            R : Restriction_Flags  renames Profile.Set;
            V : Restriction_Values renames Profile.Value;
         begin
            for J in R'Range loop
               if R (J)
                 and then (Restrictions.Set (J) = False
                             or else Restriction_Warnings (J)
                             or else
                               (J in All_Parameter_Restrictions
                                  and then Restrictions.Value (J) > V (J)))
               then
                  if (J in No_Implicit_Task_Allocations |
                           No_Implicit_Protected_Object_Allocations
                      and then Restrictions.Set (No_Implicit_Heap_Allocations))
                    or else
                     (J = Pure_Barriers
                      and then Restrictions.Set (Simple_Barriers))
                  then
                     null;
                  else
                     Ravenscar_Profile_Result := False;
                     return False;
                  end if;
               end if;
            end loop;
         end;

         --  The following No_Dependence restrictions:
         --    No_Dependence => Ada.Asynchronous_Task_Control
         --    No_Dependence => Ada.Calendar
         --    No_Dependence => Ada.Task_Attributes
         --  are already checked by the above loop.

         --  The following restrictions were added to Ada 2005:
         --    No_Dependence => Ada.Execution_Time.Group_Budget
         --    No_Dependence => Ada.Execution_Time.Timers

         if Ada_Version >= Ada_2005 then

            Name_Buffer (1 .. 3) := "ada";
            Name_Len := 3;

            Prefix_Entity := Make_Identifier (No_Location, Name_Find);

            Name_Buffer (1 .. 14) := "execution_time";
            Name_Len := 14;

            Selector_Entity := Make_Identifier (No_Location, Name_Find);

            Prefix_Node :=
              Make_Selected_Component
                (Sloc          => No_Location,
                 Prefix        => Prefix_Entity,
                 Selector_Name => Selector_Entity);

            Name_Buffer (1 .. 13) := "group_budgets";
            Name_Len := 13;

            Selector_Entity := Make_Identifier (No_Location, Name_Find);

            Node :=
              Make_Selected_Component
                (Sloc          => No_Location,
                 Prefix        => Prefix_Node,
                 Selector_Name => Selector_Entity);

            if not Restriction_No_Dependence (Unit => Node) then
               Ravenscar_Profile_Result := False;
               return False;
            end if;

            Name_Buffer (1 .. 6) := "timers";
            Name_Len := 6;

            Selector_Entity := Make_Identifier (No_Location, Name_Find);

            Node :=
              Make_Selected_Component
                (Sloc          => No_Location,
                 Prefix        => Prefix_Node,
                 Selector_Name => Selector_Entity);

            if not Restriction_No_Dependence (Unit => Node) then
               Ravenscar_Profile_Result := False;
               return False;
            end if;

         end if;

         --  The following restriction was added to Ada 2005:
         --    No_Dependence => System.Multiprocessors.Dispatching_Domains

         if Ada_Version >= Ada_2012 then

            Name_Buffer (1 .. 6) := "system";
            Name_Len := 6;

            Prefix_Entity := Make_Identifier (No_Location, Name_Find);

            Name_Buffer (1 .. 15) := "multiprocessors";
            Name_Len := 15;

            Selector_Entity := Make_Identifier (No_Location, Name_Find);

            Prefix_Node :=
              Make_Selected_Component
                (Sloc          => No_Location,
                 Prefix        => Prefix_Entity,
                 Selector_Name => Selector_Entity);

            Name_Buffer (1 .. 19) := "dispatching_domains";
            Name_Len := 19;

            Selector_Entity := Make_Identifier (No_Location, Name_Find);

            Node :=
              Make_Selected_Component
                (Sloc          => No_Location,
                 Prefix        => Prefix_Node,
                 Selector_Name => Selector_Entity);

            if not Restriction_No_Dependence (Unit => Node) then
               Ravenscar_Profile_Result := False;
               return False;
            end if;

         end if;

         return True;
      end if;
   end GNATprove_Tasking_Profile;

   ----------------------------
   -- Sequential_Elaboration --
   ----------------------------

   function Sequential_Elaboration
     return Boolean is (Partition_Elaboration_Policy = 'S');

   ----------------------------------
   -- Recursive Marking of the AST --
   ----------------------------------

   procedure Mark (N : Node_Id);
   --  Generic procedure for marking code

   function In_SPARK (E : Entity_Id) return Boolean;
   --  Returns whether the entity E is in SPARK; computes this information by
   --  calling Mark_Entity, which is very cheap.

   function Retysp_In_SPARK (E : Entity_Id) return Boolean with
     Pre => Is_Type (E);
   --  Returns whether the representive type of the entity E is in SPARK;
   --  computes this information by calling Mark_Entity, which is very cheap.
   --  Theoretically, it is equivalent to In_SPARK (Retyps (E)) except that
   --  Retysp can only be called on Marked entities

   procedure Mark_Entity (E : Entity_Id);
   --  Push entity E on the stack, mark E, and pop E from the stack. Always
   --  adds E to the set of Entity_Set as a result. If no violation was
   --  detected, E is added to the Entities_In_SPARK.

   --  Marking of declarations

   procedure Mark_Number_Declaration          (N : Node_Id);
   procedure Mark_Object_Declaration          (N : Node_Id);

   procedure Mark_Package_Body                (N : Node_Id);
   procedure Mark_Package_Declaration         (N : Node_Id);

   procedure Mark_Concurrent_Type_Declaration (N : Node_Id);
   --  Mark declarations of concurrent types

   procedure Mark_Protected_Body              (N : Node_Id);
   --  Mark bodies of protected types

   procedure Mark_Subprogram_Body             (N : Node_Id);
   --  Mark bodies of functions, procedures, task types and entries

   procedure Mark_Subprogram_Declaration      (N : Node_Id);
   --  N is either a subprogram declaration node, or a subprogram body node
   --  for those subprograms which do not have a prior declaration (not
   --  counting a stub as a declaration); it works also for entry and task
   --  type declarations.

   --  Special treatment for marking some kinds of nodes
   --  ??? Do we want preconditions on these? For example
   --  Mark_Identifier_Or_Expanded_Name on N_Entry_Body is wrong but does
   --  not fail.

   procedure Mark_Attribute_Reference         (N : Node_Id);
   procedure Mark_Binary_Op                   (N : Node_Id);

   procedure Mark_Call                        (N : Node_Id) with
     Pre => Nkind (N) in N_Subprogram_Call | N_Entry_Call_Statement;

   procedure Mark_Component_Declaration       (N : Node_Id);
   procedure Mark_Handled_Statements          (N : Node_Id);
   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id);
   procedure Mark_If_Expression               (N : Node_Id);
   procedure Mark_If_Statement                (N : Node_Id);
   procedure Mark_Iteration_Scheme            (N : Node_Id);
   procedure Mark_Pragma                      (N : Node_Id);
   procedure Mark_Simple_Return_Statement     (N : Node_Id);
   procedure Mark_Extended_Return_Statement   (N : Node_Id);
   procedure Mark_Subtype_Indication          (N : Node_Id);
   procedure Mark_Unary_Op                    (N : Node_Id);

   procedure Mark_Stmt_Or_Decl_List           (L : List_Id);
   --  Mark a list of statements and declarations, and register any pragma
   --  Annotate (GNATprove) which may be part of that list.

   procedure Mark_Aspect_Clauses_And_Pragmas_In_List (L : List_Id);
   --  Mark only pragmas and aspect clauses in a list of statements and
   --  declarations. Do not register pragmas Annotate (GNATprove) which are
   --  part of that list.

   procedure Mark_Actions (N : Node_Id; L : List_Id);
   --  Mark a possibly null list of actions L from expression N. It should be
   --  called before the expression to which the actions apply is marked, so
   --  that declarations of constants in actions are possibly marked in SPARK.

   procedure Mark_List (L : List_Id);
   --  Call Mark on all nodes in list L

   procedure Mark_Most_Underlying_Type_In_SPARK (Id : Entity_Id; N : Node_Id);
   --  The most underlying type for type Id should be in SPARK, otherwise mark
   --  node N as not in SPARK.

   function Emit_Warning_Info_Messages return Boolean is
     (Emit_Messages and then Gnat2Why_Args.Limit_Subp = Null_Unbounded_String);
   --  Emit warning/info messages only when messages should be emitted, and
   --  analysis is not restricted to a single subprogram/line (typically during
   --  interactive use in IDEs), to avoid reporting messages on pieces of code
   --  not belonging to the analyzed subprogram/line.

   -----------------------------
   -- Discard_Underlying_Type --
   -----------------------------

   procedure Discard_Underlying_Type (T : Entity_Id) is
      U : constant Entity_Id := Underlying_Type (T);
   begin
      if U /= T then
         Entity_Set.Include (U);
         if not Is_Full_View (U) then
            Set_Partial_View (U, T);
         end if;
      end if;
   end Discard_Underlying_Type;

   ---------------------------------
   -- Get_First_Ancestor_In_SPARK --
   ---------------------------------

   function Get_First_Ancestor_In_SPARK (E : Entity_Id) return Entity_Id is
     (Full_Views_Not_In_SPARK.Element (E));

   --------------------
   -- Get_SPARK_JSON --
   --------------------

   function Get_SPARK_JSON return JSON_Array is
      SPARK_Status_JSON : JSON_Array := Empty_Array;

   begin
      --  ??? iterating over all entities is not efficient, but we do it only
      --  once. Perhaps iteration over hierarchical Entity_Tree would allow to
      --  skip entities from non-main unit and those whose parent is not in
      --  SPARK. However, Entity_Tree does not contain protected types (maybe
      --  it should?) while we want to generate SPARK status for them (maybe
      --  we should not?).

      for E of Entity_List loop
         --  Only add infomation for an entity if analysis is requested for it.
         --  Then, absence of errors in flow and warnings in proof for it can
         --  be interpreted as a correct flow analysis or proof for it.

         if Ekind (E) in Entry_Kind       |
                         E_Function       |
                         E_Procedure      |
                         E_Package        |
                         E_Protected_Type |
                         E_Task_Type
           and then Analysis_Requested (E, With_Inlined => True)
         then
            declare
               V : constant JSON_Value := To_JSON (Entity_To_Subp (E));

               SPARK_Status : constant String :=
                 (if Entity_Body_In_SPARK (E)
                  then "all"
                  elsif Entity_Spec_In_SPARK (E)
                  then
                    (if Ekind (E) = E_Package and then No (Package_Body (E))
                     then "all"
                     else "spec")
                  else "no");
            begin
               Set_Field (V, "spark", SPARK_Status);
               Append (SPARK_Status_JSON, V);
            end;

         elsif Is_Type (E)
           and then Needs_Default_Checks_At_Decl (E)
           and then Analysis_Requested (E, With_Inlined => True)
         then

            --  If the entity is a record or private type with fields hidden
            --  from SPARK, then the default initialization was not verified.

            pragma Assert (Entity_In_SPARK (E));

            declare
               V            : constant JSON_Value :=
                 To_JSON (Entity_To_Subp (E));
               SPARK_Status : constant String :=
                 (if (Has_Record_Type (E) or else Has_Private_Type (E))
                       and then
                     Has_Private_Fields (E)
                  then "no"
                  else "all");
            begin
               Set_Field (V, "spark", SPARK_Status);
               Append (SPARK_Status_JSON, V);
            end;
         end if;
      end loop;

      return SPARK_Status_JSON;
   end Get_SPARK_JSON;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin
      Current_SPARK_Pragma := Empty;
      Violation_Detected := False;
      Inside_Actions := False;
   end Initialize;

   --------------
   -- In_SPARK --
   --------------

   function In_SPARK (E : Entity_Id) return Boolean is
   begin
      Mark_Entity (E);
      return Entities_In_SPARK.Contains (E);
   end In_SPARK;

   ----------
   -- Mark --
   ----------

   procedure Mark (N : Node_Id) is

      -----------------------
      -- Local subprograms --
      -----------------------

      function Is_Update_Aggregate (Aggr : Node_Id) return Boolean;
      --  Detect whether Aggr is an aggregate node modelling 'Update. Returns
      --  false for a normal aggregate.

      function Is_Update_Unconstr_Multidim_Aggr (Aggr : Node_Id) return Boolean
      with Pre => Is_Update_Aggregate (N);
      --  Detect whether a 'Update aggregate is an update of an
      --  unconstrained multidimensional array.

      function Is_Special_Multidim_Update_Aggr (Aggr : Node_Id) return Boolean;
      --  Detect special case of AST node.
      --  For an 'Update of a multidimensional array, the indexed components
      --    (the expressions (1, 1), (2, 2) and (3, 3) in example
      --     Arr_A2D'Update ((1, 1) => 1,  (2, 2) => 2, (3, 3) => 3,
      --     where Arr_A2D is a two-dimensional array)
      --  are modelled in the AST using an aggregate node which does not have a
      --  a type. An aggregate node is expected to have a type, but this kind
      --  of expression (indexed components) is not, so need to detect special
      --  case here.
      --  Why aren't these kind of nodes Indexed_Components instead?

      procedure Check_Loop_Invariant_Placement
        (Stmts : List_Id;
         Nested : Boolean := False);
      --  Checks that no non-scalar object declaration appears before the
      --  last loop-invariant or variant in a loop's list of statements. Also
      --  stores scalar objects declared before the last loop-invariant in
      --  Loop_Entity_Set. Nested should be true when checking statements
      --  coming from a nested construct of the loop (if, case, extended
      --  return statements and nested loops).

      ------------------------------------
      -- Check_Loop_Invariant_Placement --
      ------------------------------------

      procedure Check_Loop_Invariant_Placement
        (Stmts  : List_Id;
         Nested : Boolean := False) is

         use Node_Lists;

         Loop_Stmts : constant Node_Lists.List :=
           Get_Flat_Statement_And_Declaration_List (Stmts);
         Inv_Found  : Boolean := Nested;
         --  We only call Check_Loop_Invariant_Placement on nested list of
         --  statements if an invariant has been found.

      begin
         for N of reverse Loop_Stmts loop

            if not Inv_Found then

               --  Find last loop invariant/variant from the loop

               if Is_Pragma_Check (N, Name_Loop_Invariant)
                 or else Is_Pragma (N, Pragma_Loop_Variant)
               then
                  Inv_Found := True;
               end if;

            else
               --  Check that there are no non-scalar objects declarations
               --  before the last invariant/variant.

               case Nkind (N) is
                  when N_Full_Type_Declaration
                     | N_Private_Extension_Declaration
                     | N_Private_Type_Declaration
                     | N_Subtype_Declaration
                  =>
                     declare
                        E : constant Entity_Id := Defining_Entity (N);
                     begin
                        if Is_Scalar_Type (E) then
                           Loop_Entity_Set.Insert (E);
                        end if;
                     end;

                  when N_Object_Declaration =>
                     if Is_Scalar_Type (Etype (Defining_Entity (N))) then
                        --  Store scalar entities defined in loops before the
                        --  invariant in Loop_Entity_Set

                        Loop_Entity_Set.Include (Defining_Entity (N));
                     else
                        Mark_Unsupported
                          ("non-scalar object declared before loop-invariant",
                           N);
                     end if;

                  when N_Package_Declaration =>
                     Mark_Unsupported
                       ("nested packages before loop-invariant", N);

                  when N_Subprogram_Declaration
                     | N_Subprogram_Body
                  =>
                     Mark_Unsupported
                       ("nested subprogram before loop-invariant", N);

                  --  Go inside if, case, exended return statements and
                  --  nested loops to check for absence of non-scalar
                  --  object declarations.

                  when N_If_Statement =>
                     Check_Loop_Invariant_Placement
                       (Then_Statements (N), True);
                     declare
                        Cur : Node_Id := First (Elsif_Parts (N));
                     begin
                        while Present (Cur) loop
                           Check_Loop_Invariant_Placement
                             (Then_Statements (Cur), True);
                           Next (Cur);
                        end loop;
                     end;
                     Check_Loop_Invariant_Placement
                       (Else_Statements (N), True);

                  when N_Case_Statement =>
                     declare
                        Cases : constant List_Id := Alternatives (N);
                        Cur   : Node_Id := First (Cases);
                     begin
                        while Present (Cur) loop
                           Check_Loop_Invariant_Placement
                             (Statements (Cur), True);
                           Next (Cur);
                        end loop;
                     end;

                  when N_Extended_Return_Statement =>
                     Check_Loop_Invariant_Placement
                       (Return_Object_Declarations (N), True);
                     Check_Loop_Invariant_Placement
                       (Statements (Handled_Statement_Sequence (N)), True);

                  when N_Loop_Statement =>
                     Check_Loop_Invariant_Placement (Statements (N), True);

                  when others => null;
               end case;
            end if;
         end loop;
      end Check_Loop_Invariant_Placement;

      -------------------------
      -- Is_Update_Aggregate --
      -------------------------

      function Is_Update_Aggregate (Aggr : Node_Id) return Boolean is
         Par : Node_Id;
      begin
         if Nkind (Aggr) = N_Aggregate then
            Par := Parent (Aggr);

            if Present (Par)
              and then Nkind (Par) = N_Attribute_Reference
              and then Get_Attribute_Id
                         (Attribute_Name (Par)) = Attribute_Update
            then
               return True;
            end if;
         end if;

         return False;
      end Is_Update_Aggregate;

      --------------------------------------
      -- Is_Update_Unconstr_Multidim_Aggr --
      --------------------------------------

      function Is_Update_Unconstr_Multidim_Aggr
        (Aggr : Node_Id) return Boolean
      is
         Pref_Type : constant Entity_Id := Etype (Prefix (Parent (Aggr)));
      begin
         return Is_Array_Type (Pref_Type)
           and then Number_Dimensions (Pref_Type) > 1
           and then not Is_Static_Array_Type (Pref_Type);
      end Is_Update_Unconstr_Multidim_Aggr;

      -------------------------------------
      -- Is_Special_Multidim_Update_Aggr --
      -------------------------------------

      function Is_Special_Multidim_Update_Aggr
        (Aggr : Node_Id) return Boolean
      is
         Pref, Par, Grand_Par, Grand_Grand_Par : Node_Id;
      begin
         if Nkind (Aggr) = N_Aggregate then
            Par := Parent (Aggr);

            if Present (Par) then
               Grand_Par := Parent (Par);

               if Present (Grand_Par)
                 and then Is_Update_Aggregate (Grand_Par)
               then
                  Grand_Grand_Par := Parent (Grand_Par);
                  Pref := Prefix (Grand_Grand_Par);

                  if Is_Array_Type (Etype (Pref))
                    and then Number_Dimensions (Etype (Pref)) > 1
                  then
                     return True;
                  end if;
               end if;
            end if;
         end if;

         return False;
      end Is_Special_Multidim_Update_Aggr;

   --  Start of processing for Mark

   begin
      --  If present, the type of N should be in SPARK. This also allows
      --  marking Itypes and class-wide types at their first occurrence
      --  (inside In_SPARK).

      --  The Itype may be located in some other unit than the expression, and
      --  a violation of SPARK_Mode on the Itype may mask another violation on
      --  the expression. As we prefer to have the error located on the
      --  expression, we mark the type of the node after the expression.

      --  The type may be absent on kinds of nodes that should have types,
      --  in very special cases, like the fake aggregate node in a 'Update
      --  attribute_reference, and the fake identifier node for an abstract
      --  state. So we also check that the type is explicitly present.

      if Nkind (N) in N_Has_Etype
        and then Present (Etype (N))
        and then Is_Type (Etype (N))
        and then not Retysp_In_SPARK (Etype (N))
      then
         Mark_Violation (N, From => Etype (N));
      end if;

      --  Dispatch on node kind

      case Nkind (N) is

         when N_Abstract_Subprogram_Declaration =>
            Mark_Subprogram_Declaration (N);

         when N_Aggregate =>
            if not Is_Update_Aggregate (N)
              and then not Is_Special_Multidim_Update_Aggr (N)
            then
               Mark_Most_Underlying_Type_In_SPARK (Etype (N), N);
               if not Aggregate_Is_Fully_Initialized (N) then
                  Mark_Violation ("aggregate not fully defined", N,
                                  SRM_Reference => "SPARK RM 4.3");
               end if;
            elsif Is_Update_Aggregate (N)
              and then Is_Update_Unconstr_Multidim_Aggr (N)
            then
               Mark_Unsupported
                 ("attribute % of unconstrained multidimensional array",
                  N, Name_Update);
            end if;
            Mark_List (Expressions (N));
            Mark_List (Component_Associations (N));

         when N_Allocator =>
            Mark_Violation ("allocator", N);

         when N_Assignment_Statement =>
            Mark (Name (N));
            Mark (Expression (N));

         when N_Attribute_Reference =>
            Mark_Attribute_Reference (N);

         when N_Binary_Op =>
            Mark_Binary_Op (N);

         when N_Block_Statement =>
            Mark_Stmt_Or_Decl_List (Declarations (N));
            Mark (Handled_Statement_Sequence (N));

         when N_Case_Expression
            | N_Case_Statement
         =>
            Mark (Expression (N));
            Mark_List (Alternatives (N));

         when N_Case_Expression_Alternative =>
            Mark_Actions (N, Actions (N));
            Mark (Expression (N));

         when N_Case_Statement_Alternative =>
            Mark_Stmt_Or_Decl_List (Statements (N));

         when N_Code_Statement =>
            Mark_Violation ("code statement", N);

         when N_Component_Association =>
            pragma Assert (No (Loop_Actions (N)));
            Mark_List (Choices (N));

            if not Box_Present (N) then
               Mark (Expression (N));
            end if;

         when N_Iterated_Component_Association =>
            Mark_Violation ("iterated associations", N);

         when N_Component_Declaration =>
            Mark_Component_Declaration (N);

         when N_Delay_Relative_Statement
            | N_Delay_Until_Statement
         =>
            Mark (Expression (N));

         when N_Exit_Statement =>
            if Present (Condition (N)) then
               Mark (Condition (N));
            end if;

         when N_Expanded_Name
            | N_Identifier
         =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_Explicit_Dereference =>
            Mark_Violation ("explicit dereference", N);

         when N_Extended_Return_Statement =>
            Mark_Extended_Return_Statement (N);

         when N_Extension_Aggregate =>
            Mark_Most_Underlying_Type_In_SPARK (Etype (N), N);
            if not Aggregate_Is_Fully_Initialized (N) then
               Mark_Violation ("extension aggregate not fully defined", N,
                               SRM_Reference => "SPARK RM 4.3");
            end if;

            if Nkind (Ancestor_Part (N)) in N_Identifier | N_Expanded_Name
              and then Is_Type (Entity (Ancestor_Part (N)))
            then
               --  The ancestor part of an aggregate can be either an
               --  expression or a subtype.
               --  The second case is not currently supported in SPARK.

               Mark_Unsupported
                 ("extension aggregate with subtype ancestor part", N);
            end if;

            Mark (Ancestor_Part (N));
            Mark_List (Expressions (N));
            Mark_List (Component_Associations (N));

         when N_Free_Statement =>
            Mark_Violation ("free statement", N);

         when N_Function_Call =>
            Mark_Call (N);

         when N_Goto_Statement =>
            Mark_Violation ("goto statement", N);

         when N_Handled_Sequence_Of_Statements =>
            Mark_Handled_Statements (N);

         when N_If_Expression =>
            Mark_If_Expression (N);

         when N_If_Statement =>
            Mark_If_Statement (N);

         when N_Indexed_Component =>
            Mark_Most_Underlying_Type_In_SPARK (Etype (Prefix (N)), N);
            Mark (Prefix (N));
            Mark_List (Expressions (N));

         when N_Iterator_Specification =>

            --  Retrieve Iterable aspect specification if any

            declare
               Iterable_Aspect : constant Node_Id :=
                 Find_Aspect (Id => Etype (Name (N)), A => Aspect_Iterable);
            begin

               if Present (Iterable_Aspect) then

                  --  Mark components of the Iterable aggregate

                  declare
                     Iterable_Component_Assoc : constant List_Id :=
                       Component_Associations (Expression
                                                 (Iterable_Aspect));
                     Iterable_Field : Node_Id :=
                       First (Iterable_Component_Assoc);

                  begin

                     --  Nodes in Iterable fields are not rewritten.
                     --  The ultimate alias should be considered.

                     while Present (Iterable_Field) loop
                        Mark_Entity (Ultimate_Alias
                                     (Entity (Expression (Iterable_Field))));
                        Next (Iterable_Field);
                     end loop;

                  end;

                  Mark (Name (N));

               elsif Of_Present (N)
                 and then Has_Array_Type (Etype (Name (N)))
               then
                  if Number_Dimensions (Etype (Name (N))) > 1 then
                     Mark_Unsupported
                       ("iterator specification over array of dimension ^",
                        N,
                        Extra_Num =>
                          UI_From_Int (Number_Dimensions (Etype (Name (N)))));
                  end if;

                  if Present (Subtype_Indication (N)) then
                     Mark (Subtype_Indication (N));
                  end if;
                  Mark (Name (N));

               else

                  --  if no Iterable aspect is found, raise a violation
                  --  other forms of iteration are not allowed in SPARK

                  Mark_Violation ("iterator specification", N,
                                  SRM_Reference => "SPARK RM 5.5.2");
               end if;
            end;

            --  Mark iterator's identifier

            Mark_Entity (Defining_Identifier (N));

         when N_Loop_Statement =>
            Check_Loop_Invariant_Placement (Statements (N));

            --  Mark the entity for the loop, which is used in the translation
            --  phase to generate exceptions for this loop.

            Mark_Entity (Entity (Identifier (N)));

            if Present (Iteration_Scheme (N)) then
               Mark_Iteration_Scheme (Iteration_Scheme (N));
            end if;
            Mark_Stmt_Or_Decl_List (Statements (N));

         when N_Membership_Test =>
            if Is_Array_Type (Etype (Left_Opnd (N))) then
               Mark_Unsupported ("membership test on array values", N);
            end if;

            Mark (Left_Opnd (N));
            if Present (Alternatives (N)) then
               Mark_List (Alternatives (N));
            else
               Mark (Right_Opnd (N));
            end if;

         when N_Null =>
            Mark_Violation ("null", N);

         when N_Number_Declaration =>
            Mark_Number_Declaration (N);

         when N_Object_Declaration =>
            declare
               E : constant Entity_Id := Defining_Entity (N);
            begin
               --  Store correspondence from completions of deferred constants,
               --  so that Is_Full_View can be used for dealing correctly with
               --  deferred constants, when the public part of the package is
               --  marked as SPARK_Mode On, and the private part of the package
               --  is marked as SPARK_Mode Off. This is also used later during
               --  generation of Why.

               if Ekind (E) = E_Constant
                 and then Present (Full_View (E))
               then
                  Set_Partial_View (Full_View (E), E);
               end if;

               Mark_Object_Declaration (N);
            end;

         when N_Package_Body =>
            Mark_Package_Body (N);

         when N_Package_Body_Stub =>
            Mark_Package_Body (Get_Body_From_Stub (N));

         when N_Package_Declaration =>
            Mark_Package_Declaration (N);

         when N_Parameter_Association =>
            Mark (Explicit_Actual_Parameter (N));

         when N_Pragma =>
            Mark_Pragma (N);

         when N_Procedure_Call_Statement =>
            Mark_Call (N);

         when N_Qualified_Expression =>
            Mark (Subtype_Mark (N));
            Mark (Expression (N));

         when N_Quantified_Expression =>
            if Present (Loop_Parameter_Specification (N)) then
               Mark (Discrete_Subtype_Definition
                       (Loop_Parameter_Specification (N)));
            else
               Mark (Iterator_Specification (N));
            end if;
            Mark (Condition (N));

         when N_Raise_Statement =>
            if Present (Expression (N)) then
               Mark (Expression (N));
            end if;

         when N_Raise_xxx_Error =>
            --  The frontend inserts explicit checks during semantic
            --  analysis in some cases, for which GNATprove issues a
            --  corresponding check. Currently, this is only used for
            --  discriminant checks introduced when converting a
            --  discriminant type into another discriminant type, in
            --  which multiple source discriminants are mapped to the
            --  same target discriminant (RM 4.6(43)).

            case RT_Exception_Code'Val (UI_To_Int (Reason (N))) is
               when CE_Discriminant_Check_Failed =>
                  null;
               when others =>
                  Mark_Violation ("raise statement", N);
            end case;

         when N_Raise_Expression =>
            Mark_Violation ("raise expression", N);

         when N_Range =>
            Mark (Low_Bound (N));
            Mark (High_Bound (N));

         when N_Reference =>
            Mark_Violation ("reference", N);

         when N_Short_Circuit =>
            Mark_Actions (N, Actions (N));
            Mark (Left_Opnd (N));
            Mark (Right_Opnd (N));

         when N_Simple_Return_Statement =>
            Mark_Simple_Return_Statement (N);

         when N_Selected_Component =>

            --  In some cases, the static type of the prefix does not contain
            --  the selected component. This may happen for generic instances,
            --  or inlined subprograms, whose body is analyzed in the general
            --  context only. Issue an error in that case.

            declare
               Name        : constant Node_Id   := Prefix (N);
               Selector    : constant Entity_Id := Entity (Selector_Name (N));
               Prefix_Type : constant Entity_Id :=
                 Unique_Entity (Etype (Name));

            begin
               if Is_Access_Type (Prefix_Type) then
                  Mark_Violation ("implicit dereference", N);

               elsif No (Search_Component_By_Name (Prefix_Type, Selector)) then
                  Violation_Detected := True;
                  if SPARK_Pragma_Is (Opt.On) then
                     Apply_Compile_Time_Constraint_Error
                       (N, "component not present in }",
                        CE_Discriminant_Check_Failed,
                        Ent => Prefix_Type, Rep => False);
                  end if;
               end if;
            end;

            --  In most cases, it is enough to look at the record type (the
            --  most underlying one) to see whether the access is in SPARK. An
            --  exception is the access to discrimants to a private type whose
            --  full view is not in SPARK.

            if not Is_Private_Type (Etype (Prefix (N)))
              or else Retysp_In_SPARK (Etype (Prefix (N)))
            then
               Mark_Most_Underlying_Type_In_SPARK (Etype (Prefix (N)), N);
            elsif Ekind (Entity (Selector_Name (N))) /= E_Discriminant then
               Mark_Violation (N, From  => Etype (Prefix (N)));
            end if;

            --  Check if the component is visible in SPARK. If it is not,
            --  report the error on the prefix type to avoid polluting the
            --  output when the type is in a part with SPARK_Mode (On).

            if not Violation_Detected
              and then not Is_Access_Type (Etype (Prefix (N)))
              and then not
                Component_Is_Visible_In_SPARK (Entity (Selector_Name (N)))
            then
               Mark_Violation (N, From  => Etype (Prefix (N)));
            end if;

            Mark (Prefix (N));
            Mark (Selector_Name (N));

         when N_Slice =>
            Mark_Most_Underlying_Type_In_SPARK (Etype (Prefix (N)), N);
            Mark (Prefix (N));
            Mark (Discrete_Range (N));

         when N_Subprogram_Body =>

            --  For expression functions that have a unique declaration, the
            --  body inserted by the frontend may be far from the original
            --  point of declaration, after the private declarations of the
            --  package (to avoid premature freezing.) In those cases, mark the
            --  subprogram body at the same point as the subprogram
            --  declaration, so that entities declared afterwards have access
            --  to the axiom defining the expression function.

            if Present (Get_Expression_Function (Unique_Defining_Entity (N)))
              and then not Comes_From_Source (Original_Node (N))
            then
               null;

            --  In GNATprove_Mode, a separate declaration is usually generated
            --  before the body for a subprogram if not defined by the user
            --  (unless the subprogram defines a unit or has a contract). So
            --  in general Mark_Subprogram_Declaration is always called on the
            --  declaration before Mark_Subprogram_Body is called on the body.
            --  In the remaining cases where a subprogram unit body does not
            --  have a prior declaration, call Mark_Subprogram_Declaration on
            --  the subprogram body.

            else
               if Acts_As_Spec (N) then
                  Mark_Subprogram_Declaration (N);
               end if;

               Mark_Subprogram_Body (N);
            end if;

         when N_Subprogram_Body_Stub =>
            if Is_Subprogram_Stub_Without_Prior_Declaration (N) then
               Mark_Subprogram_Declaration (N);
            end if;
            Mark_Subprogram_Body (Get_Body_From_Stub (N));

         when N_Subprogram_Declaration =>
            Mark_Subprogram_Declaration (N);

            --  For expression functions that have a unique declaration, the
            --  body inserted by the frontend may be far from the original
            --  point of declaration, after the private declarations of the
            --  package (to avoid premature freezing). In those cases, mark the
            --  subprogram body at the same point as the subprogram
            --  declaration, so that entities declared afterwards have access
            --  to the axiom defining the expression function.

            declare
               E      : constant Entity_Id := Defining_Entity (N);
               Body_N : constant Node_Id := Subprogram_Body (E);
            begin
               if Present (Get_Expression_Function (E))
                 and then not Comes_From_Source (Original_Node (Body_N))
               then
                  Mark_Subprogram_Body (Body_N);
               end if;
            end;

         when N_Subtype_Indication =>
            Mark_Subtype_Indication (N);

         when N_Type_Conversion
            | N_Unchecked_Type_Conversion
         =>
            --  Source unchecked type conversion nodes were rewritten as such
            --  by SPARK_Rewrite.Rewrite_Call, keeping the original call to an
            --  instance of Unchecked_Conversion as the Original_Node of the
            --  new N_Unchecked_Type_Conversion node, and marking the node as
            --  coming from source. We translate this original node to Why, so
            --  it should be in SPARK too.

            if Nkind (N) = N_Unchecked_Type_Conversion
              and then Comes_From_Source (N)
            then
               declare
                  Orig_N : constant Node_Id := Original_Node (N);
               begin
                  pragma Assert (Nkind (Orig_N) = N_Function_Call
                                   and then Is_Entity_Name (Name (Orig_N))
                                   and then Is_Unchecked_Conversion_Instance
                                     (Entity (Name (Orig_N))));

                  Mark (Orig_N);
               end;

            --  Otherwise, this is a type conversion that does not come from an
            --  unchecked conversion in the source. Check various limitations
            --  of GNATprove and issue an error on unsupported conversions.

            elsif Has_Array_Type (Etype (N)) then
               declare
                  Target_Comp_Typ : constant Entity_Id :=
                    Retysp (Component_Type (Retysp (Etype (N))));
                  Source_Comp_Typ : constant Entity_Id :=
                    Retysp (Component_Type (Retysp (Etype (Expression (N)))));
               begin
                  if Target_Comp_Typ /= Source_Comp_Typ then
                     Mark_Unsupported
                       ("conversion between array types "
                        & "that have different element types", N);
                  end if;
               end;

               --  Restrict array conversions to the cases where either:
               --  - corresponding indices have modular types of the same size
               --  - or both don't have a modular type.
               --  Supporting other cases of conversions would require
               --  generating conversion functions for each required pair of
               --  array types and index base types.

               declare
                  Target_Index : Node_Id :=
                    First_Index (Retysp (Etype (N)));

                  Source_Type_Retysp : constant Entity_Id :=
                    Retysp (Etype (Expression (N)));
                  --  SPARK representation of the type of source expression

                  Source_Index : Node_Id :=
                    First_Index
                      (if Ekind (Source_Type_Retysp) = E_String_Literal_Subtype
                       then Retysp (Etype (Source_Type_Retysp))
                       else Source_Type_Retysp);
                  --  Special case string literals, since First_Index cannot be
                  --  directly called for them.

                  Dim          : constant Pos :=
                    Number_Dimensions (Retysp (Etype (N)));
                  Target_Type  : Entity_Id;
                  Source_Type  : Entity_Id;

               begin
                  for I in 1 .. Dim loop
                     Target_Type := Etype (Target_Index);
                     Source_Type := Etype (Source_Index);

                     if Has_Modular_Integer_Type (Target_Type)
                          and then
                        Has_Modular_Integer_Type (Source_Type)
                     then
                        if Esize (Target_Type) /= Esize (Source_Type) then
                           Mark_Unsupported
                             ("this conversion between array types", N);
                           exit;
                        end if;

                     elsif Has_Modular_Integer_Type (Target_Type)
                             or else
                           Has_Modular_Integer_Type (Source_Type)
                     then
                        Mark_Unsupported
                          ("this conversion between array types", N);
                        exit;
                     end if;

                     Target_Index := Next_Index (Target_Index);
                     Source_Index := Next_Index (Source_Index);
                  end loop;
               end;

            elsif Has_Floating_Point_Type (Etype (N))
                    and then
                  Has_Fixed_Point_Type (Etype (Expression (N)))
            then
               Mark_Unsupported
                 ("conversion from fixed-point to floating-point", N);

            elsif Has_Fixed_Point_Type (Etype (N))
                    and then
                  Has_Fixed_Point_Type (Etype (Expression (N)))
            then
               declare
                  Target_Root_Type : constant Entity_Id :=
                    Root_Type (Etype (N));
                  Expr : constant Node_Id := Expression (N);

                  --  The multiplication and division operations on fixed-point
                  --  types have a return type of universal_fixed (with no
                  --  bounds), which is used as an overload resolution trick to
                  --  allow free conversion between certain real types on the
                  --  result of multiplication or division. Use the fixed-point
                  --  type of one of the operands as the source type for the
                  --  conversion.

                  Expr_Type : constant Entity_Id :=
                    (if Nkind (Expr) in N_Op_Multiply | N_Op_Divide
                       and then Etype (Expr) = Universal_Fixed
                     then
                       (if Has_Fixed_Point_Type (Etype (Left_Opnd (Expr))) then
                          Etype (Left_Opnd (Expr))
                        else
                          Etype (Right_Opnd (Expr)))
                     else
                       Etype (Expr));
                  Source_Root_Type : constant Entity_Id :=
                    Root_Type (Expr_Type);
               begin
                  if Target_Root_Type /= Source_Root_Type then
                     Mark_Unsupported
                       ("conversion between different fixed-point types", N);
                  end if;
               end;
            end if;

            Mark (Expression (N));

         when N_Unary_Op =>
            Mark_Unary_Op (N);

         when N_Variant_Part =>
            declare
               Var : Node_Id := First (Variants (N));
            begin
               while Present (Var) loop
                  Mark (Var);
                  Next (Var);
               end loop;
            end;

         --  Frontend sometimes declares an Itype for the base type of a type
         --  declaration. This Itype should be marked at the point of
         --  declaration of the corresponding type, otherwise it may end up
         --  being marked multiple times in various client units, which leads
         --  to multiple definitions in Why3 for the same type.

         when N_Full_Type_Declaration
            | N_Private_Extension_Declaration
            | N_Private_Type_Declaration
            | N_Subtype_Declaration
         =>
            declare
               E  : constant Entity_Id := Defining_Entity (N);
               BT : constant Entity_Id := Base_Type (E);

            begin

               --  Store correspondence from completions of private types, so
               --  that Is_Full_View can be used for dealing correctly with
               --  private types, when the public part of the package is marked
               --  as SPARK_Mode On, and the private part of the package is
               --  marked as SPARK_Mode Off. This is also used later during
               --  generation of Why.

               if Is_Private_Type (E)
                 and then Present (Full_View (E))
                 and then not Is_Full_View (Full_View (E)) -- ??? why needed
               then
                  Set_Partial_View (Full_View (E), E);
               end if;

               --  Fill in the map between classwide types and their
               --  corresponding specific type, in the case of the implicitly
               --  declared classwide type T'Class. Also fill in the map
               --  between primitive operations and their corresponding
               --  tagged type.

               if Ekind (E) in E_Record_Type | E_Record_Subtype
                 and then Is_Tagged_Type (E)
                 and then (if Ekind (E) = E_Record_Subtype then
                               not (Present (Cloned_Subtype (E))))
                 and then not Is_Class_Wide_Type (E)
                 and then not Is_Itype (E)
               then
                  Set_Specific_Tagged (Class_Wide_Type (E), E);

                  --  Only mark the classwide type associated to a record type
                  --  if the record type isn't constrained. Otherwise, the
                  --  classwide type is not in SPARK and should not be used.

                  if not Has_Discriminants (E)
                    or else not Is_Constrained (E)
                  then
                     Mark_Entity (Class_Wide_Type (E));
                  end if;
               end if;

               Mark_Entity (E);

               if Is_Itype (BT) then
                  Mark_Entity (BT);
               end if;
            end;

         when N_Task_Type_Declaration
            | N_Protected_Type_Declaration
         =>

            --  Pick SPARK_Mode from the concurrent type definition

            declare
               Save_SPARK_Pragma : constant Node_Id :=
                 Current_SPARK_Pragma;
               E                 : constant Entity_Id := Defining_Entity (N);
            begin
               Current_SPARK_Pragma := SPARK_Pragma (E);
               Mark_Entity (E);

               Mark_Concurrent_Type_Declaration (N);

               Current_SPARK_Pragma := Save_SPARK_Pragma;
            end;

         --  Supported tasking constructs

         when N_Protected_Body
            | N_Task_Body
         =>
            if Is_SPARK_Tasking_Configuration then
                  case Nkind (N) is
                     when N_Protected_Body =>
                        Mark_Protected_Body (N);

                     when N_Task_Body =>
                        Mark_Subprogram_Body (N);

                     when others =>
                        raise Program_Error;

                  end case;
            else
               Mark_Violation_In_Tasking (N);
            end if;

         when N_Protected_Body_Stub
            | N_Task_Body_Stub
         =>
            if Is_SPARK_Tasking_Configuration then
               Mark (Get_Body_From_Stub (N));
            else
               Mark_Violation_In_Tasking (N);
            end if;

         when N_Entry_Body =>
            Mark_Subprogram_Body (N);

         when N_Entry_Call_Statement =>
            if Is_SPARK_Tasking_Configuration then
               --  This might be either protected entry or protected subprogram
               --  call.
               Mark_Call (N);
            else
               Mark_Violation_In_Tasking (N);
            end if;

         when N_Entry_Declaration =>
            Mark_Subprogram_Declaration (N);

         --  Unsupported tasking constructs

         when N_Abort_Statement
            | N_Accept_Statement
            | N_Asynchronous_Select
            | N_Conditional_Entry_Call
            | N_Requeue_Statement
            | N_Selective_Accept
            | N_Timed_Entry_Call
         =>
            Mark_Violation ("tasking", N);

         --  The following kinds can be safely ignored by marking

         when N_At_Clause
            | N_Attribute_Definition_Clause
            | N_Character_Literal
            | N_Enumeration_Representation_Clause
            | N_Exception_Declaration
            | N_Exception_Renaming_Declaration
            | N_Formal_Object_Declaration
            | N_Formal_Package_Declaration
            | N_Formal_Subprogram_Declaration
            | N_Formal_Type_Declaration
            | N_Freeze_Entity
            | N_Freeze_Generic_Entity
            | N_Function_Instantiation
            | N_Generic_Function_Renaming_Declaration
            | N_Generic_Package_Declaration
            | N_Generic_Package_Renaming_Declaration
            | N_Generic_Procedure_Renaming_Declaration
            | N_Generic_Subprogram_Declaration
            | N_Implicit_Label_Declaration
            | N_Incomplete_Type_Declaration
            | N_Itype_Reference
            | N_Label
            | N_Null_Statement
            | N_Operator_Symbol
            | N_Others_Choice
            | N_Package_Instantiation
            | N_Package_Renaming_Declaration
            | N_Procedure_Instantiation
            | N_Record_Representation_Clause
            | N_String_Literal
            | N_Subprogram_Renaming_Declaration
            | N_Use_Package_Clause
            | N_With_Clause
            | N_Use_Type_Clause
            | N_Validate_Unchecked_Conversion
         =>
            null;

         when N_Real_Literal
            | N_Integer_Literal
         =>
            --  If a literal is the result of the front-end
            --  rewriting a static attribute, then we mark
            --  the original node.
            if not Comes_From_Source (N)
              and then Is_Rewrite_Substitution (N)
              and then Nkind (Original_Node (N)) = N_Attribute_Reference
            then
               Mark_Attribute_Reference (Original_Node (N));
            end if;

         --  Object renamings are rewritten by expansion, but they are kept in
         --  the tree, so just ignore them.

         when N_Object_Renaming_Declaration =>
            null;

         --  The following nodes are rewritten by semantic analysis

         when N_Expression_Function
            | N_Single_Protected_Declaration
            | N_Single_Task_Declaration
         =>
            raise Program_Error;

         --  The following nodes are never generated in GNATprove mode

         when N_Expression_With_Actions
            | N_Compound_Statement
            | N_Unchecked_Expression
         =>
            raise Program_Error;

         --  Mark should not be called on other kinds

         when N_Abortable_Part
            | N_Accept_Alternative
            | N_Access_Definition
            | N_Access_Function_Definition
            | N_Access_Procedure_Definition
            | N_Access_To_Object_Definition
            | N_Aspect_Specification
            | N_Compilation_Unit
            | N_Compilation_Unit_Aux
            | N_Component_Clause
            | N_Component_Definition
            | N_Component_List
            | N_Constrained_Array_Definition
            | N_Contract
            | N_Decimal_Fixed_Point_Definition
            | N_Defining_Character_Literal
            | N_Defining_Identifier
            | N_Defining_Operator_Symbol
            | N_Defining_Program_Unit_Name
            | N_Delay_Alternative
            | N_Delta_Constraint
            | N_Derived_Type_Definition
            | N_Designator
            | N_Digits_Constraint
            | N_Discriminant_Association
            | N_Discriminant_Specification
            | N_Function_Specification
            | N_Iteration_Scheme
            | N_Loop_Parameter_Specification
            | N_Elsif_Part
            | N_Empty
            | N_Entry_Body_Formal_Part
            | N_Enumeration_Type_Definition
            | N_Entry_Call_Alternative
            | N_Entry_Index_Specification
            | N_Error
            | N_Exception_Handler
            | N_Floating_Point_Definition
            | N_Formal_Decimal_Fixed_Point_Definition
            | N_Formal_Derived_Type_Definition
            | N_Formal_Discrete_Type_Definition
            | N_Formal_Floating_Point_Definition
            | N_Formal_Incomplete_Type_Definition
            | N_Formal_Modular_Type_Definition
            | N_Formal_Ordinary_Fixed_Point_Definition
            | N_Formal_Private_Type_Definition
            | N_Formal_Signed_Integer_Type_Definition
            | N_Generic_Association
            | N_Index_Or_Discriminant_Constraint
            | N_Mod_Clause
            | N_Modular_Type_Definition
            | N_Ordinary_Fixed_Point_Definition
            | N_Parameter_Specification
            | N_Pragma_Argument_Association
            | N_Package_Specification
            | N_Procedure_Specification
            | N_Protected_Definition
            | N_Push_Pop_xxx_Label
            | N_Range_Constraint
            | N_Real_Range_Specification
            | N_Record_Definition
            | N_SCIL_Dispatch_Table_Tag_Init
            | N_SCIL_Dispatching_Call
            | N_SCIL_Membership_Test
            | N_Signed_Integer_Type_Definition
            | N_Subunit
            | N_Target_Name
            | N_Task_Definition
            | N_Terminate_Alternative
            | N_Triggering_Alternative
            | N_Unconstrained_Array_Definition
            | N_Unused_At_Start
            | N_Unused_At_End
            | N_Variant
            | N_Delta_Aggregate
         =>
            raise Program_Error;
      end case;
   end Mark;

   ------------------
   -- Mark_Actions --
   ------------------

   procedure Mark_Actions (N : Node_Id; L : List_Id) is
      function Acceptable_Actions (L : List_Id) return Boolean;
      --  Return whether L is a list of acceptable actions, which can be
      --  translated into Why.

      ------------------------
      -- Acceptable_Actions --
      ------------------------

      function Acceptable_Actions (L : List_Id) return Boolean is
         N : Node_Id;

      begin
         N := First (L);
         while Present (N) loop
            --  Only actions that consist in N_Object_Declaration nodes for
            --  constants are translated. All types are accepted and
            --  corresponding effects (for bounds of dynamic types) discarded
            --  when translating to Why.

            case Nkind (N) is
               when N_Subtype_Declaration
                  | N_Full_Type_Declaration
               =>
                  null;

               when N_Object_Declaration =>
                  if Constant_Present (N) then
                     null;
                  else
                     return False;
                  end if;

               when N_Null_Statement
                  | N_Freeze_Entity
               =>
                  null;

               when N_Pragma =>
                  if Is_Ignored_Pragma_Check (N) then
                     null;
                  else
                     return False;
                  end if;

               when others =>
                  return False;
            end case;

            Next (N);
         end loop;

         return True;
      end Acceptable_Actions;

      Save_Inside_Actions : constant Boolean := Inside_Actions;

   --  Start of processing for Mark_Actions

   begin
      Inside_Actions := True;

      Mark_List (L);
      if Emit_Messages
        and then SPARK_Pragma_Is (Opt.On)
        and then not Acceptable_Actions (L)
      then

         --  We should never reach here, but in case we do, we issue an
         --  understandable error message pointing to the source of the
         --  too complex actions.

         Error_Msg_N ("too complex actions inserted in expression", N);
      end if;

      Inside_Actions := Save_Inside_Actions;
   end Mark_Actions;

   ---------------------------------------------
   -- Mark_Aspect_Clauses_And_Pragmas_In_List --
   ---------------------------------------------

   procedure Mark_Aspect_Clauses_And_Pragmas_In_List (L : List_Id) is
      Cur : Node_Id := First (L);

   begin
      --  Only mark pragmas and aspect clauses. Do not mark GNATprove annotate
      --  pragmas here.

      while Present (Cur) loop
         if Nkind (Cur) in N_Pragma | N_Representation_Clause
           and then not Is_Pragma_Annotate_GNATprove (Cur)
         then
            Mark (Cur);
         end if;
         Next (Cur);
      end loop;
   end Mark_Aspect_Clauses_And_Pragmas_In_List;

   ------------------------------
   -- Mark_Attribute_Reference --
   ------------------------------

   procedure Mark_Attribute_Reference (N : Node_Id) is
      Aname   : constant Name_Id      := Attribute_Name (N);
      P       : constant Node_Id      := Prefix (N);
      Exprs   : constant List_Id      := Expressions (N);
      Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);

   begin
      --  This case statement must agree with the table specified in SPARK RM
      --  15.2 "Language Defined Attributes".
      --
      --  See also the analysis in Gnat2Why.Expr.Transform_Attr which defines
      --  which of these attributes are supported in proof.
      case Attr_Id is

         --  Support special aspects defined in SPARK
         when Attribute_Loop_Entry =>
            null;

         --  Support a subset of the attributes defined in Ada RM. These are
         --  the attributes marked "Yes" in SPARK RM 15.2.
         when Attribute_Adjacent       |
           Attribute_Aft               |
           Attribute_Body_Version      |
           Attribute_Callable          |
           Attribute_Caller            |
           Attribute_Ceiling           |
           Attribute_Class             |
           Attribute_Constrained       |
           Attribute_Copy_Sign         |
           Attribute_Definite          |
           Attribute_Delta             |
           Attribute_Denorm            |
           Attribute_Digits            |
           Attribute_First             |
           Attribute_First_Valid       |
           Attribute_Floor             |
           Attribute_Fore              |
           Attribute_Image             |
           Attribute_Last              |
           Attribute_Last_Valid        |
           Attribute_Length            |
           Attribute_Machine           |
           Attribute_Machine_Emax      |
           Attribute_Machine_Emin      |
           Attribute_Machine_Mantissa  |
           Attribute_Machine_Overflows |
           Attribute_Machine_Radix     |
           Attribute_Machine_Rounding  |
           Attribute_Machine_Rounds    |
           Attribute_Max               |
           Attribute_Min               |
           Attribute_Mod               |
           Attribute_Model             |
           Attribute_Model_Emin        |
           Attribute_Model_Epsilon     |
           Attribute_Model_Mantissa    |
           Attribute_Model_Small       |
           Attribute_Modulus           |
           Attribute_Old               |
           Attribute_Partition_ID      |
           Attribute_Pos               |
           Attribute_Pred              |
           Attribute_Range             |
           Attribute_Remainder         |
           Attribute_Result            |
           Attribute_Round             |
           Attribute_Rounding          |
           Attribute_Safe_First        |
           Attribute_Safe_Last         |
           Attribute_Scale             |
           Attribute_Scaling           |
           Attribute_Small             |
           Attribute_Succ              |
           Attribute_Terminated        |
           Attribute_Truncation        |
           Attribute_Unbiased_Rounding |
           Attribute_Update            |
           Attribute_Val               |
           Attribute_Value             |
           Attribute_Version           |
           Attribute_Wide_Image        |
           Attribute_Wide_Value        |
           Attribute_Wide_Width        |
           Attribute_Wide_Wide_Image   |
           Attribute_Wide_Wide_Value   |
           Attribute_Wide_Wide_Width   |
           Attribute_Width             =>
            null;

         --  These attributes are supported, but generate a warning in
         --  "pedantic" mode, owing to their implemention-defined status.
         --  These are the attributes marked "Warn" in SPARK RM 15.2.
         when Attribute_Alignment   |
           Attribute_Bit_Order      |
           Attribute_Component_Size |
           Attribute_First_Bit      |
           Attribute_Last_Bit       |
           Attribute_Position       |
           Attribute_Size           =>
            if Emit_Warning_Info_Messages
              and then SPARK_Pragma_Is (Opt.On)
              and then Gnat2Why_Args.Pedantic
            then
               Error_Msg_Name_1 := Aname;
               Error_Msg_N
                 ("?attribute % has an implementation-defined value", N);
            end if;

         when Attribute_Valid =>
            if Emit_Warning_Info_Messages
              and then SPARK_Pragma_Is (Opt.On)
            then
               Error_Msg_F ("?attribute Valid is assumed to return True", N);
            end if;

         when others =>
            Violation_Detected := True;
            if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
               Error_Msg_Name_1 := Aname;
               Error_Msg_N ("attribute % is not permitted in SPARK", N);
            end if;
            return;
      end case;

      Mark (P);
      Mark_List (Exprs);
   end Mark_Attribute_Reference;

   --------------------
   -- Mark_Binary_Op --
   --------------------

   procedure Mark_Binary_Op (N : Node_Id) is
   begin
      --  Only support for now multiplication and division operations on
      --  fixed-point types if both arguments and the result have the same
      --  base type, or one of the arguments is an integer type.

      if Nkind (N) in N_Op_Multiply | N_Op_Divide then
         declare
            L_Type : constant Entity_Id := Base_Type (Etype (Left_Opnd (N)));
            R_Type : constant Entity_Id := Base_Type (Etype (Right_Opnd (N)));

            --  The multiplication and division operations on fixed-point
            --  types have a return type of universal_fixed (with no
            --  bounds), which is used as an overload resolution trick to
            --  allow free conversion between certain real types on the
            --  result of multiplication or division. Use the fixed-point
            --  type of one of the operands as the source type for the
            --  conversion.

            Expr_Type : constant Entity_Id :=
              (if Etype (N) = Universal_Fixed then
                 Etype (Parent (N))
               else
                 Etype (N));
            E_Type : constant Entity_Id := Base_Type (Expr_Type);
         begin
            if Is_Fixed_Point_Type (L_Type)
                 and then
               Is_Fixed_Point_Type (R_Type)
                 and then
               L_Type /= R_Type
            then
               Mark_Unsupported
                 ("operation between different fixed-point types", N);

            elsif (Is_Fixed_Point_Type (L_Type)
                     and then
                   Is_Floating_Point_Type (R_Type))
                     or else
                  (Is_Fixed_Point_Type (R_Type)
                     and then
                   Is_Floating_Point_Type (L_Type))
            then
               Mark_Unsupported
                 ("operation between fixed-point type and universal real", N);

            elsif (Is_Fixed_Point_Type (L_Type) and then L_Type /= E_Type)
                     or else
                  (Is_Fixed_Point_Type (R_Type) and then R_Type /= E_Type)
            then
               --  Support division of fixed-point values with integer result

               if Nkind (N) = N_Op_Divide
                 and then Is_Fixed_Point_Type (L_Type)
                 and then Is_Fixed_Point_Type (R_Type)
                 and then Is_Integer_Type (E_Type)
               then
                  null;
               else
                  Mark_Unsupported ("operation on fixed-point type"
                                    & " with non-integer result type", N);
               end if;
            end if;
         end;
      end if;

      --  In pedantic mode, issue a warning whenever an arithmetic operation
      --  could be reordered by the compiler, like "A + B - C", as a given
      --  ordering may overflow and another may not. Not that a warning is
      --  issued even on operations like "A * B / C" which are not reordered
      --  by GNAT, as they could be reordered according to RM 4.5/13.

      if Gnat2Why_Args.Pedantic

        --  Ignore code defined in the standard library, unless the main unit
        --  is from the standard library. In particular, ignore code from
        --  instances of generics defined in the standard library (unless we
        --  are analyzing the standard library itself). As a result, no warning
        --  is generated in this case for standard library code. Such warnings
        --  are only noise, because a user sets the strict SPARK mode precisely
        --  when he uses another compiler than GNAT, with a different
        --  implementation of the standard library.

        and then
          (not Location_In_Standard_Library (Sloc (N))
            or else Unit_In_Standard_Library (Main_Unit))
      then
         case N_Binary_Op'(Nkind (N)) is
            when N_Op_Add | N_Op_Subtract =>
               if Emit_Warning_Info_Messages
                 and then SPARK_Pragma_Is (Opt.On)
                 and then Nkind (Left_Opnd (N)) in N_Op_Add | N_Op_Subtract
                 and then Paren_Count (Left_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Left_Opnd (N));
               end if;

               if Emit_Warning_Info_Messages
                 and then SPARK_Pragma_Is (Opt.On)
                 and then Nkind (Right_Opnd (N)) in N_Op_Add | N_Op_Subtract
                 and then Paren_Count (Right_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Right_Opnd (N));
               end if;

            when N_Op_Multiply | N_Op_Divide | N_Op_Mod | N_Op_Rem =>
               if Emit_Warning_Info_Messages
                 and then SPARK_Pragma_Is (Opt.On)
                 and then Nkind (Left_Opnd (N)) in N_Multiplying_Operator
                 and then Paren_Count (Left_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Left_Opnd (N));
               end if;

               if Emit_Warning_Info_Messages
                 and then SPARK_Pragma_Is (Opt.On)
                 and then Nkind (Right_Opnd (N)) in N_Multiplying_Operator
                 and then Paren_Count (Right_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Right_Opnd (N));
               end if;

            when others =>
               null;
         end case;
      end if;

      Mark (Left_Opnd (N));
      Mark (Right_Opnd (N));
   end Mark_Binary_Op;

   ---------------
   -- Mark_Call --
   ---------------

   procedure Mark_Call (N : Node_Id) is
      E : Entity_Id;
      --  Entity of the called subprogram or entry

      function Is_Volatile_Call (Target : Entity_Id) return Boolean;
      --  Returns True iff call to Target is volatile

      ----------------------
      -- Is_Volatile_Call --
      ----------------------

      function Is_Volatile_Call (Target : Entity_Id) return Boolean is
        (if Current_Protected_Type = Scope (Target) then
           --  This is an internal call to protected function
           Is_Enabled_Pragma (Get_Pragma (Target, Pragma_Volatile_Function))
         else
           Is_Volatile_Function (Target));

      procedure Mark_Param (Formal : Entity_Id; Actual : Node_Id);
      --  Mark actuals of the call

      ----------------
      -- Mark_Param --
      ----------------

      procedure Mark_Param
        (Formal : Entity_Id;
         Actual : Node_Id) is
      begin
         --  Special checks for effectively volatile calls and objects
         if Comes_From_Source (Actual)
           and then
             (Is_Effectively_Volatile_Object (Actual)
              or else (Nkind (Actual) = N_Function_Call
                       and then Nkind (Name (Actual)) /= N_Explicit_Dereference
                       and then Is_Volatile_Call (Get_Called_Entity (Actual))))
         then
            --  An effectively volatile object may act as an actual when the
            --  corresponding formal is of a non-scalar effectively volatile
            --  type (SPARK RM 7.1.3(11)).

            if not Is_Scalar_Type (Etype (Formal))
              and then Is_Effectively_Volatile (Etype (Formal))
            then
               null;

            --  An effectively volatile object may act as an actual in a call
            --  to an instance of Unchecked_Conversion. (SPARK RM 7.1.3(11)).

            elsif Is_Unchecked_Conversion_Instance (E) then
               null;

            else
               Mark_Violation
                 (Msg           =>
                    "volatile " &
                  (if Nkind (Actual) = N_Function_Call
                     then "function call"
                     else "object") & " as actual",
                  N             => Actual,
                  SRM_Reference => "7.1.3(11)");
            end if;
         end if;

         --  Regular checks
         Mark (Actual);
      end Mark_Param;

      procedure Mark_Actuals is new Iterate_Call_Parameters (Mark_Param);

   --  Start processing for Mark_Call

   begin
      if Nkind (Name (N)) = N_Explicit_Dereference then
         --  Indirect calls are not in SPARK
         Mark_Violation
           ("call through access to " &
            (case Nkind (N) is
                  when N_Procedure_Call_Statement => "procedure",
                  when N_Function_Call            => "function",
                  when others                     => raise Program_Error),
            N);

         return;

      else
         E := Get_Called_Entity (N);
      end if;

      --  External calls to non-library-level objects are not yet supported
      if Ekind (Scope (E)) = E_Protected_Type
        and then Is_External_Call (N)
      then
         declare
            Obj : constant Entity_Id :=
              Get_Enclosing_Object (Prefix (Name (N)));
         begin
            case Ekind (Obj) is
               when Formal_Kind =>
                  Mark_Unsupported
                    ("call to operation of a formal protected parameter", N);
                  return;

               --  External calls prefixed with library-level objects are fine

               when E_Variable =>
                  null;

               when others =>
                  raise Program_Error;
            end case;
         end;
      end if;

      --  Similar limitation for suspending on suspension objects
      if Suspends_On_Suspension_Object (E) then
         case Ekind (Get_Enclosing_Object (First_Actual (N))) is
            when Formal_Kind =>
               Mark_Unsupported ("suspension on a formal parameter", N);
               return;

            --  Suspension on library-level objects is fine

            when E_Variable =>
               null;

            when others =>
               raise Program_Error;
         end case;
      end if;

      --  Current_Protected_Type is either empty or points to what is says
      pragma Assert (Present (Scope (E)));

      if Ekind (E) in E_Function
        and then not Is_OK_Volatile_Context (Context => Parent (N),
                                             Obj_Ref => N)
        and then Is_Volatile_Call (E)
      then
         Mark_Violation ("call to a volatile function in interfering context",
                         N);
         return;
      end if;

      Mark_Actuals (N);

      --  Call is in SPARK only if the subprogram called is in SPARK

      if not In_SPARK (E) then
         Mark_Violation (N,
                         From => (if Ekind (E) = E_Function
                                    and then Is_Predicate_Function (E)
                                  then Etype (First_Formal (E))
                                  else E));

      elsif Nkind (N) in N_Subprogram_Call
        and then Present (Controlling_Argument (N))
        and then Is_Invisible_Dispatching_Operation (E)
      then
         Mark_Violation
           ("dispatching call on primitive of untagged private", N);

      --  There should not be calls to default initial condition and invariant
      --  procedures.

      elsif Subprogram_Is_Ignored_For_Proof (E) then
         raise Program_Error;

      --  Warn about calls to predefined and imported subprograms with no
      --  manually-written Global or Depends contracts. Exempt calls to pure
      --  subprograms (because Pure acts as "Global => null").

      elsif Emit_Warning_Info_Messages
        and then SPARK_Pragma_Is (Opt.On)
        and then not Has_User_Supplied_Globals (E)
        and then ((Is_Imported (E) and then
                     Convention (E) not in Convention_Ada)
                  or else In_Internal_Unit (E))
        and then not Is_Pure (E)
      then
         Error_Msg_NE
           ("?no Global contract available for &", N, E);
         Error_Msg_NE
           ("\\assuming & has no effect on global items", N, E);
      end if;
   end Mark_Call;

   ---------------------------
   -- Mark_Compilation_Unit --
   ---------------------------

   procedure Mark_Compilation_Unit (N : Node_Id) is
      CU        : constant Node_Id := Parent (N);
      Context_N : Node_Id;

      use type Node_Lists.Cursor;

   begin
      --  Avoid rewriting generic units which are only preanalyzed, which may
      --  cause rewriting to fail, as this is not needed.

      if Is_Generic_Unit (Unique_Defining_Entity (N)) then
         return;
      end if;

      Initialize;

      --  Separately mark declarations from Standard as in SPARK or not

      if Defining_Entity (N) = Standard_Standard then
         return;
      end if;

      --  Mark entities in SPARK or not

      Context_N := First (Context_Items (CU));
      while Present (Context_N) loop
         Mark (Context_N);
         Next (Context_N);
      end loop;

      Mark (N);

      --  Mark delayed type aspects

      --  If no SPARK_Mode is set for the type, we only mark delayed aspects
      --  for types which have been found to be in SPARK. In this case, every
      --  violation is considered an error as we can't easily backtrack the
      --  type to be out of SPARK.

      for Cur in Delayed_Type_Aspects.Iterate loop
         declare
            Delayed_Mapping : Node_Id renames Node_Maps.Element (Cur);

            Mark_Delayed_Aspect : Boolean := False;
         begin
            --  Consider delayed aspects only if type was in a scope marked
            --  SPARK_Mode(On)...

            if Nkind (Delayed_Mapping) = N_Pragma then

               Current_SPARK_Pragma := Delayed_Mapping;

               Mark_Delayed_Aspect := True;

            --  or if the type entity has been found to be in SPARK. In this
            --  case (scope not marked SPARK_Mode(On)), the type entity was
            --  stored as value in the Delayed_Type_Aspects map.

            elsif Entity_In_SPARK (Delayed_Mapping) then
               Current_SPARK_Pragma := Empty;

               Mark_Delayed_Aspect := True;

            else
               Mark_Delayed_Aspect := False;
            end if;

            if Mark_Delayed_Aspect then
               declare
                  --  The subprogram generated by the frontend for
                  --  Default_Initial_Condition is stored as key in
                  --  the Delayed_Type_Aspects map.

                  Subp  : Entity_Id renames Node_Maps.Key (Cur);
                  Expr  : constant Node_Id :=
                    Get_Expr_From_Check_Only_Proc (Subp);
                  Param : constant Entity_Id :=
                    Defining_Entity (First (Parameter_Specifications
                                     (Subprogram_Specification (Subp))));

                  Save_Delayed_Aspect_Type : constant Entity_Id :=
                    Current_Delayed_Aspect_Type;

               begin
                  pragma Assert (Present (Param));

                  Current_Delayed_Aspect_Type := Etype (Param);

                  Mark_Entity (Param);
                  if Present (Expr) then
                     Mark (Expr);
                  end if;

                  Current_Delayed_Aspect_Type := Save_Delayed_Aspect_Type;
               end;
            end if;
         end;
      end loop;

      --  Forget about delayed type aspects once they are processes
      Delayed_Type_Aspects.Clear;

      --  Ensure that global variables are restored to their initial values
      pragma Assert (No (Current_Protected_Type));
      pragma Assert (No (Current_Delayed_Aspect_Type));
   end Mark_Compilation_Unit;

   --------------------------------
   -- Mark_Component_Declaration --
   --------------------------------

   procedure Mark_Component_Declaration (N : Node_Id) is
      Def : constant Node_Id := Component_Definition (N);

   begin
      if Present (Access_Definition (Def)) then
         Mark_Violation ("access type", Def);
      else
         Mark_Subtype_Indication (Subtype_Indication (Def));
      end if;
   end Mark_Component_Declaration;

   --------------------------------------
   -- Mark_Concurrent_Type_Declaration --
   --------------------------------------

   procedure Mark_Concurrent_Type_Declaration (N : Node_Id) is
      E                       : constant Entity_Id := Defining_Entity (N);
      Type_Def                : constant Node_Id :=
        (if Ekind (E) = E_Protected_Type
         then Protected_Definition (N)
         else Task_Definition (N));
      Save_Violation_Detected : constant Boolean := Violation_Detected;

   begin
      Violation_Detected := False;

      if Has_Discriminants (E) then
         declare
            D : Entity_Id := First_Discriminant (E);
         begin
            while Present (D) loop
               Mark_Entity (D);
               Next_Discriminant (D);
            end loop;
         end;
      end if;

      if Present (Type_Def) then
         Mark_Stmt_Or_Decl_List
           (Visible_Declarations (Type_Def));

         declare
            Save_SPARK_Pragma : constant Node_Id :=
              Current_SPARK_Pragma;

         begin
            Current_SPARK_Pragma := SPARK_Aux_Pragma (E);
            if not SPARK_Pragma_Is (Opt.Off) then
               declare
                  Save_Protected_Type : constant Entity_Id :=
                    Current_Protected_Type;

               begin
                  Current_Protected_Type := E;

                  Mark_Stmt_Or_Decl_List
                    (Private_Declarations (Type_Def));

                  Current_Protected_Type :=
                    Save_Protected_Type;
               end;
            end if;

            Current_SPARK_Pragma := Save_SPARK_Pragma;
         end;
      end if;

      Violation_Detected := Save_Violation_Detected;
   end Mark_Concurrent_Type_Declaration;

   -----------------
   -- Mark_Entity --
   -----------------

   procedure Mark_Entity (E : Entity_Id) is

      --  Subprograms for marking specific entities. These are defined locally
      --  so that they cannot be called from other marking subprograms, which
      --  should call Mark_Entity instead.

      procedure Mark_Parameter_Entity (E : Entity_Id)
      with Pre => Ekind (E) in E_Discriminant
                             | E_Loop_Parameter
                             | E_Variable
                             | Formal_Kind;
      --  E is a subprogram or a loop parameter, or a discriminant

      procedure Mark_Number_Entity     (E : Entity_Id);
      procedure Mark_Object_Entity     (E : Entity_Id);
      procedure Mark_Package_Entity    (E : Entity_Id) with
        Pre =>
          Entity_In_Ext_Axioms (E)
            and then Present (Current_SPARK_Pragma)
            and then Current_SPARK_Pragma = SPARK_Pragma (E)
            and then
              Get_SPARK_Mode_From_Annotation (Current_SPARK_Pragma) = On;
      procedure Mark_Subprogram_Entity (E : Entity_Id);
      procedure Mark_Type_Entity       (E : Entity_Id);

      use type Node_Lists.Cursor;

      Current_Concurrent_Insert_Pos : Node_Lists.Cursor;
      --  This variable is set at the start of marking concurrent type and
      --  stores the position on the list where the type itself should be
      --  inserted.
      --
      --  Concurrent types must be inserted into Entity_List before operations
      --  defined in their scope, because these operations take the type as an
      --  implicit argument.

      ------------------------
      -- Mark_Number_Entity --
      ------------------------

      procedure Mark_Number_Entity (E : Entity_Id) is
         N    : constant Node_Id   := Parent (E);
         Expr : constant Node_Id   := Expression (N);
         T    : constant Entity_Id := Etype (E);
      begin
         if not Retysp_In_SPARK (T) then
            Mark_Violation (N, From => T);
         end if;

         if Present (Expr) then
            Mark (Expr);
         end if;
      end Mark_Number_Entity;

      ------------------------
      -- Mark_Object_Entity --
      ------------------------

      procedure Mark_Object_Entity (E : Entity_Id) is
         N        : constant Node_Id   := Parent (E);
         Def      : constant Node_Id   := Object_Definition (N);
         Expr     : constant Node_Id   := Expression (N);
         T        : constant Entity_Id := Etype (E);
         Sub      : constant Entity_Id := Actual_Subtype (E);
         Encap_Id : constant Entity_Id := Encapsulating_State (E);

      begin
         --  A constant object (other than a formal parameter of mode in) shall
         --  not be effectively volatile (SPARK RM 7.1.3(4)). This legality
         --  rule is checked by the frontend for code with SPARK_Mode On, but
         --  needs to be checked here for code with SPARK_Mode Auto.

         if Ekind (E) = E_Constant and then Is_Effectively_Volatile (T) then
            Mark_Violation ("volatile constant", Def);
         end if;

         --  A variable whose Part_Of pragma specifies a single concurrent
         --  type as encapsulator must be (SPARK RM 9.4):
         --    * Of a type that defines full default initialization, or
         --    * Declared with a default value, or
         --    * Imported

         if Present (Encap_Id)
           and then Is_Single_Concurrent_Object (Encap_Id)
           and then Default_Initialization (Etype (E)) not in
             Full_Default_Initialization | No_Possible_Initialization
           and then not Has_Initial_Value (E)
           and then not Is_Imported (E)
         then
            Mark_Violation ("not fully initialized part of " &
                            (if Ekind (Etype (Encap_Id)) = E_Task_Type
                             then "task"
                             else "protected") & " type",
                            Def, SRM_Reference => "SPARK RM 9.4");
         end if;

         --  The object is in SPARK if-and-only-if its type is in SPARK and
         --  its initialization expression, if any, is in SPARK.

         if not Retysp_In_SPARK (T) then
            Mark_Violation (Def, From => T);
         end if;

         if Present (Sub)
           and then not In_SPARK (Sub)
         then
            Mark_Violation (Def, From => Sub);
         end if;

         if Present (Expr) then
            Mark (Expr);
         end if;
      end Mark_Object_Entity;

      -------------------------
      -- Mark_Package_Entity --
      -------------------------

      procedure Mark_Package_Entity (E : Entity_Id) is

         procedure Declare_In_Package_With_External_Axioms (Decls : List_Id);
         --  Mark types, subprograms and objects from a package with external
         --  axioms.

         ---------------------------------------------
         -- Declare_In_Package_With_External_Axioms --
         ---------------------------------------------

         procedure Declare_In_Package_With_External_Axioms (Decls : List_Id) is
            Decl : Node_Id;
            Id   : Entity_Id;
         begin
            Decl := First (Decls);

            --  Declare entities for types

            while Present (Decl) and then not Comes_From_Source (Decl) loop
               if Nkind (Decl) in N_Subtype_Declaration then
                  Id := Defining_Entity (Decl);

                  if Is_Type (Id) then
                     Mark_Entity (Id);
                  end if;
               end if;
               Next (Decl);
            end loop;

            while Present (Decl) loop
               if Nkind (Decl) in N_Package_Declaration then

                  --  Mark elements of sub-packages

                  Declare_In_Package_With_External_Axioms
                    (Visible_Declarations (Specification (Decl)));
               elsif Nkind (Decl) in N_Full_Type_Declaration
                                   | N_Private_Type_Declaration
                                   | N_Private_Extension_Declaration
                                   | N_Subtype_Declaration
                                   | N_Subprogram_Declaration
                                   | N_Object_Declaration
               then
                  Id := Defining_Entity (Decl);

                  if (Is_Type (Id)
                      or else Is_Object (Id)
                      or else Is_Subprogram (Id))
                    and then not Is_Hidden (Id)
                  then

                     --  Should only mark entities that are public.
                     --  Others are simply ignored.

                     Mark_Entity (Id);
                  end if;
               end if;

               Next (Decl);
            end loop;
         end Declare_In_Package_With_External_Axioms;

         --  Local variables

         Spec     : constant Node_Id := Package_Specification (E);
         G_Parent : constant Node_Id := Generic_Parent (Spec);

      --  Start of processing for Mark_Package_Entity

      begin
         --  Do not analyze specs for instantiations of the formal containers.
         --  Only mark types in SPARK or not, and mark all subprograms in
         --  SPARK, but none should be scheduled for translation into Why3.

         --  Packages with external axioms should have SPARK_Mode On;
         --  this is enforced by Entity_In_Ext_Axioms (E).

         --  External_Axiomatization can be given only for non-generic packages

         if Present (G_Parent) then
            Mark_Violation
              ("generic package with External_Axiomatization", G_Parent);
         end if;

         --  Mark types and subprograms from packages with external
         --  axioms as in SPARK or not.

         Declare_In_Package_With_External_Axioms (Visible_Declarations (Spec));

         --  Check that the private part (if any) of a package with
         --  External_Axiomatization has SPARK_Mode => Off.

         if Present (Private_Declarations (Spec)) then
            declare
               Private_Pragma : constant Node_Id := SPARK_Aux_Pragma (E);

            begin
               if Present (Private_Pragma)
                 and then
                   Get_SPARK_Mode_From_Annotation (Private_Pragma) /= Off
               then
                  Mark_Violation
                    ("private part of package with External_Axiomatization",
                     E);
               end if;
            end;
         end if;

         if not Violation_Detected then

            --  Explicitly add the package declaration to the entities to
            --  translate into Why3.

            Entity_List.Append (E);
         end if;
      end Mark_Package_Entity;

      ---------------------------
      -- Mark_Parameter_Entity --
      ---------------------------

      procedure Mark_Parameter_Entity (E : Entity_Id) is
         T : constant Entity_Id := Etype (E);
      begin
         if not Retysp_In_SPARK (T) then
            Mark_Violation (E, From => T);
         end if;
      end Mark_Parameter_Entity;

      ----------------------------
      -- Mark_Subprogram_Entity --
      ----------------------------

      procedure Mark_Subprogram_Entity (E : Entity_Id) is

         procedure Mark_Function_Specification (N : Node_Id);
         --  Mark violations related to impure functions

         procedure Mark_Subprogram_Specification (N : Node_Id);
         --  Mark violations related to parameters, result and contract

         procedure Process_Class_Wide_Condition
           (Expr    : Node_Id;
            Spec_Id : Entity_Id);
         --  Replace the type of all references to the controlling formal of
         --  subprogram Spec_Id found in expression Expr with the corresponding
         --  class-wide type.

         ---------------------------------
         -- Mark_Function_Specification --
         ---------------------------------

         procedure Mark_Function_Specification (N : Node_Id) is
            Id               : constant Entity_Id := Defining_Entity (N);
            Is_Volatile_Func : constant Boolean   := Is_Volatile_Function (Id);
            Params           : constant List_Id   :=
              Parameter_Specifications (N);
            Param            : Node_Id;
            Param_Id         : Entity_Id;

         begin
            --  A nonvolatile function shall not have a result of an
            --  effectively volatile type (SPARK RM 7.1.3(9)).

            if not Is_Volatile_Func
              and then Is_Effectively_Volatile (Etype (Id))
            then
               Mark_Violation
                 ("nonvolatile function with effectively volatile result", Id);
            end if;

            Param := First (Params);
            while Present (Param) loop
               Param_Id := Defining_Identifier (Param);

               --  A nonvolatile function shall not have a formal parameter
               --  of an effectively volatile type (SPARK RM 7.1.3(9)).

               if not Is_Volatile_Func
                 and then Is_Effectively_Volatile (Etype (Param_Id))
               then
                  Mark_Violation
                    ("nonvolatile function with effectively volatile " &
                       "parameter", Id);
               end if;

               --  A function declaration shall not have a
               --  parameter_specification with a mode of OUT or IN OUT
               --  (SPARK RM 6.1(5)).

               case Ekind (Param_Id) is
                  when E_Out_Parameter =>
                     Mark_Violation ("function with OUT parameter", Id);

                  when E_In_Out_Parameter =>
                     Mark_Violation ("function with `IN OUT` parameter", Id);

                  when others =>
                     null;
               end case;

               Next (Param);
            end loop;

            --  If the result type of a subprogram is not in SPARK, then the
            --  subprogram is not in SPARK.

            if not Retysp_In_SPARK (Etype (Id)) then
               Mark_Violation (Id, From => Etype (Id));
            end if;
         end Mark_Function_Specification;

         -----------------------------------
         -- Mark_Subprogram_Specification --
         -----------------------------------

         procedure Mark_Subprogram_Specification (N : Node_Id) is

            procedure Mark_Global_Items (Subp_Items : Elist_Id);
            --  Mark global inputs or outputs of the subprogram

            -----------------------
            -- Mark_Global_Items --
            -----------------------

            procedure Mark_Global_Items (Subp_Items : Elist_Id) is
            begin
               for Item of Iter (Subp_Items) loop
                  declare
                     Item_Id : constant Entity_Id :=
                       (if Nkind (Item) = N_Defining_Identifier
                        then Item
                        else Entity_Of (Item));
                  begin
                     if Present (Item_Id) then
                        Mark_Entity (if From_Limited_With (Item_Id)
                                     then Non_Limited_View (Item_Id)
                                     else Item_Id);
                     end if;
                  end;
               end loop;
            end Mark_Global_Items;

            Id         : constant Entity_Id := Defining_Entity (N);
            Formals    : constant List_Id   := Parameter_Specifications (N);
            Param_Spec : Node_Id;
            Formal     : Entity_Id;

            --  Variables for collecting the subprogram's inputs and outputs
            Subp_Inputs  : Elist_Id := No_Elist;
            Subp_Outputs : Elist_Id := No_Elist;
            Global_Seen  : Boolean;
            pragma Unreferenced (Global_Seen);

         --  Start of processing for Mark_Subprogram_Specification

         begin
            case Ekind (Id) is
               when E_Function =>
                  Mark_Function_Specification (N);

               when E_Entry_Family =>
                  Mark_Violation ("entry family", N);

               when others =>
                  null;
            end case;

            Param_Spec := First (Formals);
            while Present (Param_Spec) loop
               Formal := Defining_Identifier (Param_Spec);
               if not In_SPARK (Formal) then
                  Mark_Violation (Formal, From => Etype (Formal));
               end if;
               Next (Param_Spec);
            end loop;

            --  Mark global items that appear in Global and Depends contracts,
            --  so that they get translated to Why3, even if this is the only
            --  occurrence of these variables/states.

            Collect_Subprogram_Inputs_Outputs
              (Id, False, Subp_Inputs, Subp_Outputs, Global_Seen);
            Mark_Global_Items (Subp_Inputs);
            Mark_Global_Items (Subp_Outputs);
         end Mark_Subprogram_Specification;

         ----------------------------------
         -- Process_Class_Wide_Condition --
         ----------------------------------

         procedure Process_Class_Wide_Condition
           (Expr    : Node_Id;
            Spec_Id : Entity_Id)
         is
            Disp_Typ : constant Entity_Id :=
              Sem_Disp.Find_Dispatching_Type (Spec_Id);

            function Replace_Type (N : Node_Id) return Traverse_Result;
            --  Within the expression for a Pre'Class or Post'Class aspect for
            --  a primitive subprogram of a tagged type Disp_Typ, a name that
            --  denotes a formal parameter of type Disp_Typ is treated as
            --  having type Disp_Typ'Class. This is used to create a suitable
            --  pre- or postcondition expression for analyzing dispatching
            --  calls.

            ------------------
            -- Replace_Type --
            ------------------

            function Replace_Type (N : Node_Id) return Traverse_Result is
               Context : constant Node_Id    := Parent (N);
               Loc     : constant Source_Ptr := Sloc (N);
               CW_Typ  : Entity_Id := Empty;
               Ent     : Entity_Id;
               Typ     : Entity_Id;

            begin
               if Is_Entity_Name (N)
                 and then Present (Entity (N))
                 and then Is_Formal (Entity (N))
               then
                  Ent := Entity (N);
                  Typ := Etype (Ent);

                  if Nkind (Context) = N_Type_Conversion then
                     null;

                  --  Do not perform the type replacement for selector names
                  --  in parameter associations. These carry an entity for
                  --  reference purposes, but semantically they are just
                  --  identifiers.

                  elsif Nkind (Context) = N_Parameter_Association
                    and then Selector_Name (Context) = N
                  then
                     null;

                  elsif Typ = Disp_Typ then
                     CW_Typ := Class_Wide_Type (Typ);
                  end if;

                  if Present (CW_Typ) then
                     Rewrite (N,
                       Nmake.Make_Type_Conversion (Loc,
                         Subtype_Mark =>
                           Tbuild.New_Occurrence_Of (CW_Typ, Loc),
                         Expression   => Tbuild.New_Occurrence_Of (Ent, Loc)));
                     Set_Etype (N, CW_Typ);

                     --  When changing the type of an argument to a potential
                     --  dispatching call, make the call dispatching indeed by
                     --  setting its controlling argument.

                     if Nkind (Parent (N)) = N_Function_Call
                       and then Nkind (Name (Context)) in N_Has_Entity
                       and then Present (Entity (Name (Context)))
                       and then
                         Is_Dispatching_Operation (Entity (Name (Context)))
                     then
                        Set_Controlling_Argument (Context, N);
                     end if;
                  end if;
               end if;

               return OK;
            end Replace_Type;

            procedure Replace_Types is new Traverse_Proc (Replace_Type);

         --  Start of processing for Process_Class_Wide_Condition

         begin
            Replace_Types (Expr);
         end Process_Class_Wide_Condition;

         Prag : Node_Id;
         Expr : Node_Id;

      --  Start of processing for Mark_Subprogram_Entity

      begin
         Mark_Subprogram_Specification (if Ekind (E) in Entry_Kind
                                        then Parent (E)
                                        else Subprogram_Specification (E));

         Prag := (if Present (Contract (E))
                  then Pre_Post_Conditions (Contract (E))
                  else Empty);

         while Present (Prag) loop
            Expr :=
              Get_Pragma_Arg (First (Pragma_Argument_Associations (Prag)));

            --  Postconditions of protected subprograms declared in protected
            --  type declarations are executed as part of protected operations,
            --  so calls to protected functions of the same protected type are
            --  internal.
            --
            --  Subprograms declared in protected bodies can only be called
            --  internally and then Current_Protected_Type is already set
            --  anyway.

            if Is_Pragma (Prag, Pragma_Postcondition)
              and then Is_Protected_Type (Scope (E))
            then
               declare
                  Save_Protected_Type : constant Entity_Id :=
                    Current_Protected_Type;
               begin
                  Current_Protected_Type := Scope (E);
                  Mark (Expr);
                  Current_Protected_Type := Save_Protected_Type;
               end;
            else
               Mark (Expr);
            end if;

            --  For a class-wide condition, a corresponding expression must
            --  be created in which a reference to a controlling formal
            --  is interpreted as having the class-wide type. This is used
            --  to create a suitable pre- or postcondition expression for
            --  analyzing dispatching calls. This is done here so that the
            --  newly created expression can be marked, including its possible
            --  newly created itypes.

            if Class_Present (Prag) then
               declare
                  New_Expr : constant Node_Id :=
                    New_Copy_Tree (Source => Expr);
               begin
                  Process_Class_Wide_Condition (New_Expr, E);
                  Mark (New_Expr);
                  Set_Dispatching_Contract (Expr, New_Expr);
                  Set_Parent (New_Expr, Prag);
               end;
            end if;

            Prag := Next_Pragma (Prag);
         end loop;

         Prag := Get_Pragma (E, Pragma_Contract_Cases);
         if Present (Prag) then
            declare
               Aggr          : constant Node_Id :=
                 Expression (First (Pragma_Argument_Associations (Prag)));
               Case_Guard    : Node_Id;
               Conseq        : Node_Id;
               Contract_Case : Node_Id;
            begin
               Contract_Case := First (Component_Associations (Aggr));
               while Present (Contract_Case) loop
                  Case_Guard := First (Choices (Contract_Case));
                  Conseq     := Expression (Contract_Case);

                  Mark (Case_Guard);

                  --  Consequences of protected subprograms declared in
                  --  protected type declarations are executed as part of
                  --  protected operations, so any calls to protected
                  --  functions of the same protected type are internal.
                  --
                  --  Subprograms declared in protected bodies can only be
                  --  called internally and then Current_Protected_Type is
                  --  already set anyway.
                  if Is_Protected_Type (Scope (E)) then
                     declare
                        Save_Protected_Type : constant Entity_Id :=
                          Current_Protected_Type;
                     begin
                        Current_Protected_Type := Scope (E);
                        Mark (Conseq);
                        Current_Protected_Type := Save_Protected_Type;
                     end;
                  else
                     Mark (Conseq);
                  end if;

                  Next (Contract_Case);
               end loop;
            end;
         end if;

         --  Enforce the current limitation that a subprogram is only inherited
         --  from a single source, so that there is at most one inherited
         --  Pre'Class or Post'Class to consider for LSP.

         if Is_Dispatching_Operation (E) then
            declare
               Inherit_Subp_No_Intf : constant Subprogram_List :=
                 Inherited_Subprograms (E, No_Interfaces => True);
               Inherit_Subp_Intf : constant Subprogram_List :=
                 Inherited_Subprograms (E, Interfaces_Only => True);
            begin
               --  Ok to inherit a subprogram only from non-interfaces

               if Inherit_Subp_Intf'Length = 0 then
                  null;

               --  Ok to inherit a subprogram from a single interface

               elsif Inherit_Subp_No_Intf'Length = 0
                 and then Inherit_Subp_Intf'Length = 1
               then
                  null;

               --  Do not support yet a subprogram inherited from root type and
               --  from an interface.

               elsif Inherit_Subp_No_Intf'Length /= 0 then
                  Mark_Unsupported
                    ("subprogram inherited from root and interface", E);

               --  Do not support yet a subprogram inherited from multiple
               --  interfaces.

               else
                  Mark_Unsupported
                    ("subprogram inherited from multiple interfaces", E);
               end if;
            end;
         end if;
      end Mark_Subprogram_Entity;

      ----------------------
      -- Mark_Type_Entity --
      ----------------------

      procedure Mark_Type_Entity (E : Entity_Id) is

         function Is_Private_Entity_Mode_Off (E : Entity_Id) return Boolean
         with Pre => Is_Type (E);
         --  Return True iff E is declared in a private part with
         --  SPARK_Mode => Off.

         function Is_Synchronous_Barrier (E : Entity_Id) return Boolean;
         --  Return True if E is Ada.Synchronous_Barriers.Synchronous_Barrier
         --
         --  Synchronous barriers are allowed by the Ravenscar profile, but we
         --  do not want them in SPARK.

         procedure Mark_Default_Expression (C : Entity_Id)
         with Pre => Ekind (C) in E_Component | E_Discriminant;
         --  Mark default expression of component or discriminant and check it
         --  for references to the current instance of a type or subtype (which
         --  is considered to be variable input).

         -----------------------------
         -- Mark_Default_Expression --
         -----------------------------

         procedure Mark_Default_Expression (C : Entity_Id) is

            function Uses_Current_Type_Instance (N : Node_Id) return Boolean;
            --  Returns True iff node [N] mentions the type name [E]

            --------------------------------
            -- Uses_Current_Type_Instance --
            --------------------------------

            function Uses_Current_Type_Instance (N : Node_Id) return Boolean is
               Current_Type_Instance : constant Entity_Id := Unique_Entity (E);

               function Is_Current_Instance
                 (N : Node_Id) return Traverse_Result;
               --  Returns Abandon when a Current_Type_Instance is referenced
               --  in node N and OK otherwise.

               -------------------------
               -- Is_Current_Instance --
               -------------------------

               function Is_Current_Instance
                 (N : Node_Id)
                  return Traverse_Result is
               begin
                  case Nkind (N) is
                     when N_Identifier | N_Expanded_Name =>
                        declare
                           E : constant Entity_Id := Entity (N);

                        begin
                           if Present (E)
                             and then
                              (Unique_Entity (E) = Current_Type_Instance
                                 or else
                               (Ekind (E) = E_Function
                                and then Scope (E) = Current_Type_Instance))
                           then
                              return Abandon;
                           end if;
                        end;

                     when others =>
                        null;
                  end case;

                  return OK;
               end Is_Current_Instance;

               function Find_Current_Instance is new
                 Traverse_Func (Is_Current_Instance);

            begin
               return Find_Current_Instance (N) = Abandon;
            end Uses_Current_Type_Instance;

            --  Local variables

            Expr : constant Node_Id := Expression (Parent (C));

         --  Start of processing for Mark_Default_Expression

         begin
            if Present (Expr) then

               --  The default expression of a component declaration shall
               --  not contain a name denoting the current instance of the
               --  enclosing type; SPARK RM 3.8(2).

               if Uses_Current_Type_Instance (Expr) then
                  Violation_Detected := True;
                  if Emit_Messages and then SPARK_Pragma_Is (Opt.On)
                  then
                     Error_Msg_Node_1 := E;
                     Error_Msg_N
                       ("default expression cannot mention }", E);
                  end if;
               end if;

               Mark (Expr);
            end if;
         end Mark_Default_Expression;

         --------------------------------
         -- Is_Private_Entity_Mode_Off --
         --------------------------------

         function Is_Private_Entity_Mode_Off (E : Entity_Id) return Boolean is
            Decl : constant Node_Id :=
              (if Is_Itype (E)
               then Associated_Node_For_Itype (E)
               else Parent (E));
            Pack_Decl : constant Node_Id := Parent (Parent (Decl));

         begin
            pragma Assert (Nkind (Pack_Decl) = N_Package_Declaration);

            return
              Present (SPARK_Aux_Pragma (Defining_Entity (Pack_Decl)))
              and then Get_SPARK_Mode_From_Annotation
                (SPARK_Aux_Pragma (Defining_Entity (Pack_Decl))) = Off;
         end Is_Private_Entity_Mode_Off;

         ----------------------------
         -- Is_Synchronous_Barrier --
         ----------------------------

         function Is_Synchronous_Barrier (E : Entity_Id) return Boolean is
            S_Ptr : Entity_Id := E;
            --  Scope pointer

            Name_Synchronous_Barrier : constant Name_Id :=
              Name_Find ("synchronous_barrier");
            --  ??? this should be moved to snames.ads-tmpl
         begin
            if Chars (S_Ptr) /= Name_Synchronous_Barrier then
               return False;
            end if;

            S_Ptr := Scope (S_Ptr);

            if Chars (S_Ptr) /= Name_Synchronous_Barriers then
               return False;
            end if;

            S_Ptr := Scope (S_Ptr);

            if Chars (S_Ptr) /= Name_Ada then
               return False;
            end if;

            return Scope (S_Ptr) = Standard_Standard;
         end Is_Synchronous_Barrier;

      --  Start of processing for Mark_Type_Entity

      begin
         --  Synchronous barriers are allowed by the Ravenscar profile, but
         --  we do not want them in SPARK.
         if Is_Synchronous_Barrier (E) then
            Mark_Violation ("synchronous barriers", E);
         end if;

         --  The base type or original type should be marked before the current
         --  type. We also protect ourselves against the case where the Etype
         --  of a full view points to the partial view.

         if not Is_Nouveau_Type (E)
           and then Underlying_Type (Etype (E)) /= E
         then
            if not Retysp_In_SPARK (Etype (E)) then
               Mark_Violation (E, From => Retysp (Etype (E)));
            end if;
         end if;

         --  Type declarations may refer to private types whose full view has
         --  not been declared yet. However, it is this full view which may
         --  define the type in Why3, if it happens to be in SPARK. Hence the
         --  need to define it now, so that it is available for the current
         --  type definition. So we start here with marking all needed types
         --  if not already marked.

         if Is_Array_Type (E) then
            declare
               Component_Typ : constant Node_Id := Component_Type (E);
               Index         : Node_Id := First_Index (E);
            begin
               if Present (Component_Typ) then
                  Mark_Entity (Component_Typ);
               end if;

               while Present (Index) loop
                  Mark_Entity (Etype (Index));
                  Next_Index (Index);
               end loop;

               --  Mark default aspect if any

               if Has_Default_Aspect (E) then
                  Mark (Default_Aspect_Component_Value (E));
               end if;
            end;

         --  Fill in the map between classwide types and their corresponding
         --  specific type, in the case of a user-defined classwide type.

         elsif Is_Class_Wide_Type (E) then
            if Ekind (E) = E_Class_Wide_Subtype then
               declare
                  Subty : constant Node_Id := Subtype_Indication (Parent (E));
                  Ty    : Entity_Id := Empty;
               begin
                  case Nkind (Subty) is
                     when N_Attribute_Reference =>
                        pragma Assert (Attribute_Name (Subty) = Name_Class);
                        Ty := Entity (Prefix (Subty));
                     when N_Identifier | N_Expanded_Name =>
                        Ty := Entity (Subty);
                     when N_Subtype_Indication =>

                        --  Constrained class-wide types are not supported yet
                        --  as it is unclear wether we should do discriminant
                        --  checks for them or not.

                        Mark_Unsupported ("constrained class-wide subtype", E);
                     when others =>
                        raise Program_Error;
                  end case;

                  if Nkind (Subty) /= N_Subtype_Indication then
                     pragma Assert (Present (Ty));
                     Set_Specific_Tagged (E, Unique_Entity (Ty));
                  end if;
               end;
            end if;

         elsif Is_Private_Type (E) and then not Violation_Detected then

            --  When a private type is defined in a package with external
            --  axiomatization or whose private part has SPARK_Mode => Off, we
            --  do not need to mark its underlying type. Indeed, either it is
            --  shared with an ancestor of E and was already handled or it will
            --  not be used.

            if Is_Nouveau_Type (E)
              and then (Entity_In_Ext_Axioms (E)
                          or else
                        Is_Private_Entity_Mode_Off (E))
            then
               Full_Views_Not_In_SPARK.Insert (E, E);
               Discard_Underlying_Type (E);

            --  The same is true for an untagged subtype or a derived type of
            --  such a type or of types whose fullview is not in SPARK.

            elsif not Is_Nouveau_Type (E)
              and then not Is_Tagged_Type (E)
              and then Full_View_Not_In_SPARK (Etype (E))
            then
               Full_Views_Not_In_SPARK.Insert (E, Retysp (Etype (E)));
               Discard_Underlying_Type (E);
            else
               declare
                  Utype : constant Entity_Id :=
                    (if Present (Full_View (E)) then Full_View (E)
                     else Underlying_Type (E));
                  --  Mark the fullview of the type if present before the
                  --  underlying type as this underlying type may not be in
                  --  SPARK.

               begin
                  if not In_SPARK (Utype) then
                     Full_Views_Not_In_SPARK.Insert
                       (E, (if Is_Nouveau_Type (E) then E
                        else Retysp (Etype (E))));
                     Discard_Underlying_Type (E);
                  elsif Full_View_Not_In_SPARK (Utype) then
                     Full_Views_Not_In_SPARK.Insert
                       (E, Get_First_Ancestor_In_SPARK (Utype));
                     Discard_Underlying_Type (E);
                  end if;
               end;
            end if;
         end if;

         --  If the type has a Default_Initial_Condition aspect, store the
         --  corresponding procedure in the Delayed_Type_Aspects map.

         if Gnat2Why.Util.May_Need_DIC_Checking (E) then
            declare
               Delayed_Mapping : constant Node_Id :=
                 (if Present (Current_SPARK_Pragma)
                  then Current_SPARK_Pragma
                  else E);
            begin
               Delayed_Type_Aspects.Include
                 (DIC_Procedure (E), Delayed_Mapping);
            end;
         end if;

         --  Now mark the type itself

         --  Components of a record type should be in SPARK for the record type
         --  to be in SPARK. For a private type, we're only interested here in
         --  its publicly visible components. The same applies to concurrent
         --  types.

         if Ekind (E) in Record_Kind then
            declare
               Comp : Node_Id := First_Component_Or_Discriminant (E);

            begin
               while Present (Comp) loop

                  --  Do not mark components which are declared in a part with
                  --  SPARK_Mode => Off.

                  if Component_Is_Visible_In_SPARK (Comp) then
                     Mark_Entity (Etype (Comp));

                     --  Mark default value of component or discriminant

                     Mark_Default_Expression (Comp);
                  end if;

                  Next_Component_Or_Discriminant (Comp);
               end loop;
            end;

         elsif Ekind (E) in E_Protected_Type | E_Task_Type then
            declare
               Save_SPARK_Pragma : constant Node_Id :=
                 Current_SPARK_Pragma;
               Comp              : Node_Id;
               Fullview_In_SPARK : Boolean;

            begin
               --  Mark discriminants of the protected type

               if Has_Discriminants (E) then
                  Comp := First_Discriminant (E);

                  while Present (Comp) loop

                     --  Mark type and default value of discriminant

                     if In_SPARK (Etype (Comp)) then
                        Mark_Default_Expression (Comp);
                     else
                        Mark_Violation (Comp, From => Etype (Comp));
                     end if;

                     Next_Discriminant (Comp);
                  end loop;
               end if;

               --  Components of protected objects may be subjected to a
               --  different SPARK_Mode.

               Current_SPARK_Pragma := SPARK_Aux_Pragma (E);

               --  Do not mark components which are declared in a part with
               --  SPARK_Mode => Off.

               if Ekind (E) = E_Protected_Type
                 and then not SPARK_Pragma_Is (Opt.Off)
               then
                  declare
                     Save_Protected_Type : constant Entity_Id :=
                       Current_Protected_Type;
                     Save_Violation_Detected : constant Boolean :=
                       Violation_Detected;

                  begin
                     Current_Protected_Type := E;

                     Comp := First_Component (E);
                     while Present (Comp) loop

                        --  Mark type and default value of component

                        if In_SPARK (Etype (Comp)) then
                           Mark_Default_Expression (Comp);
                        else
                           Mark_Violation (Comp, From => Etype (Comp));
                        end if;

                        Next_Component (Comp);
                     end loop;

                     --  Protected types need full default initialization. No
                     --  check needed if the private view of the type is not in
                     --  SPARK.

                     if SPARK_Util.Types.Default_Initialization (E) not in
                       Full_Default_Initialization | No_Possible_Initialization
                     then
                        Mark_Violation ("protected type "
                                        & "with no default initialization",
                                        E,
                                        SRM_Reference => "SPARK RM 9.4");
                     end if;

                     --  If a violation has been found while marking the
                     --  private components of the protected type, then its
                     --  full view is not in SPARK. The type itself can still
                     --  be in SPARK if no SPARK_Mode has been specified.

                     if not SPARK_Pragma_Is (Opt.On) then
                        Fullview_In_SPARK := not Violation_Detected;
                        Violation_Detected := Save_Violation_Detected;

                     --  If the private part is marked On, then the full view
                     --  of the type is forced to be SPARK. Violations found
                     --  during marking of the private part are not reverted.

                     else
                        Fullview_In_SPARK := True;
                     end if;
                     Current_Protected_Type := Save_Protected_Type;
                  end;

               --  Tasks are considered as always having a private part which
               --  is not visible to the prover.

               else
                  Fullview_In_SPARK := False;
               end if;

               Current_SPARK_Pragma := Save_SPARK_Pragma;

               --  If the protected type is in SPARK but not its full view,
               --  store it in Full_Views_Not_In_SPARK.

               if not Violation_Detected and then not Fullview_In_SPARK then
                  Full_Views_Not_In_SPARK.Insert
                    (E, (if Is_Nouveau_Type (E) then E
                         else Retysp (Etype (E))));
               end if;
            end;
         end if;

         --  Record position of where to insert concurrent type on the
         --  Entity_List.

         if Ekind (E) in E_Protected_Type | E_Task_Type then
            Current_Concurrent_Insert_Pos := Entity_List.Last;
         end if;

         if Has_Own_Invariants (E) then

            --  Classwide invariants are not in SPARK

            if Has_Inheritable_Invariants (E) then
               Mark_Violation
                 ("classwide invariant", E, "SPARK RM 7.3.2(2)");

            --  Partial invariants are not allowed in SPARK

            elsif Present (Partial_Invariant_Procedure (E)) then
               Mark_Violation
                 ("type invariant on private_type_declaration or"
                  & " private_type_extension", E, "SPARK RM 7.3.2(2)");

            --  Only mark the invariant as part of the type's fullview

            elsif not Is_Partial_View (E)
              and then not (Ekind (E) in SPARK_Util.Types.Subtype_Kind)
            then

               --  Invariants cannot be specified on completion of private
               --  extension in SPARK.

               if Is_Full_View (E)
                 and then Present (Parent (Partial_View (E)))
                 and then Nkind (Parent (Partial_View (E))) =
                 N_Private_Extension_Declaration
               then
                  Mark_Violation
                    ("type invariant on completion of "
                     & "private_type_extension", E, "SPARK RM 7.3.2(2)");

               --  We currently do not support invariants on type declared in a
               --  nested package. This restriction results in simplifications
               --  in invariant checks on subprogram parameters/global
               --  variables, as well as in determining which are the type
               --  invariants which are visible at a given program point.

               elsif not Is_Compilation_Unit (Enclosing_Unit (E)) then
                  Mark_Unsupported
                    ("type invariant not immediately in a compilation unit",
                     E);

               elsif Is_Child_Unit (Enclosing_Unit (E)) then
                  Mark_Unsupported ("type invariant in child unit", E);

               --  We currently do not support invariants on protected types.
               --  To support them, we would probably need some new RM wording
               --  in SPARK or new syntax in Ada (see P826-030).

               elsif Is_Protected_Type (E) then
                  Mark_Unsupported ("type invariant on protected types", E);

               --  We currently do not support invariants on tagged types. To
               --  support them, we would need to introduce checks for type
               --  invariants of childs on dispatching calls to root primitives
               --  (see SPARK RM 7.3.2(8) and test
               --  P801-002__invariant_on_tagged_types).

               elsif Is_Tagged_Type (E) then
                  Mark_Unsupported ("type invariant on tagged types", E);
               else

                  --  Add the type invariant to delayed aspects to be marked
                  --  later.

                  pragma Assert (Present (Invariant_Procedure (E)));

                  declare
                     Delayed_Mapping : constant Node_Id :=
                       (if Present (Current_SPARK_Pragma)
                        then Current_SPARK_Pragma
                        else E);
                  begin
                     Delayed_Type_Aspects.Include (Invariant_Procedure (E),
                                                   Delayed_Mapping);
                  end;
               end if;
            end if;
         end if;

         --  We currently do not support invariants on components of tagged
         --  types, if the invariant is visible. It is still allowed to include
         --  types with invariants in tagged types as long as the tagged type
         --  is not visible from the scope of the invariant. To support them,
         --  we would need to introduce checks for type invariants of
         --  components of childs on dispatching calls to root primitives
         --  (see SPARK RM 7.3.2(8) and test
         --  P801-002__invariant_on_tagged_component).

         if Is_Tagged_Type (E)
           and then not Is_Partial_View (E)
           and then not (Ekind (E) in SPARK_Util.Types.Subtype_Kind)
         then
            declare
               Comp : Node_Id := First_Component_Or_Discriminant (E);

            begin
               while Present (Comp) loop
                  if Component_Is_Visible_In_SPARK (Comp)
                    and then In_SPARK (Etype (Comp))
                    and then Invariant_Check_Needed (Etype (Comp))
                  then
                     Mark_Unsupported
                       ("type invariant on components of tagged types", E);
                  end if;

                  Next_Component_Or_Discriminant (Comp);
               end loop;
            end;
         end if;

         if Is_Array_Type (E) then
            declare
               Component_Typ : constant Entity_Id := Component_Type (E);
               Index         : Node_Id := First_Index (E);

            begin
               if Positive (Number_Dimensions (E)) > Max_Array_Dimensions then
                  Mark_Unsupported
                    ("} of dimension greater than" & Max_Array_Dimensions'Img,
                     E, Extra_Node => E);
               end if;

               --  Check that all index types are in SPARK

               while Present (Index) loop
                  if not In_SPARK (Etype (Index)) then
                     Mark_Violation (Index, From => Etype (Index));
                  end if;
                  Next_Index (Index);
               end loop;

               --  Access definition for component type is not in SPARK

               if No (Component_Typ) then
                  Mark_Violation ("access type", E);
               end if;

               --  Check that component type is in SPARK

               if not In_SPARK (Component_Typ) then
                  Mark_Violation (E, From => Component_Typ);
               end if;
            end;

         elsif Is_Fixed_Point_Type (E) then
            declare
               function Only_Factor_Is
                 (Num    : Uint;
                  Factor : Uint) return Boolean
               with Pre => UI_Gt (Num, Uint_0) and then
                           UI_Gt (Factor, Uint_0);
               --  Returns True if Num is a power of Factor

               --------------------
               -- Only_Factor_Is --
               --------------------

               function Only_Factor_Is
                 (Num    : Uint;
                  Factor : Uint) return Boolean
               is
                  N : Uint := Num;
               begin
                  while N /= Uint_1 loop
                     if UI_Rem (N, Factor) /= Uint_0 then
                        return False;
                     end if;
                     N := UI_Div (N, Factor);
                  end loop;

                  return True;
               end Only_Factor_Is;

               Inv_Small : constant Ureal := UR_Div (Uint_1, Small_Value (E));
               Inv_Small_Num : constant Uint := Norm_Num (Inv_Small);
            begin
               if Norm_Den (Inv_Small) = Uint_1
                 and then
                   Inv_Small_Num /= Uint_1
                   and then
                     (Only_Factor_Is (Inv_Small_Num, Uint_2)
                      or else
                      Only_Factor_Is (Inv_Small_Num, Uint_10))
               then
                  null;
               else
                  Mark_Unsupported ("fixed-point type whose small is not "
                                    & "a negative power of 2 or 10", E);
               end if;
            end;

         --  Discrete and floating-point types are always in SPARK

         elsif Is_Scalar_Type (E) then

            --  Modular types with modulus greater than 2 ** 64 are not
            --  supported in GNAT, so no need to support them in GNATprove for
            --  now. Supporting them would require either extending the support
            --  in Why3 and provers for bitvectors greater than 64 bits, or
            --  else having a default theory for handling these modular types
            --  too large for bitvectors.
            --  In addition, GNATprove only support single and double ieee
            --  precision floats for now. This is in order to simplify initial
            --  work on smtlib floats. Extending support to Ada's
            --  long_long_float should not pose any fundamental problem.

            if Is_Modular_Integer_Type (E)
              and then Modulus (E) > UI_Expon (2, 64)
            then
               Mark_Unsupported ("modulus greater than 2 ** 64", E);
            elsif Is_Floating_Point_Type (E)
              and then not Is_Double_Precision_Floating_Point_Type (E)
              and then not Is_Single_Precision_Floating_Point_Type (E)
            then
               Mark_Unsupported ("extended precision floating point type", E);
            end if;

         elsif Is_Class_Wide_Type (E) then

            --  Class wide types with a non SPARK root are not in SPARK.
            --  Remark that the violation is always redundant for classwide
            --  types implicitely declared on code with SPARK_Mode => On.
            --  Still, it is necessary for preventing the usage of such
            --  class wide types declared in with'ed packages without
            --  SPARK_Mode.

            declare
               Specific_Type : constant Entity_Id :=
                 Get_Specific_Type_From_Classwide (E);
            begin
               if not Retysp_In_SPARK (Specific_Type) then
                  Mark_Violation (E, From => Specific_Type);

               --  Constrained class-wide types are not supported yet as it is
               --  unclear wether we should do discriminant checks for them
               --  or not.

               elsif Has_Discriminants (Retysp (Specific_Type))
                 and then Is_Constrained (Retysp (Specific_Type))
               then
                  Mark_Unsupported
                    ("Class attribute of a constrained type", E);
               end if;
            end;

         elsif Is_Private_Type (E) then

            --  Private types may export discriminants. Discriminants with
            --  non-SPARK type should be disallowed here.

            declare
               Disc : Entity_Id :=
                 (if Has_Discriminants (E)
                    or else Has_Unknown_Discriminants (E)
                  then First_Discriminant (E)
                  else Empty);
            begin
               while Present (Disc) loop
                  if not In_SPARK (Etype (Disc)) then
                     Mark_Violation (E, From => Etype (Disc));
                  end if;
                  Next_Discriminant (Disc);
               end loop;
            end;

            --  A derived type cannot have explicit discriminants

            if Nkind (Parent (E)) = N_Private_Extension_Declaration
              and then Unique_Entity (Etype (E)) /= Unique_Entity (E)
              and then Present (Discriminant_Specifications (Parent (E)))
              and then Comes_From_Source (E)
            then
               Mark_Violation
                 ("discriminant on derived type",
                  Parent (E),
                  SRM_Reference => "SPARK RM 3.7(2)");
            end if;

         elsif Is_Record_Type (E) then

            if Ekind (E) = E_Record_Subtype
              and then not In_SPARK (Base_Type (E))
            then
               Mark_Violation (E, From => Base_Type (E));
            end if;

            if not Is_Interface (E) then
               declare
                  Field : Entity_Id := First_Component_Or_Discriminant (E);
                  Typ   : Entity_Id;

               begin
                  while Present (Field) loop
                     Typ := Etype (Field);

                     if not Is_Tag (Field)
                       and then Is_Object (Field)
                       and then not In_SPARK (Typ)
                       and then Component_Is_Visible_In_SPARK (Field)
                     then
                        Mark_Violation (Field, From => Typ);
                     end if;

                     Next_Component_Or_Discriminant (Field);
                  end loop;
               end;
            end if;

            --  A derived type cannot have explicit discriminants

            if Nkind (Parent (E)) = N_Full_Type_Declaration
              and then Unique_Entity (Etype (E)) /= Unique_Entity (E)
              and then Present (Discriminant_Specifications (Parent (E)))
              and then Comes_From_Source (E)
            then
               Mark_Violation
                 ("discriminant on derived type",
                  Parent (E),
                  SRM_Reference => "SPARK RM 3.7(2)");
            end if;

            --  A local derived type cannot have ancestors not defined in
            --  the same local scope. We only check direct ancestors, as the
            --  definition of these ancestors will already have checked this
            --  rule for their own ancestors.

            if Nkind (Parent (E)) = N_Full_Type_Declaration
              and then Nkind (Type_Definition (Parent (E))) =
                       N_Derived_Type_Definition
            then
               declare
                  Scop : constant Entity_Id := Enclosing_Dynamic_Scope (E);
               begin
                  if Scop /= Standard_Standard then
                     if Enclosing_Dynamic_Scope (Etype (E)) /= Scop then
                        Mark_Violation
                          ("local derived type from non-local parent",
                           E,
                           SRM_Reference => "SPARK RM 3.9.1(1)");
                     end if;

                     if Present (Interfaces (E)) then
                        declare
                           Ty : Elmt_Id := First_Elmt (Interfaces (E));
                        begin
                           while Present (Node (Ty)) loop
                              if Enclosing_Dynamic_Scope (Node (Ty)) /= Scop
                              then
                                 Mark_Violation
                                   ("local derived type from non-local " &
                                    "interface",
                                    E,
                                    SRM_Reference => "SPARK RM 3.9.1(1)");
                              end if;
                              Ty := Next_Elmt (Ty);
                           end loop;
                        end;
                     end if;
                  end if;
               end;
            end if;

            --  A record type may have a type with full_view not in SPARK as an
            --  etype. In this case, the whole type has fullview not in SPARK.

            if Full_View_Not_In_SPARK (Etype (E)) then
               Full_Views_Not_In_SPARK.Insert (E, Etype (E));
            end if;

         elsif Is_Access_Type (E) then
            Mark_Violation ("access type", E);

         elsif Is_Concurrent_Type (E) then

            if Is_SPARK_Tasking_Configuration then

               --  Only mark declarations of base protected types

               if Ekind (E) in E_Protected_Type | E_Task_Type
                 and then
                   Nkind (Parent (E)) in N_Protected_Type_Declaration
                                       | N_Task_Type_Declaration
               then

                  declare
                     Type_Decl : constant Node_Id := Parent (E);
                     Type_Def  : constant Node_Id :=
                       (if Ekind (E) = E_Protected_Type
                        then Protected_Definition (Type_Decl)
                        else Task_Definition (Type_Decl));

                  begin
                     Mark_List (Interface_List (Type_Decl));

                     --  Traverse the visible and private declarations of the
                     --  type to mark pragmas and representation clauses.

                     if Present (Type_Def) then
                        Mark_Aspect_Clauses_And_Pragmas_In_List
                          (Visible_Declarations (Type_Def));

                        declare
                           Save_SPARK_Pragma : constant Node_Id :=
                             Current_SPARK_Pragma;

                        begin
                           Current_SPARK_Pragma := SPARK_Aux_Pragma (E);
                           if SPARK_Pragma_Is (Opt.On) then
                              declare
                                 Save_Protected_Type : constant Entity_Id :=
                                   Current_Protected_Type;

                              begin
                                 --  Private section may contain pragmas and
                                 --  they are marked here.

                                 Current_Protected_Type := E;

                                 Mark_Aspect_Clauses_And_Pragmas_In_List
                                   (Private_Declarations (Type_Def));

                                 Current_Protected_Type :=
                                   Save_Protected_Type;
                              end;
                           end if;

                           Current_SPARK_Pragma := Save_SPARK_Pragma;
                        end;
                     end if;

                  end;

                  --  Mark Part_Of variables of single protected objects

                  if Ekind (E) = E_Protected_Type
                    and then Is_Single_Concurrent_Type (E)
                  then
                     for Part of
                       Iter (Part_Of_Constituents (Anonymous_Object (E)))
                     loop
                        Mark_Entity (Part);
                     end loop;
                  end if;

               --  We have a concurrent subtype or derived type. It is in SPARK
               --  if its Etype is in SPARK.

               else
                  pragma Assert
                    (Ekind (E) in E_Protected_Subtype | E_Task_Subtype
                     or else (Nkind (Parent (E)) = N_Full_Type_Declaration
                       and then Nkind (Type_Definition (Parent (E))) =
                         N_Derived_Type_Definition));

                  if not In_SPARK (Etype (E)) then
                     Mark_Violation (E, From => Etype (E));
                  end if;

                  --  A concurrent type may have a type with full_view not in
                  --  SPARK as an etype. In this case, the subype has fullview
                  --  not in SPARK.

                  if Full_View_Not_In_SPARK (Etype (E)) then
                     Full_Views_Not_In_SPARK.Include (E, Etype (E));
                  end if;
               end if;

            else
               Mark_Violation_In_Tasking (E);
            end if;

         elsif Is_Incomplete_Type (E) then
            Mark_Unsupported
              ("incomplete type &", E,
               Cont_Msg =>
                 "consider restructuring code to avoid `LIMITED WITH`");

         else
            raise Program_Error;
         end if;
      end Mark_Type_Entity;

      --  Save whether a violation was previously detected, to restore after
      --  marking this entity.

      Save_Violation_Detected : constant Boolean := Violation_Detected;
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;

   --  Start of processing for Mark_Entity

   begin
      --  For entities in external axioms, mark the package entity

      if Entity_In_Ext_Axioms (E) then
         declare
            Pack : constant Entity_Id :=
              Containing_Package_With_Ext_Axioms (E);
         begin
            if Pack /= E and then not In_SPARK (Pack) then
               Mark_Violation (E, From => Pack);
            end if;
         end;
      end if;

      --  Ignore functions generated by the frontend for aspects Type_Invariant
      --  and Default_Initial_Condition. This does not include the functions
      --  generated for Predicate aspects, as these functions are translated
      --  to check absence of RTE in the predicate in the most general context.

      if Is_Subprogram (E)
        and then Subprogram_Is_Ignored_For_Proof (E)
      then
         return;
      end if;

      --  Nothing to do if the entity E was already marked

      if Entity_Marked (E) then
         return;
      end if;

      --  Store entities defined in actions in Actions_Entity_Set

      if Inside_Actions then
         Actions_Entity_Set.Insert (E);
      end if;

      --  Entities may be marked out of order, for example because completions
      --  of private types need to be marked at the point of their partial view
      --  declaration, to avoid out-of-order declarations in Why.
      --  Retrieve the appropriate SPARK_Mode pragma before marking.
      --
      --  For concurrent types SPARK_Mode can be queried directly

      if Ekind (E) in E_Protected_Type | E_Task_Type then

         Current_SPARK_Pragma := SPARK_Pragma (E);

      --  ??? perhaps use SPARK_Pragma_Of_Type here, but not sure if that works
      --  for itypes.

      elsif Is_Type (E) or else Is_Object (E) then
         declare
            Decl : constant Node_Id :=
              (if Is_Itype (E)
               then Associated_Node_For_Itype (E)
               else Parent (E));

         begin
            pragma Assert (Present (Parent (Decl)));

            if Nkind (Parent (Decl)) = N_Package_Specification then
               declare
                  Pack_Decl : constant Node_Id := Parent (Parent (Decl));
                  pragma Assert (Nkind (Pack_Decl) = N_Package_Declaration);

                  Pack_Ent : constant Entity_Id := Defining_Entity (Pack_Decl);
               begin
                  Current_SPARK_Pragma :=
                    (if In_Private_Declarations (Decl)
                     then SPARK_Aux_Pragma (Pack_Ent)
                     else SPARK_Pragma (Pack_Ent));
               end;
            end if;
         end;

      --  Get appropriate SPARK_Mode for subprograms and packages (only happens
      --  for packages with external axioms).

      elsif Is_Subprogram (E)
        or else Is_Entry (E)
        or else Ekind (E) = E_Package
      then
         Current_SPARK_Pragma := SPARK_Pragma (E);
      end if;

      --  Include entity E in the set of marked entities

      Entity_Set.Insert (E);

      --  If the entity is declared in the scope of SPARK_Mode => Off, then
      --  do not consider whether it could be in SPARK or not. An exception to
      --  this rule is abstract state, which has to be added to the Entity_List
      --  regardless of SPARK status. Restore SPARK_Mode pragma before
      --  returning.

      if SPARK_Pragma_Is (Opt.Off)
        and then Ekind (E) /= E_Abstract_State
      then
         Current_SPARK_Pragma := Save_SPARK_Pragma;
         return;
      end if;

      --  For recursive references, start with marking the entity in SPARK

      Entities_In_SPARK.Include (E);

      --  Start with no violation being detected

      Violation_Detected := False;

      --  Mark differently each kind of entity

      case Ekind (E) is
         when Type_Kind        => Mark_Type_Entity (E);

         when Subprogram_Kind  => Mark_Subprogram_Entity (E);

         when E_Constant       |
              E_Variable       =>
            begin
               case Nkind (Parent (E)) is
                  when N_Object_Declaration     => Mark_Object_Entity (E);
                  when N_Iterator_Specification => Mark_Parameter_Entity (E);
                  when others                   => raise Program_Error;
               end case;
            end;

         when E_Discriminant   |
              E_Loop_Parameter |
              Formal_Kind      => Mark_Parameter_Entity (E);

         when Named_Kind       => Mark_Number_Entity (E);
         when E_Package        => Mark_Package_Entity (E);

         --  The identifier of a loop is used to generate the needed
         --  exception declarations in the translation phase.

         when E_Loop           => null;

         --  Mark_Entity is called on all abstract state variables

         when E_Abstract_State =>

            --  If an abstract state is a Part_Of constituent of a single
            --  concurrent object then raise a violation.

            if Is_Part_Of_Concurrent_Object (E) then
               Mark_Unsupported
                 ("abstract state Part_Of constituent of " &
                  "a single concurrent object", E);
            end if;

         when Entry_Kind       => Mark_Subprogram_Entity (E);

         when others           =>
            Ada.Text_IO.Put_Line ("[Mark_Entity] kind ="
                                  & Entity_Kind'Image (Ekind (E)));
            raise Program_Error;
      end case;

      --  If a violation was detected, remove E from the set of SPARK entities

      if Violation_Detected then
         Entities_In_SPARK.Delete (E);

      --  Otherwise, add entity to appropriate list

      else
         --  Entities from packages with external axioms are handled by a
         --  specific mechanism and thus should not be translated.
         if not Entity_In_Ext_Axioms (E) then

            --  Concurrent types go before their visible declarations (because
            --  declarations reference them as implicit inputs).
            if Ekind (E) in E_Protected_Type | E_Task_Type then

               pragma Assert
                 (Current_Concurrent_Insert_Pos /= Node_Lists.No_Element);

               Node_Lists.Next (Current_Concurrent_Insert_Pos);

               --  If there were no entities defined within concurrent types
               --  then Next will advance the cursor to No_Element and Insert
               --  will be equivalent to Append. This is precisely what we
               --  need.
               Entity_List.Insert (Before   => Current_Concurrent_Insert_Pos,
                                   New_Item => E);
            else
               Entity_List.Append (E);
            end if;
         end if;
      end if;

      --  Update the information that a violation was detected

      Violation_Detected := Save_Violation_Detected;

      --  Restore SPARK_Mode pragma

      Current_SPARK_Pragma := Save_SPARK_Pragma;
   end Mark_Entity;

   ------------------------------------
   -- Mark_Extended_Return_Statement --
   ------------------------------------

   procedure Mark_Extended_Return_Statement (N : Node_Id) is
   begin
      Mark_Stmt_Or_Decl_List (Return_Object_Declarations (N));

      if Present (Handled_Statement_Sequence (N)) then
         Mark (Handled_Statement_Sequence (N));
      end if;
   end Mark_Extended_Return_Statement;

   -----------------------------
   -- Mark_Handled_Statements --
   -----------------------------

   procedure Mark_Handled_Statements (N : Node_Id) is
      Handlers : constant List_Id := Exception_Handlers (N);

   begin
      if Present (Handlers) then
         Mark_Violation ("handler", First (Handlers));
      end if;

      Mark_Stmt_Or_Decl_List (Statements (N));
   end Mark_Handled_Statements;

   --------------------------------------
   -- Mark_Identifier_Or_Expanded_Name --
   --------------------------------------

   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id) is
      E : constant Entity_Id := Entity (N);
   begin
      case Ekind (E) is
         when Object_Kind =>
            if Ekind (E) in E_Variable | E_Constant | Formal_Kind
              and then not In_SPARK (E)
            then
               Mark_Violation (N, From => E);

            --  Record components and discriminants are in SPARK if they are
            --  visible in the representative type of their scope. Do not
            --  report a violation if the type itself is not SPARK, as the
            --  violation will already have been reported.

            elsif Ekind (E) in E_Discriminant | E_Component then
               declare
                  Ty : constant Entity_Id := Retysp (Scope (E));
               begin
                  if In_SPARK (Ty)
                    and then No (Search_Component_By_Name (Ty, E))
                  then
                     Mark_Violation (N, From => Ty);
                  end if;
               end;
            end if;

         --  Subprogram names appear for example in Sub'Result

         when Entry_Kind  |
              E_Function  |
              E_Procedure |
              Named_Kind  |
              Type_Kind   =>
            if not In_SPARK (E) then
               Mark_Violation (N, From => E);
            end if;

         when E_Void                  |
              E_Enumeration_Literal   |
              E_Block                 |
              Generic_Subprogram_Kind |
              E_Generic_Package       |
              E_Label                 |
              E_Loop                  |
              E_Return_Statement      |
              E_Package               |
              E_Package_Body          |
              E_Subprogram_Body       |
              E_Exception             =>
            null;

         --  Abstract state entities are passed directly to Mark_Entity

         when E_Abstract_State =>
            raise Program_Error;

         --  ??? how about Protected_Object'Size?

         when E_Entry_Index_Parameter |
              E_Protected_Object      |
              E_Protected_Body        |
              E_Task_Body             =>
            Mark_Violation ("tasking", N);

         --  Entities that we do not expect in SPARK

         when E_Operator =>
            raise Program_Error;
      end case;
   end Mark_Identifier_Or_Expanded_Name;

   ------------------------
   -- Mark_If_Expression --
   ------------------------

   procedure Mark_If_Expression (N : Node_Id) is
   begin
      Mark_Actions (N, Then_Actions (N));
      Mark_Actions (N, Else_Actions (N));

      declare
         Condition : constant Node_Id := First (Expressions (N));
         Then_Expr : constant Node_Id := Next (Condition);
         Else_Expr : constant Node_Id := Next (Then_Expr);
      begin
         Mark (Condition);
         Mark (Then_Expr);

         if Present (Else_Expr) then
            Mark (Else_Expr);
         end if;
      end;
   end Mark_If_Expression;

   -----------------------
   -- Mark_If_Statement --
   -----------------------

   procedure Mark_If_Statement (N : Node_Id) is
   begin
      Mark (Condition (N));

      Mark_Stmt_Or_Decl_List (Then_Statements (N));

      declare
         Part : Node_Id;

      begin
         Part := First (Elsif_Parts (N));
         while Present (Part) loop
            Mark_Actions (N, Condition_Actions (Part));
            Mark (Condition (Part));
            Mark_Stmt_Or_Decl_List (Then_Statements (Part));
            Next (Part);
         end loop;
      end;

      if Present (Else_Statements (N)) then
         Mark_Stmt_Or_Decl_List (Else_Statements (N));
      end if;
   end Mark_If_Statement;

   ---------------------------
   -- Mark_Iteration_Scheme --
   ---------------------------

   procedure Mark_Iteration_Scheme (N : Node_Id) is
   begin
      if Present (Condition (N)) then
         Mark_Actions (N, Condition_Actions (N));
         Mark (Condition (N));

      elsif Present (Loop_Parameter_Specification (N)) then
         pragma Assert (No (Condition_Actions (N)));
         Mark (Discrete_Subtype_Definition
                 (Loop_Parameter_Specification (N)));

         --  The loop parameter shall be added to the entities in SPARK
         declare
            Loop_Index : constant Entity_Id :=
              Defining_Identifier (Loop_Parameter_Specification (N));
         begin
            Mark_Entity (Loop_Index);
         end;

      else
         pragma Assert (No (Condition_Actions (N)));
         pragma Assert (Present (Iterator_Specification (N)));

         Mark (Iterator_Specification (N));
      end if;
   end Mark_Iteration_Scheme;

   ---------------
   -- Mark_List --
   ---------------

   procedure Mark_List (L : List_Id) is
      N : Node_Id;
   begin
      N := First (L);
      while Present (N) loop
         Mark (N);
         Next (N);
      end loop;
   end Mark_List;

   -----------------------------
   -- Mark_Number_Declaration --
   -----------------------------

   procedure Mark_Number_Declaration (N : Node_Id) renames
     Mark_Object_Declaration;

   -----------------------------
   -- Mark_Object_Declaration --
   -----------------------------

   procedure Mark_Object_Declaration (N : Node_Id) is
      E : constant Entity_Id := Defining_Entity (N);
   begin
      if not In_SPARK (E) then
         Mark_Violation (N, From => E);
      end if;
   end Mark_Object_Declaration;

   -----------------------
   -- Mark_Package_Body --
   -----------------------

   procedure Mark_Package_Body (N : Node_Id) is
      Body_E : constant Entity_Id := Defining_Entity (N);
      Spec_E : constant Entity_Id := Unique_Entity (Body_E);

      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;

   begin
      --  Do not analyze generic bodies

      if Ekind (Spec_E) = E_Generic_Package
        or else not Entity_In_SPARK (Spec_E)
      then
         return;
      end if;

      --  Do not analyze bodies for packages with external axioms. Only check
      --  that their SPARK_Mode is Off.

      if Entity_In_Ext_Axioms (Spec_E) then

         if Present (SPARK_Pragma (Body_E))
           and then
             Get_SPARK_Mode_From_Annotation (SPARK_Pragma (Body_E)) /= Off
         then
            --  Call to Mark_Violation will only emit a message if
            --  Current_SPARK_Pragma is points to On. Here we know that pragma
            --  on the body entity is not Off, so it must be On.

            Current_SPARK_Pragma := SPARK_Pragma (Body_E);

            Mark_Violation ("Body of package with External_Axiomatization", N);

            Current_SPARK_Pragma := Save_SPARK_Pragma;
         end if;

      else
         Current_SPARK_Pragma := SPARK_Pragma (Body_E);

         --  Only analyze package body when SPARK_Mode /= Off

         if not SPARK_Pragma_Is (Opt.Off) then

            declare
               Save_Violation_Detected : constant Boolean :=
                 Violation_Detected;
            begin
               Violation_Detected := False;

               Mark_Stmt_Or_Decl_List (Declarations (N));

               --  Only analyze package body statements when SPARK_Mode /= Off

               Current_SPARK_Pragma := SPARK_Aux_Pragma (Body_E);

               if not SPARK_Pragma_Is (Opt.Off) then

                  declare
                     HSS : constant Node_Id := Handled_Statement_Sequence (N);
                  begin
                     if Present (HSS) then
                        Mark (HSS);
                     end if;
                  end;

               end if;

               if not Violation_Detected then
                  Bodies_In_SPARK.Insert (Spec_E);
               end if;

               Violation_Detected := Save_Violation_Detected;
            end;
         end if;

         Current_SPARK_Pragma := Save_SPARK_Pragma;

      end if;

   end Mark_Package_Body;

   ------------------------------
   -- Mark_Package_Declaration --
   ------------------------------

   procedure Mark_Package_Declaration (N : Node_Id) is
      Id : constant Entity_Id := Defining_Entity (N);

   begin
      if Entity_In_Ext_Axioms (Id) then

         --  Mark the package entity

         Mark_Entity (Id);

      else
         declare
            Spec       : constant Node_Id := Specification (N);
            Vis_Decls  : constant List_Id := Visible_Declarations (Spec);
            Priv_Decls : constant List_Id := Private_Declarations (Spec);

            Save_SPARK_Pragma       : constant Node_Id := Current_SPARK_Pragma;
            Save_Violation_Detected : constant Boolean := Violation_Detected;

         begin
            Current_SPARK_Pragma := SPARK_Pragma (Id);

            --  Record the package as an entity to translate iff it is
            --  explicitly marked with SPARK_Mode => On.

            if SPARK_Pragma_Is (Opt.On) then
               Entity_List.Append (Id);
            end if;

            --  Reset violation status to determine if there are any violations
            --  in the package declaration itself.

            Violation_Detected := False;

            --  Mark abstract state entities, since they may be referenced from
            --  the outside. Iff SPARK_Mode is On | None they they will be in
            --  SPARK; if SPARK_Mode is Off then they will be not. Same for
            --  visible declarations.

            for State of Iter (Abstract_States (Id)) loop
               if not Is_Null_State (State) then
                  Mark_Entity (State);
               end if;
            end loop;

            Mark_Stmt_Or_Decl_List (Vis_Decls);

            Current_SPARK_Pragma := SPARK_Aux_Pragma (Id);

            --  Private declarations cannot be referenced from the outside;
            --  if SPARK_Mode is Off then should just skip them, but the Retysp
            --  magic relies on their marking status (which most likely hides
            --  some underlying problem).

            Mark_Stmt_Or_Decl_List (Priv_Decls);

            --  Finally, if the the package has SPARK_Mode On | None and there
            --  are no violations then record it as in SPARK.

            Current_SPARK_Pragma := SPARK_Pragma (Id);

            if not SPARK_Pragma_Is (Opt.Off)
              and then not Violation_Detected
            then
               Entities_In_SPARK.Include (Id);
            end if;

            Violation_Detected := Save_Violation_Detected;
            Current_SPARK_Pragma := Save_SPARK_Pragma;
         end;

      end if;

   end Mark_Package_Declaration;

   -----------------
   -- Mark_Pragma --
   -----------------

   --  GNATprove currently deals with a subset of the Ada and GNAT pragmas.
   --  Other recognized pragmas are ignored, and a warning is issued here (and
   --  in flow analysis, and in proof) that the pragma is ignored. Any change
   --  in the set of pragmas that GNATprove supports should be reflected:
   --    . in Mark_Pragma below
   --    . for flow analysis, in Pragma_Relevant_To_Flow in
   --      flow-control_flow_graph.adb
   --    . for proof, in Transform_Pragma in gnat2why-expr.adb

   procedure Mark_Pragma (N : Node_Id) is
      Pname   : constant Name_Id   := Pragma_Name (N);
      Prag_Id : constant Pragma_Id := Get_Pragma_Id (Pname);

      Arg1 : Node_Id;
      Arg2 : Node_Id;
      --  First two pragma arguments (pragma argument association nodes, or
      --  Empty if the corresponding argument does not exist).

   begin
      if Present (Pragma_Argument_Associations (N)) then
         Arg1 := First (Pragma_Argument_Associations (N));
         pragma Assert (Present (Arg1));
         Arg2 := Next (Arg1);
      else
         Arg1 := Empty;
         Arg2 := Empty;
      end if;

      case Prag_Id is

         --  pragma Check ([Name    =>] Identifier,
         --                [Check   =>] Boolean_Expression
         --              [,[Message =>] String_Expression]);

         when Pragma_Check =>
            if not Is_Ignored_Pragma_Check (N) then
               Mark (Get_Pragma_Arg (Arg2));
            end if;

         --  pragma Loop_Variant
         --         ( LOOP_VARIANT_ITEM {, LOOP_VARIANT_ITEM } );

         --  LOOP_VARIANT_ITEM ::= CHANGE_DIRECTION => discrete_EXPRESSION

         --  CHANGE_DIRECTION ::= Increases | Decreases

         when Pragma_Loop_Variant =>
            declare
               Variant : Node_Id;
            begin
               --  Process all increasing / decreasing expressions

               Variant := First (Pragma_Argument_Associations (N));
               while Present (Variant) loop
                  Mark (Expression (Variant));
                  Next (Variant);
               end loop;
            end;

         --  Emit warning on pragma Overflow_Mode being currently ignored, even
         --  in code not marked SPARK_Mode On, as otherwise no warning would
         --  be issued on configuration pragmas at the start of units whose
         --  top level declaration is marked later SPARK_Mode On. Do not emit
         --  a warning in code marked SPARK_Mode Off though.

         when Pragma_Overflow_Mode =>
            if Emit_Warning_Info_Messages
              and then not SPARK_Pragma_Is (Opt.Off)
            then
               Error_Msg_F ("?pragma Overflow_Mode in code is ignored", N);
            end if;

         when Pragma_Attach_Handler =>
            --  Arg1 is the handler name; check if it is in SPARK, because
            --  SPARK code should not reference non-SPARK code.
            --  Arg2 is the interrupt ID.
            Mark (Expression (Arg1));
            Mark (Expression (Arg2));

         when Pragma_Interrupt_Priority =>
            --  Priority expression is optional
            if Present (Arg1) then
               Mark (Expression (Arg1));
            end if;

         when Pragma_Priority =>
            Mark (Expression (Arg1));

         when Pragma_Max_Queue_Length =>
            Mark (Expression (Arg1));

         --  Remaining pragmas fall into two major groups:
         --
         --  Group 1 - ignored
         --
         --  Pragmas that do not need any marking, either because:
         --  . they are defined by SPARK 2014, or
         --  . they are already taken into account elsewhere (contracts)
         --  . they have no effect on verification

         --  Group 1a - RM Table 16.1, Ada language-defined pragmas marked
         --  "Yes".
         --  Note: pragma Assert is transformed into an
         --  instance of pragma Check by the front-end.
         when Pragma_Assertion_Policy             |
              Pragma_Atomic                       |
              Pragma_Atomic_Components            |
              Pragma_Convention                   |
              Pragma_Elaborate                    |
              Pragma_Elaborate_All                |
              Pragma_Elaborate_Body               |
              Pragma_Export                       |
              Pragma_Extensions_Visible           |
              Pragma_Import                       |
              Pragma_Independent                  |
              Pragma_Independent_Components       |
              Pragma_Inline                       |
              Pragma_Inspection_Point             |
              Pragma_Linker_Options               |
              Pragma_List                         |
              Pragma_No_Return                    |
              Pragma_Normalize_Scalars            |
              Pragma_Optimize                     |
              Pragma_Pack                         |
              Pragma_Page                         |
              Pragma_Partition_Elaboration_Policy |
              Pragma_Preelaborable_Initialization |
              Pragma_Preelaborate                 |
              Pragma_Profile                      |
              Pragma_Pure                         |
              Pragma_Restrictions                 |
              Pragma_Reviewable                   |
              Pragma_Suppress                     |
              Pragma_Unsuppress                   |
              Pragma_Volatile                     |
              Pragma_Volatile_Components          |
              Pragma_Volatile_Full_Access         |

         --  Group 1b - RM Table 16.2, SPARK language-defined pragmas marked
         --  "Yes".
         --  Note: pragmas Assert_And_Cut, Assume, and
         --  Loop_Invariant are transformed into instances of
         --  pragma Check by the front-end.
              Pragma_Abstract_State               |
              Pragma_Assume_No_Invalid_Values     |
              Pragma_Async_Readers                |
              Pragma_Async_Writers                |
              Pragma_Constant_After_Elaboration   |
              Pragma_Contract_Cases               |
              Pragma_Depends                      |
              Pragma_Default_Initial_Condition    |
              Pragma_Effective_Reads              |
              Pragma_Effective_Writes             |
              Pragma_Ghost                        |
              Pragma_Global                       |
              Pragma_Initializes                  |
              Pragma_Initial_Condition            |
              Pragma_Invariant                    |
              Pragma_Part_Of                      |
              Pragma_Postcondition                |
              Pragma_Precondition                 |
              Pragma_Refined_Depends              |
              Pragma_Refined_Global               |
              Pragma_Refined_Post                 |
              Pragma_Refined_State                |
              Pragma_SPARK_Mode                   |
              Pragma_Type_Invariant               |
              Pragma_Type_Invariant_Class         |
              Pragma_Unevaluated_Use_Of_Old       |
              Pragma_Volatile_Function            |

         --  Group 1c - RM Table 16.3, GNAT implementation-defined pragmas
         --  marked "Yes".
         --  Note: pragma Debug is removed by the front-end.
         --  Note: the interesting case of pragma Annotate (the one with first
         --  argument Gnatprove) is handled in Mark_Stmt_Or_Decl_List.

              Pragma_Ada_83                       |
              Pragma_Ada_95                       |
              Pragma_Ada_05                       |
              Pragma_Ada_2005                     |
              Pragma_Ada_12                       |
              Pragma_Ada_2012                     |
              Pragma_Annotate                     |
              Pragma_Check_Policy                 |
              Pragma_Ignore_Pragma                |
              Pragma_Inline_Always                |
              Pragma_Linker_Section               |
              Pragma_No_Elaboration_Code_All      |
              Pragma_No_Heap_Finalization         |
              Pragma_No_Tagged_Streams            |
              Pragma_Pure_Function                |
              Pragma_Restriction_Warnings         |
              Pragma_Secondary_Stack_Size         |
              Pragma_Style_Checks                 |
              Pragma_Test_Case                    |
              Pragma_Unmodified                   |
              Pragma_Unreferenced                 |
              Pragma_Unused                       |
              Pragma_Validity_Checks              |
              Pragma_Warnings                     |
              Pragma_Weak_External                =>
            null;

         --  Group 1d - pragma that are re-written and/or removed
         --  by the front-end in GNATprove, so they should
         --  never be seen here.
         when Pragma_Assert                       |
              Pragma_Assert_And_Cut               |
              Pragma_Assume                       |
              Pragma_Debug                        |
              Pragma_Loop_Invariant               =>
            raise Program_Error;

         --  Group 2 - Remaining pragmas, enumerated here rather than
         --  a "when others" to force re-consideration when
         --  SNames.Pragma_Id is extended.
         --
         --  These all generate a warning.  In future, these pragmas
         --  may move to be fully ignored or to be processed with more
         --  semantic detail as required.

         --  Group 2a - GNAT Defined and obsolete pragmas
         when Pragma_Abort_Defer                 |
           Pragma_Allow_Integer_Address          |
           Pragma_Attribute_Definition           |
           Pragma_C_Pass_By_Copy                 |
           Pragma_Check_Float_Overflow           |
           Pragma_Check_Name                     |
           Pragma_Comment                        |
           Pragma_Common_Object                  |
           Pragma_Compile_Time_Error             |
           Pragma_Compile_Time_Warning           |
           Pragma_Compiler_Unit                  |
           Pragma_Compiler_Unit_Warning          |
           Pragma_Complete_Representation        |
           Pragma_Complex_Representation         |
           Pragma_Component_Alignment            |
           Pragma_Controlled                     |
           Pragma_Convention_Identifier          |
           Pragma_CPP_Class                      |
           Pragma_CPP_Constructor                |
           Pragma_CPP_Virtual                    |
           Pragma_CPP_Vtable                     |
           Pragma_CPU                            |
           Pragma_Debug_Policy                   |
           Pragma_Default_Scalar_Storage_Order   |
           Pragma_Default_Storage_Pool           |
           Pragma_Detect_Blocking                |
           Pragma_Disable_Atomic_Synchronization |
           Pragma_Dispatching_Domain             |
           Pragma_Elaboration_Checks             |
           Pragma_Eliminate                      |
           Pragma_Enable_Atomic_Synchronization  |
           Pragma_Export_Function                |
           Pragma_Export_Object                  |
           Pragma_Export_Procedure               |
           Pragma_Export_Value                   |
           Pragma_Export_Valued_Procedure        |
           Pragma_Extend_System                  |
           Pragma_Extensions_Allowed             |
           Pragma_External                       |
           Pragma_External_Name_Casing           |
           Pragma_Fast_Math                      |
           Pragma_Favor_Top_Level                |
           Pragma_Finalize_Storage_Only          |
           Pragma_Ident                          |
           Pragma_Implementation_Defined         |
           Pragma_Implemented                    |
           Pragma_Implicit_Packing               |
           Pragma_Import_Function                |
           Pragma_Import_Object                  |
           Pragma_Import_Procedure               |
           Pragma_Import_Valued_Procedure        |
           Pragma_Initialize_Scalars             |
           Pragma_Inline_Generic                 |
           Pragma_Interface                      |
           Pragma_Interface_Name                 |
           Pragma_Interrupt_Handler              |
           Pragma_Interrupt_State                |
           Pragma_Keep_Names                     |
           Pragma_License                        |
           Pragma_Link_With                      |
           Pragma_Linker_Alias                   |
           Pragma_Linker_Constructor             |
           Pragma_Linker_Destructor              |
           Pragma_Loop_Optimize                  |
           Pragma_Machine_Attribute              |
           Pragma_Main                           |
           Pragma_Main_Storage                   |
           Pragma_Memory_Size                    |
           Pragma_No_Body                        |
           Pragma_No_Inline                      |
           Pragma_No_Run_Time                    |
           Pragma_No_Strict_Aliasing             |
           Pragma_Obsolescent                    |
           Pragma_Optimize_Alignment             |
           Pragma_Ordered                        |
           Pragma_Overriding_Renamings           |
           Pragma_Passive                        |
           Pragma_Persistent_BSS                 |
           Pragma_Polling                        |
           Pragma_Post                           |
           Pragma_Post_Class                     |
           Pragma_Pre                            |
           Pragma_Predicate                      |
           Pragma_Predicate_Failure              |
           Pragma_Prefix_Exception_Messages      |
           Pragma_Pre_Class                      |
           Pragma_Priority_Specific_Dispatching  |
           Pragma_Profile_Warnings               |
           Pragma_Propagate_Exceptions           |
           Pragma_Provide_Shift_Operators        |
           Pragma_Psect_Object                   |
           Pragma_Rational                       |
           Pragma_Ravenscar                      |
           Pragma_Relative_Deadline              |
           Pragma_Remote_Access_Type             |
           Pragma_Rename_Pragma                  |
           Pragma_Restricted_Run_Time            |
           Pragma_Share_Generic                  |
           Pragma_Shared                         |
           Pragma_Short_Circuit_And_Or           |
           Pragma_Short_Descriptors              |
           Pragma_Simple_Storage_Pool_Type       |
           Pragma_Source_File_Name               |
           Pragma_Source_File_Name_Project       |
           Pragma_Source_Reference               |
           Pragma_Static_Elaboration_Desired     |
           Pragma_Storage_Unit                   |
           Pragma_Stream_Convert                 |
           Pragma_Subtitle                       |
           Pragma_Suppress_All                   |
           Pragma_Suppress_Debug_Info            |
           Pragma_Suppress_Exception_Locations   |
           Pragma_Suppress_Initialization        |
           Pragma_System_Name                    |
           Pragma_Task_Info                      |
           Pragma_Task_Name                      |
           Pragma_Task_Storage                   |
           Pragma_Thread_Local_Storage           |
           Pragma_Time_Slice                     |
           Pragma_Title                          |
           Pragma_Unchecked_Union                |
           Pragma_Unimplemented_Unit             |
           Pragma_Universal_Aliasing             |
           Pragma_Universal_Data                 |
           Pragma_Unreferenced_Objects           |
           Pragma_Unreserve_All_Interrupts       |
           Pragma_Use_VADS_Size                  |
           Pragma_Warning_As_Error               |
           Pragma_Wide_Character_Encoding        |

           --  Group 2b - Ada RM pragmas
           Pragma_Discard_Names                  |
           Pragma_Locking_Policy                 |
           Pragma_Queuing_Policy                 |
           Pragma_Task_Dispatching_Policy        |
           Pragma_All_Calls_Remote               |
           Pragma_Asynchronous                   |
           Pragma_Remote_Call_Interface          |
           Pragma_Remote_Types                   |
           Pragma_Shared_Passive                 |
           Pragma_Lock_Free                      |
           Pragma_Storage_Size                   =>

            if Emit_Warning_Info_Messages
              and then SPARK_Pragma_Is (Opt.On)
            then
               Error_Msg_Name_1 := Pname;
               Error_Msg_N ("?pragma % ignored (not yet supported)", N);
            end if;

         --  Unknown_Pragma is treated here. We use an OTHERS case in order to
         --  deal with all the more recent pragmas introduced in GNAT for which
         --  we have not yet defined how they are supported in SPARK.

         when others =>
            Error_Msg_Name_1 := Pname;
            Mark_Violation ("unknown pragma %", N);
      end case;
   end Mark_Pragma;

   -------------------------
   -- Mark_Protected_Body --
   -------------------------

   procedure Mark_Protected_Body (N : Node_Id) is
      Spec : constant Entity_Id := Corresponding_Spec (N);

   begin
      if Entity_In_SPARK (Spec) then
         declare
            Def_E : constant Entity_Id := Defining_Entity (N);

            Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;

         begin
            Current_SPARK_Pragma := SPARK_Pragma (Def_E);

            if not SPARK_Pragma_Is (Opt.Off) then
               declare
                  Save_Protected_Type : constant Entity_Id :=
                    Current_Protected_Type;

                  Save_Violation_Detected : constant Boolean :=
                    Violation_Detected;

               begin
                  Current_Protected_Type := Spec;
                  Violation_Detected := False;

                  Mark_Stmt_Or_Decl_List (Declarations (N));

                  if not Violation_Detected then
                     Bodies_In_SPARK.Insert (Spec);
                  end if;

                  Violation_Detected := Save_Violation_Detected;
                  Current_Protected_Type := Save_Protected_Type;
               end;

            end if;

            Current_SPARK_Pragma := Save_SPARK_Pragma;
         end;
      end if;
   end Mark_Protected_Body;

   ----------------------------------
   -- Mark_Simple_Return_Statement --
   ----------------------------------

   procedure Mark_Simple_Return_Statement (N : Node_Id) is
   begin
      if Present (Expression (N)) then
         Mark (Expression (N));
      end if;
   end Mark_Simple_Return_Statement;

   ---------------------------
   -- Mark_Standard_Package --
   ---------------------------

   procedure Mark_Standard_Package is

      procedure Insert_All_And_SPARK (E : Entity_Id);

      --------------------------
      -- Insert_All_And_SPARK --
      --------------------------

      procedure Insert_All_And_SPARK (E : Entity_Id) is
      begin
         Entity_Set.Insert (E);
         Entities_In_SPARK.Insert (E);
      end Insert_All_And_SPARK;

      --  Standard types which are in SPARK are associated to True

      Standard_Type_Is_In_SPARK : constant array (S_Types) of Boolean :=
        (S_Boolean             => True,

         S_Short_Short_Integer => True,
         S_Short_Integer       => True,
         S_Integer             => True,
         S_Long_Integer        => True,
         S_Long_Long_Integer   => True,

         S_Natural             => True,
         S_Positive            => True,

         S_Short_Float         =>
           Is_Single_Precision_Floating_Point_Type
             (Standard_Entity (S_Short_Float)),
         S_Float               => True,
         S_Long_Float          => True,
         S_Long_Long_Float     =>
           Is_Double_Precision_Floating_Point_Type
             (Standard_Entity (S_Long_Long_Float)),

         S_Character           => True,
         S_Wide_Character      => True,
         S_Wide_Wide_Character => True,

         S_String              => True,
         S_Wide_String         => True,
         S_Wide_Wide_String    => True,

         S_Duration            => True);

   --  Start of processing for Mark_Standard_Package

   begin
      Initialize;

      for S in S_Types loop
         Entity_Set.Insert (Standard_Entity (S));
         Entity_Set.Include (Etype (Standard_Entity (S)));
         if Standard_Type_Is_In_SPARK (S) then
            Entities_In_SPARK.Insert (Standard_Entity (S));
            Entities_In_SPARK.Include (Etype (Standard_Entity (S)));
         end if;
      end loop;

      for S in S_ASCII_Names loop
         Insert_All_And_SPARK (Standard_Entity (S));
      end loop;

      Insert_All_And_SPARK (Standard_Void_Type);

      Insert_All_And_SPARK (Standard_False);
      Insert_All_And_SPARK (Standard_True);

      Insert_All_And_SPARK (Universal_Integer);
      Insert_All_And_SPARK (Universal_Real);
      Insert_All_And_SPARK (Universal_Fixed);

      Insert_All_And_SPARK (Standard_Integer_8);
      Insert_All_And_SPARK (Standard_Integer_16);
      Insert_All_And_SPARK (Standard_Integer_32);
      Insert_All_And_SPARK (Standard_Integer_64);
   end Mark_Standard_Package;

   ----------------------------
   -- Mark_Stmt_Or_Decl_List --
   ----------------------------

   procedure Mark_Stmt_Or_Decl_List (L : List_Id) is
      Preceding : Node_Id;
      Cur       : Node_Id := First (L);
      Is_Parent : Boolean := True;
   begin
      --  We delay the initialization after checking that we really have a list

      if No (Cur) then
         return;
      end if;

      Preceding := Parent (L);

      while Present (Cur) loop

         --  We peek into the statement node to handle the case of the Annotate
         --  pragma separately here, to avoid passing the "Preceding" node
         --  around. All other cases are handled by Mark.

         if Is_Pragma_Annotate_GNATprove (Cur) then

            --  Handle all the following pragma Annotate, with the same
            --  "Preceding" node.

            loop
               Mark_Pragma_Annotate (Cur, Preceding,
                                     Consider_Next => not Is_Parent);
               Next (Cur);
               exit when
                 No (Cur)
                 or else not Is_Pragma_Annotate_GNATprove (Cur);
            end loop;

         else
            Mark (Cur);

            --  If the current declaration does not come from source, we
            --  consider it to be part of the preceding one as far as pragma
            --  Annotate is concerned, so we don't update the "preceding" node
            --  in that case. The exception to this rule are expression
            --  functions.

            if Comes_From_Source (Cur)
              or else Nkind (Original_Node (Cur)) = N_Expression_Function
            then
               Preceding := Cur;
               Is_Parent := False;
            end if;
            Next (Cur);
         end if;
      end loop;
   end Mark_Stmt_Or_Decl_List;

   --------------------------
   -- Mark_Subprogram_Body --
   --------------------------

   procedure Mark_Subprogram_Body (N : Node_Id) is
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;
      Def_E             : constant Entity_Id := Defining_Entity (N);
      E                 : constant Entity_Id := Unique_Entity (Def_E);

      In_Pred_Function_Body : constant Boolean :=
        Ekind (E) = E_Function and then Is_Predicate_Function (E);
      --  Set to True iff processing body of a predicate function, which is
      --  generated by the front end.

      Save_Delayed_Aspect_Type : constant Entity_Id :=
        Current_Delayed_Aspect_Type;

      SPARK_Pragma_Is_On : Boolean;
      --  Saves the information that SPARK_Mode is On for the body, for use
      --  later in the subprogram.

   --  Start of processing for Mark_Subprogram_Body

   begin
      --  Ignore bodies defined in the standard library, unless the main unit
      --  is from the standard library. In particular, ignore bodies from
      --  instances of generics defined in the standard library (unless we
      --  are analyzing the standard library itself). As a result, no VC is
      --  generated in this case for standard library code.

      if Location_In_Standard_Library (Sloc (N))
        and not Unit_In_Standard_Library (Main_Unit)
      then
         return;

      --  Ignore generic subprograms

      elsif Ekind (E) in Generic_Subprogram_Kind then
         return;

      --  Ignore some functions generated by the frontend for aspects
      --  Type_Invariant and Default_Initial_Condition. This does not include
      --  the functions generated for Predicate aspects, as these functions
      --  are translated to check absence of RTE in the predicate in the most
      --  general context.

      elsif Subprogram_Is_Ignored_For_Proof (E) then
         return;

      --  Ignore subprograms that front-end generates to analyze default
      --  expressions. They have no spec, only body and whose Is_Eliminated
      --  flag is set. Unlike user's subprograms with pragma Eliminated, they
      --  do come not from source. See Freeze.Process_Default_Expressions for
      --  details.

      elsif Is_Eliminated (E) and then not Comes_From_Source (E) then
         return;

      else
         if In_Pred_Function_Body then
            Current_Delayed_Aspect_Type := Etype (First_Formal (E));

            --  If the type is private and the predicate is on the full view,
            --  we should use the full view to get the correct SPARK_Mode.

            if not Has_Predicates (Current_Delayed_Aspect_Type) then
               pragma Assert
                 (Present (Full_View (Current_Delayed_Aspect_Type)));
               Current_Delayed_Aspect_Type :=
                 Full_View (Current_Delayed_Aspect_Type);
            end if;
            pragma Assert (Has_Predicates (Current_Delayed_Aspect_Type));

            Current_SPARK_Pragma :=
              SPARK_Pragma_Of_Type (Current_Delayed_Aspect_Type);

         else
            Current_SPARK_Pragma := SPARK_Pragma (Def_E);
         end if;

         SPARK_Pragma_Is_On := SPARK_Pragma_Is (Opt.On);

         --  Only analyze subprogram body declarations in SPARK_Mode => On (or
         --  while processing predicate function in discovery mode, which is
         --  recognized by the call to SPARK_Pragma_Is). An exception is made
         --  for expression functions, so that their body is translated into
         --  an axiom for analysis of its callers even in SPARK_Mode => Auto.

         if SPARK_Pragma_Is_On
           or else (Ekind (E) = E_Function
                     and then Present (Get_Expression_Function (E))
                     and then not SPARK_Pragma_Is (Opt.Off))
         then
            declare
               Save_Violation_Detected : constant Boolean :=
                 Violation_Detected;
            begin
               Violation_Detected := False;

               --  Issue warning on unreferenced local subprograms, which are
               --  analyzed anyway, unless the subprogram is marked with pragma
               --  Unreferenced.

               if Is_Local_Subprogram_Always_Inlined (E)
                 and then not Referenced (E)
                 and then not Has_Unreferenced (E)
                 and then Emit_Warning_Info_Messages
               then
                  case Ekind (E) is
                  when E_Function =>
                     Error_Msg_NE ("?analyzing unreferenced function &", N, E);

                  when E_Procedure =>
                     Error_Msg_NE
                       ("?analyzing unreferenced procedure &", N, E);

                  when others =>
                     raise Program_Error;

                  end case;
               end if;

               --  Mark Actual_Subtypes of parameters if any

               declare
                  Formals    : constant List_Id :=
                    (if Nkind (N) = N_Task_Body
                     then No_List
                     else Parameter_Specifications
                       (if Nkind (N) = N_Entry_Body
                        then Entry_Body_Formal_Part (N)
                        else Specification (N)));
                  Param_Spec : Node_Id;
                  Formal     : Node_Id;
                  Sub        : Node_Id;
               begin
                  Param_Spec := First (Formals);
                  while Present (Param_Spec) loop
                     Formal := Defining_Identifier (Param_Spec);
                     Sub := Actual_Subtype (Formal);
                     if Present (Sub)
                       and then not In_SPARK (Sub)
                     then
                        Mark_Violation (Formal, From => Sub);
                     end if;
                     Next (Param_Spec);
                  end loop;
               end;

               --  Mark entry barrier

               if Nkind (E) = N_Entry_Body then
                  --  Entry barriers in Ravenscar are always of N_Identifier
                  --  kind.
                  Mark (Condition (Entry_Body_Formal_Part (N)));
               end if;

               --  For subprogram bodies (but not other subprogram-like
               --  nodes which are also processed by this procedure) mark
               --  Refined_Post aspect if present.
               if Nkind (N) = N_Subprogram_Body then
                  declare
                     C : constant Entity_Id :=
                       Contract (Defining_Entity (Specification (N)));
                     --  ??? Def_E
                  begin
                     if Present (C) then
                        declare
                           Prag : Node_Id := Pre_Post_Conditions (C);
                        begin
                           while Present (Prag) loop
                              if Get_Pragma_Id (Prag) = Pragma_Refined_Post
                              then
                                 Mark (Expression (First (
                                       Pragma_Argument_Associations (Prag))));
                              end if;
                              Prag := Next_Pragma (Prag);
                           end loop;
                        end;
                     end if;
                  end;
               end if;

               --  Detect violations in the body itself

               Mark_Stmt_Or_Decl_List (Declarations (N));
               Mark (Handled_Statement_Sequence (N));

               --  If a violation was detected on a predicate function, then
               --  the type to which the predicate applies is not in SPARK.
               --  Remove it from the set Entities_In_SPARK if already marked
               --  in SPARK.

               if Violation_Detected then
                  if In_Pred_Function_Body then
                     Entities_In_SPARK.Exclude (Current_Delayed_Aspect_Type);
                  end if;

               else
                  --  If no violation was detected on an expression function
                  --  body, mark it as compatible with SPARK, so that its
                  --  body gets translated into an axiom for analysis of
                  --  its callers.

                  if Ekind (E) = E_Function
                    and then Present (Get_Expression_Function (E))
                  then
                     Bodies_Compatible_With_SPARK.Insert (E);
                  end if;

                  --  If no violation was detected and SPARK_Mode is On for the
                  --  body, then mark the body for translation to Why3.

                  if SPARK_Pragma_Is_On then
                     Bodies_In_SPARK.Insert (E);
                  end if;
               end if;

               Violation_Detected := Save_Violation_Detected;
            end;
         end if;

         Current_Delayed_Aspect_Type := Save_Delayed_Aspect_Type;
         Current_SPARK_Pragma := Save_SPARK_Pragma;
      end if;
   end Mark_Subprogram_Body;

   ---------------------------------
   -- Mark_Subprogram_Declaration --
   ---------------------------------

   procedure Mark_Subprogram_Declaration (N : Node_Id) is
      E : constant Entity_Id := Defining_Entity (N);

      In_Pred_Function_Decl : constant Boolean :=
        Ekind (E) = E_Function and then Is_Predicate_Function (E);
      --  Set to True iff processing declaration of a predicate function, which
      --  is generated by the front end.

   begin
      --  Ignore generic subprograms

      if Ekind (E) in Generic_Subprogram_Kind then
         return;

      --  Ignore some functions generated by the frontend for aspects
      --  Type_Invariant and Default_Initial_Condition. This does not include
      --  the functions generated for Predicate aspects, as these functions
      --  are translated to check absence of RTE in the predicate in the most
      --  general context.

      elsif Subprogram_Is_Ignored_For_Proof (E) then
         return;

      --  Ignore subprograms that front-end generates to analyze default
      --  expressions. They have no spec, only body and whose Is_Eliminated
      --  flag is set. Unlike user's subprograms with pragma Eliminated, they
      --  do come not from source. See Freeze.Process_Default_Expressions for
      --  details.

      elsif Is_Eliminated (E) and then not Comes_From_Source (E) then
         return;

      --  Mark entity

      else
         declare
            Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;

            Save_Delayed_Aspect_Type : constant Entity_Id :=
              Current_Delayed_Aspect_Type;

         begin
            if In_Pred_Function_Decl then
               Current_Delayed_Aspect_Type := Etype (First_Formal (E));

               --  If the type is private and the predicate is on the full
               --  view, we should use the full view to get the correct
               --  SPARK_Mode.

               if not Has_Predicates (Current_Delayed_Aspect_Type) then
                  pragma Assert
                    (Present (Full_View (Current_Delayed_Aspect_Type)));
                  Current_Delayed_Aspect_Type :=
                    Full_View (Current_Delayed_Aspect_Type);
               end if;
               pragma Assert (Has_Predicates (Current_Delayed_Aspect_Type));

               Current_SPARK_Pragma :=
                 SPARK_Pragma_Of_Type (Current_Delayed_Aspect_Type);

            else
               Current_SPARK_Pragma := SPARK_Pragma (E);
            end if;

            Mark_Entity (E);

            if In_Pred_Function_Decl then
               --  Type with predicate and spec of a function that implements
               --  the predicate must have the same SPARK status.
               pragma Assert
                 (In_SPARK (Current_Delayed_Aspect_Type) = In_SPARK (E));

               Current_Delayed_Aspect_Type := Save_Delayed_Aspect_Type;
            end if;

            Current_SPARK_Pragma := Save_SPARK_Pragma;
         end;
      end if;

   end Mark_Subprogram_Declaration;

   -----------------------------
   -- Mark_Subtype_Indication --
   -----------------------------

   procedure Mark_Subtype_Indication (N : Node_Id) is
      T    : constant Entity_Id := Etype (if Nkind (N) = N_Subtype_Indication
                                          then Subtype_Mark (N)
                                          else N);
      Cstr : Node_Id;

   begin
      --  Check that the base type is in SPARK

      if not In_SPARK (T) then
         Mark_Violation (N, From => T); -- ?? N? similar below
      end if;

      if Nkind (N) = N_Subtype_Indication then

         Cstr := Constraint (N);
         case Nkind (Cstr) is
            when N_Range_Constraint =>
               null;

            when N_Index_Or_Discriminant_Constraint =>

               if Is_Array_Type (T) then
                  Cstr := First (Constraints (Cstr));
                  while Present (Cstr) loop

                     case Nkind (Cstr) is
                     when N_Identifier | N_Expanded_Name =>
                        if not In_SPARK (Entity (Cstr)) then
                           Mark_Violation (N, From => Entity (Cstr));
                        end if;

                     when N_Subtype_Indication =>
                        if not In_SPARK (Subtype_Mark (Cstr)) then
                           Mark_Violation (N, From => Subtype_Mark (Cstr));
                        end if;

                     when N_Range =>
                        null;

                     when others =>
                        raise Program_Error;
                     end case;
                     Next (Cstr);
                  end loop;

               --  Note that a discriminant association that has no selector
               --  name list appears directly as an expression in the tree.

               else
                  null;
               end if;

            when N_Digits_Constraint
               | N_Delta_Constraint
            =>
               null;

            when others =>  --  TO DO ???
               raise Program_Error;
         end case;
      end if;
   end Mark_Subtype_Indication;

   -------------------
   -- Mark_Unary_Op --
   -------------------

   procedure Mark_Unary_Op (N : Node_Id) is
   begin
      Mark (Right_Opnd (N));
   end Mark_Unary_Op;

   ----------------------
   -- Mark_Unsupported --
   ----------------------

   procedure Mark_Unsupported
     (Msg        : String;
      N          : Node_Id;
      Extra_Name : Name_Id := No_Name;
      Extra_Num  : Uint    := No_Uint;
      Extra_Node : Node_Id := Empty;
      Cont_Msg   : String  := "")
   is
   begin
      --  Flag the violation, so that the current entity is marked accordingly

      Violation_Detected := True;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
         Error_Msg_Name_1 := Extra_Name;
         Error_Msg_Uint_1 := Extra_Num;
         Error_Msg_Node_1 := Extra_Node;
         Error_Msg_N (Msg & " is not yet supported", N);

         if Cont_Msg /= "" then
            Error_Msg_N ('\' & Cont_Msg, N);
         end if;
      end if;
   end Mark_Unsupported;

   --------------------
   -- Mark_Violation --
   --------------------

   procedure Mark_Violation
     (Msg           : String;
      N             : Node_Id;
      SRM_Reference : String := "") is
   begin
      --  Flag the violation, so that the current entity is marked accordingly

      Violation_Detected := True;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then

         if SRM_Reference /= "" then
            Error_Msg_F
              (Msg & " is not allowed in SPARK (" & SRM_Reference & ")", N);
         else
            Error_Msg_F (Msg & " is not allowed in SPARK", N);
         end if;

         Mark_Violation_Of_SPARK_Mode (N);
      end if;
   end Mark_Violation;

   procedure Mark_Violation
     (N    : Node_Id;
      From : Entity_Id) is
   begin
      --  Flag the violation, so that the current entity is marked accordingly

      Violation_Detected := True;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
         Error_Msg_FE ("& is not allowed in SPARK", N, From);

         Mark_Violation_Of_SPARK_Mode (N);
      end if;
   end Mark_Violation;

   ----------------------------
   -- Mark_Violation_In_Tasking --
   ----------------------------

   procedure Mark_Violation_In_Tasking (N : Node_Id) is
      Msg_Prefix : constant String := "tasking in SPARK requires ";
      Msg_Suffix : constant String := " (SPARK RM 9(2))";
   begin
      --  Flag the violation, so that the current entity is marked accordingly

      Violation_Detected := True;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then

         if not GNATprove_Tasking_Profile then
            Error_Msg_F (Msg_Prefix &
                           "Ravenscar profile" & Msg_Suffix, N);
         elsif not Sequential_Elaboration then
            Error_Msg_F (Msg_Prefix &
                           "sequential elaboration" & Msg_Suffix, N);
         end if;

         Mark_Violation_Of_SPARK_Mode (N);
      end if;
   end Mark_Violation_In_Tasking;

   ----------------------------------
   -- Mark_Violation_Of_SPARK_Mode --
   ----------------------------------

   procedure Mark_Violation_Of_SPARK_Mode (N : Node_Id) is
   begin
      if Present (Current_SPARK_Pragma) then
         Error_Msg_Sloc := Sloc (Current_SPARK_Pragma);

         Error_Msg_F ("\\violation of " &
                      (if From_Aspect_Specification (Current_SPARK_Pragma)
                       then "aspect"
                       else "pragma") &
                      " SPARK_Mode #", N);
      else
         pragma Assert (Present (Current_Delayed_Aspect_Type));
         Error_Msg_Sloc := Sloc (Current_Delayed_Aspect_Type);

         Error_Msg_FE
           ("\\delayed type aspect on & is required to be in SPARK", N,
            Current_Delayed_Aspect_Type);
      end if;
   end Mark_Violation_Of_SPARK_Mode;

   ----------------------------------
   -- Most_Underlying_Type_In_SPARK --
   ----------------------------------

   procedure Mark_Most_Underlying_Type_In_SPARK
     (Id : Entity_Id;
      N  : Node_Id)
   is
   begin
      if not Retysp_In_SPARK (Id) then
         Mark_Violation (N, From => Retysp (Id));
      end if;
   end Mark_Most_Underlying_Type_In_SPARK;

   --------------
   -- In_SPARK --
   --------------

   function Retysp_In_SPARK (E : Entity_Id) return Boolean is
   begin
      Mark_Entity (E);
      Mark_Entity (Retysp (E));
      return Entities_In_SPARK.Contains (Retysp (E));
   end Retysp_In_SPARK;

   ---------------------
   -- SPARK_Pragma_Is --
   ---------------------

   function SPARK_Pragma_Is (Mode : Opt.SPARK_Mode_Type) return Boolean is
     (if Present (Current_Delayed_Aspect_Type)
        and then In_SPARK (Current_Delayed_Aspect_Type)
      then Mode = Opt.On
      --  Force SPARK_Mode => On for expressions of a delayed aspects, if the
      --  type bearing this aspect was marked in SPARK, as we have assumed
      --  it when marking everything between their declaration and freezing
      --  point, so we cannot revert that.

      elsif Present (Current_SPARK_Pragma)
      then Get_SPARK_Mode_From_Annotation (Current_SPARK_Pragma) = Mode
      --  In the usual case where Current_SPARK_Pragma is a pragma node, get
      --  the current mode from the pragma.

      else Mode = Opt.None
      --  Otherwise there is no applicable pragma, so SPARK_Mode is None
     );

   --------------------------
   -- SPARK_Pragma_Of_Type --
   --------------------------

   function SPARK_Pragma_Of_Type (E : Entity_Id) return Node_Id is

      function Lexical_Scope (E : Entity_Id) return Entity_Id is
        (Defining_Entity
           (Enclosing_Declaration
              (Parent
                 (Enclosing_Declaration
                    (E)))));
      --  Version of Einfo.Scope that returns the lexical scope instead of the
      --  semantic scope for an entity. For example, it returns the package
      --  body entity for an entity declared directly in the body of a
      --  package, instead of the package entity. It is important for returning
      --  the appropriate SPARK_Mode pragma, which may be different for a
      --  declaration and its corresponding body.

      Def : Entity_Id := E;
      --  Entity which defines type E

      Def_Scop : Entity_Id := Lexical_Scope (E);
      --  Immediate scope of the entity that defines E

      subtype SPARK_Pragma_Scope_With_Type_Decl is Entity_Kind
        with Static_Predicate =>
               SPARK_Pragma_Scope_With_Type_Decl in
                  E_Entry           |
                  E_Entry_Family    |
                  E_Function        |
                  E_Package         |
                  E_Package_Body    |
                  E_Procedure       |
                  E_Subprogram_Body |
                  E_Task_Body;

   begin
      while Ekind (Def_Scop) not in SPARK_Pragma_Scope_With_Type_Decl
      loop
         Def := Def_Scop;
         Def_Scop := Lexical_Scope (Def_Scop);
      end loop;

      case Ekind (Def_Scop) is
         when E_Package =>
            if List_Containing (Parent (Def)) =
              Private_Declarations (Package_Specification (Def_Scop))
            then
               return SPARK_Aux_Pragma (Def_Scop);
            end if;

         when E_Package_Body =>
            if List_Containing (Parent (Def)) =
              Statements (
                Handled_Statement_Sequence (Package_Body (Def_Scop)))
            then
               return SPARK_Aux_Pragma (Def_Scop);
            end if;

         when others =>
            null;
      end case;

      return SPARK_Pragma (Def_Scop);

   end SPARK_Pragma_Of_Type;

   ----------------------------------------------------------------------
   --  Iterators
   ----------------------------------------------------------------------

   ------------------
   -- First_Cursor --
   ------------------

   function First_Cursor (Kind : Entity_Collection) return Cursor is
     (case Kind is
         when Entities_To_Translate =>
            Cursor'(Kind                       => Entities_To_Translate,
                    Entity_To_Translate_Cursor => Entity_List.First),

         when Marked_Entities =>
            Cursor'(Kind                       => Marked_Entities,
                    Marked_Entities_Cursor     => Entity_Set.First));

   -----------------
   -- Next_Cursor --
   -----------------

   function Next_Cursor (Kind : Entity_Collection;
                         C    : Cursor)
                         return Cursor is
     (case Kind is
         when Entities_To_Translate =>
            Cursor'(Kind => Entities_To_Translate,
                    Entity_To_Translate_Cursor =>
                      Node_Lists.Next (C.Entity_To_Translate_Cursor)),

          when Marked_Entities =>
             Cursor'(Kind => Marked_Entities,
                     Marked_Entities_Cursor     =>
                       Hashed_Node_Sets.Next (C.Marked_Entities_Cursor)));

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (Kind : Entity_Collection;
                         C    : Cursor)
                         return Boolean is
     (case Kind is
         when Entities_To_Translate =>
            Node_Lists.Has_Element (C.Entity_To_Translate_Cursor),

         when Marked_Entities =>
            Hashed_Node_Sets.Has_Element (C.Marked_Entities_Cursor));

   -----------------
   -- Get_Element --
   -----------------

   function Get_Element (Kind : Entity_Collection;
                         C    : Cursor)
                         return Entity_Id is
     (case Kind is
         when Entities_To_Translate =>
            Node_Lists.Element (C.Entity_To_Translate_Cursor),

         when Marked_Entities =>
            Hashed_Node_Sets.Element (C.Marked_Entities_Cursor));

end SPARK_Definition;
