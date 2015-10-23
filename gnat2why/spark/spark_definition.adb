------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      S P A R K _ D E F I N I T I O N                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                      Copyright (C) 2011-2015, AdaCore                    --
--                      Copyright (C) 2015, Altran UK Limited               --
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

with Ada.Text_IO;          use Ada.Text_IO;
with Aspects;              use Aspects;
with Assumption_Types;     use Assumption_Types;
with Elists;               use Elists;
with Errout;               use Errout;
with Exp_Util;             use Exp_Util;
with Fname;                use Fname;
with Gnat2Why.Annotate;    use Gnat2Why.Annotate;
with Gnat2Why.Assumptions; use Gnat2Why.Assumptions;
with Gnat2Why_Args;
with Lib;                  use Lib;
with Namet;                use Namet;
with Nlists;               use Nlists;
with Nmake;                use Nmake;
with Opt;                  use Opt;
with Restrict;             use Restrict;
with Rident;               use Rident;
with Sem_Aux;              use Sem_Aux;
with Sem_Ch12;             use Sem_Ch12;
with Sem_Disp;             use Sem_Disp;
with Sem_Prag;             use Sem_Prag;
with Sem_Util;             use Sem_Util;
with Snames;               use Snames;
with SPARK_Util;           use SPARK_Util;
with Stand;                use Stand;
with Uintp;                use Uintp;
with Urealp;               use Urealp;

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
   --  . for all other types, itself
   --  until reaching a non-private type that is not a record subtype.

   --  Partial views of deferred constants may be in SPARK even if their full
   --  view is not in SPARK. This is the case if the type of the constant is
   --  in SPARK, while its initializing expression is not.

   -------------------------------------
   -- Adding Entities for Translation --
   -------------------------------------

   Current_SPARK_Pragma : Node_Id;
   --  The current applicable SPARK_Mode pragma, if any, to reference in error
   --  messages when a violation is encountered. For analysis of the delayed
   --  aspects of a type T on discovery mode, this variable holds T's entity.

   Violation_Detected : Boolean;
   --  Set to True when a violation is detected

   Inside_Actions : Boolean;
   --  Set to True when traversing actions (statements introduced by the
   --  compiler inside expressions), which require a special translation.
   --  Those entities are stored in Actions_Entity_Set.

   SPARK_Status_JSON : JSON_Array := Empty_Array;

   procedure Initialize;

   function SPARK_Pragma_Is (Mode : Opt.SPARK_Mode_Type) return Boolean;
   --  Returns whether Current_SPARK_Pragma is not Empty, and corresponds to
   --  the given Mode.

   --  There are two possibilities when marking an entity, depending on whether
   --  this is in the context of a toplevel subprogram body or not. In the
   --  first case, violations are directly attached to the toplevel subprogram
   --  entity, and local entities are added or not as a whole, after the
   --  subprogram body has been fully marked. In the second case, violations
   --  are attached to the entity itself, which is directly added to the lists
   --  for translation after marking.

   Entities_In_SPARK  : Node_Sets.Set;
   --  Entities in SPARK. An entity is added to this set if, after marking,
   --  no violations where attached to the corresponding scope. Standard
   --  entities are individually added to this set.

   Specs_In_SPARK     : Node_Sets.Set;
   --  Defining entities of subprograms, entries and packages whose spec is
   --  marked in SPARK.

   Bodies_In_SPARK    : Node_Sets.Set;
   --  Unique defining entities of subprograms, entries, tasks and packages
   --  whose body is marked in SPARK.

   Bodies_Valid_SPARK : Node_Sets.Set;
   --  Unique defining entities of subprograms, entries and tasks whose body
   --  contains no SPARK violations (but not package bodies because they are
   --  never called).

   Full_Views_Not_In_SPARK : Node_Maps.Map;
   --  Maps type entities in SPARK whose full view was declared in a private
   --  part with SPARK_Mode => Off or a subtype or derived type of such an
   --  entity to its first ancester in SPARK.

   Delayed_Type_Aspects : Node_Maps.Map;
   --  Stores subprograms from aspects of types whose analysis should be
   --  delayed until the end of the analysis and maps them either to their
   --  SPARK_Mode entity if there is one or to their type entity in discovery
   --  mode.

   Loop_Entity_Set : Node_Sets.Set;
   --  Set of entities defined in loops before the invariant, which may require
   --  a special translation. See gnat2why.ads for details.

   Actions_Entity_Set : Node_Sets.Set;
   --  Set of entities defined in actions which require a special translation.
   --  See gnat2why.ads for details.

   function Entity_In_SPARK (E : Entity_Id) return Boolean is
     (Entities_In_SPARK.Contains (E));

   function Entity_Marked (E : Entity_Id) return Boolean is
     (Entity_Set.Contains (E));

   function Entity_Spec_In_SPARK (E : Entity_Id) return Boolean is
     (Specs_In_SPARK.Contains (E));

   function Entity_Body_In_SPARK (E : Entity_Id) return Boolean is
     (Bodies_In_SPARK.Contains (E));

   function Entity_Body_Valid_SPARK (E : Entity_Id) return Boolean is
     (Bodies_Valid_SPARK.Contains (E));

   function Full_View_Not_In_SPARK (E : Entity_Id) return Boolean is
     (Full_Views_Not_In_SPARK.Contains (E));

   function Is_Loop_Entity (E : Entity_Id) return Boolean is
     (Loop_Entity_Set.Contains (E));

   function Is_Actions_Entity (E : Entity_Id) return Boolean is
     (Actions_Entity_Set.Contains (E));

   procedure Discard_Underlying_Type (T : Entity_Id);
   --  Mark T's underlying type as seen and store T as its partial view

   ----------------------
   -- SPARK Violations --
   ----------------------

   procedure Mark_Violation
     (Msg           : String;
      N             : Node_Id;
      SRM_Reference : String := "");
   --  Mark node N as a violation of SPARK. An error message pointing to the
   --  current SPARK_Mode pragma/aspect is issued if current SPARK_Mode is On.
   --  If SRM_Reference is set, the reference to the SRM is appended to the
   --  error message.

   procedure Mark_Violation
     (N    : Node_Id;
      From : Entity_Id);
   --  Mark node N as a violation of SPARK, due to the use of entity From which
   --  is not in SPARK. An error message is issued if current SPARK_Mode is On.

   procedure Mark_Violation_In_Tasking
     (N : Node_Id)
     with Pre => not Is_SPARK_Tasking_Configuration;
   --  Mark node N as a violation of SPARK because of unsupported tasking
   --  configuration. An error message is issued if current SPARK_Mode is On.

   procedure Mark_Violation_Of_SPARK_Mode (N : Node_Id);
   --  Issue an error continuation message for node N with the location of the
   --  violated SPARK_Mode pragma/aspect.

   Ravenscar_Profile_Result : Boolean := False;
   --  This switch memoizes the result of Ravenscar_Profile function calls for
   --  improved efficiency. Valid only if Ravenscar_Profile_Cached is True.
   --  Note: if this switch is ever set True, it is never turned off again.

   Ravenscar_Profile_Cached : Boolean := False;
   --  This flag is set to True if the Ravenscar_Profile_Result contains the
   --  correct cached result of Ravenscar_Profile calls.

   function Ravenscar_Profile return Boolean;
   --  Tests if configuration pragmas and restrictions corresponding to Profile
   --  (Ravenscar) are currently in effect (set by pragma Profile, or by an
   --  appropriate set of individual Restrictions pragmas). Returns True only
   --  if all the required settings are set.

   function Sequential_Elaboration return Boolean;
   --  Check if Partition_Elaboration_Policy is set to Sequential

   function Is_SPARK_Tasking_Configuration return Boolean;
   --  Check tasking configuration required by SPARK and possibly
   --  mark violation on node N.

   function Is_SPARK_Tasking_Configuration return Boolean
   is (Ravenscar_Profile and then Sequential_Elaboration);

   -----------------------
   -- Ravenscar_Profile --
   -----------------------

   --  Check that the current settings match those in
   --  Sem_Prag.Set_Ravenscar_Profile.
   --  ??? Older versions of Ada are also supported to ease reuse once this
   --  code is moved to Restrict package.

   function Ravenscar_Profile return Boolean is
      Prefix_Entity   : Entity_Id;
      Selector_Entity : Entity_Id;
      Prefix_Node     : Node_Id;
      Node            : Node_Id;

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
            R : Restriction_Flags  renames Profile_Info (Ravenscar).Set;
            V : Restriction_Values renames Profile_Info (Ravenscar).Value;
         begin
            for J in R'Range loop
               if R (J)
                 and then (Restrictions.Set (J) = False
                             or else Restriction_Warnings (J)
                             or else
                               (J in All_Parameter_Restrictions
                                  and then Restrictions.Value (J) > V (J)))
               then
                  Ravenscar_Profile_Result := False;
                  return False;
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
   end Ravenscar_Profile;

   ----------------------------
   -- Sequential_Elaboration --
   ----------------------------

   function Sequential_Elaboration return Boolean
   is (Partition_Elaboration_Policy = 'S');

   ------------------------------
   -- Output SPARK Information --
   ------------------------------

   procedure Generate_Output_In_Out_SPARK (Id : Entity_Id);

   ----------------------------------
   -- Recursive Marking of the AST --
   ----------------------------------

   procedure Mark (N : Node_Id);
   --  Generic procedure for marking code

   function In_SPARK (E : Entity_Id) return Boolean;
   --  Returns whether the entity E is in SPARK; computes this information by
   --  calling Mark_Entity, which is very cheap.

   procedure Mark_Entity (E : Entity_Id);
   --  Push entity E on the stack, mark E, and pop E from the stack. Always
   --  adds E to the set of Entity_Set as a result. If no violation was
   --  detected, E is added to the Entities_In_SPARK.

   --  Marking of declarations

   procedure Mark_Number_Declaration          (N : Node_Id);
   procedure Mark_Object_Declaration          (N : Node_Id);

   procedure Mark_Package_Body                (N : Node_Id);
   procedure Mark_Package_Declaration         (N : Node_Id);

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
   procedure Mark_Call                        (N : Node_Id);
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

   procedure Mark_Actions (N : Node_Id; L : List_Id);
   --  Mark a possibly null list of actions L from expression N. It should be
   --  called before the expression to which the actions apply is marked, so
   --  that declarations of constants in actions are possibly marked in SPARK.

   procedure Mark_List (L : List_Id);
   --  Call Mark on all nodes in list L

   procedure Mark_Most_Underlying_Type_In_SPARK (Id : Entity_Id; N : Node_Id);
   --  The most underlying type for type Id should be in SPARK, otherwise mark
   --  node N as not in SPARK.

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

   ----------------------------------
   -- Generate_Output_In_Out_SPARK --
   ----------------------------------

   procedure Generate_Output_In_Out_SPARK (Id : Entity_Id) is
   begin
      --  Only add infomation for Id if analysis is requested for that
      --  subprogram or package. Then, absence of errors in flow and warnings
      --  in proof for that subprogram/package can be interpreted as correct
      --  flow analysis or proof of that entity.

      if Analysis_Requested (Id, With_Inlined => True) then
         declare
            V : constant JSON_Value := To_JSON (Entity_To_Subp (Id));
            SPARK_Status : constant String :=
              (if Entity_Body_In_SPARK (Id) then "all"
               elsif Entity_Spec_In_SPARK (Id) then
                   (if Ekind (Id) = E_Package
                    and then
                    No (Package_Body (Id))
                    then "all" else "spec")
               else "no");
         begin
            Set_Field (V, "spark", SPARK_Status);
            Append (SPARK_Status_JSON, V);
         end;
      end if;
   end Generate_Output_In_Out_SPARK;

   ---------------------------------
   -- Get_First_Ancestor_In_SPARK --
   ---------------------------------

   function Get_First_Ancestor_In_SPARK (E : Entity_Id) return Entity_Id is
     (Full_Views_Not_In_SPARK.Element (E));

   --------------------
   -- Get_SPARK_JSON --
   --------------------

   function Get_SPARK_JSON return JSON_Array is (SPARK_Status_JSON);

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
      --  Checks that no non-scalar object declaration or nested loop appears
      --  before the last loop-invariant or variant in a loop's list of
      --  statements. Also stores scalar objects declared before the last
      --  loop-invariant in Loop_Entity_Set.
      --  Nested should be true when checking statements coming from a nested
      --  construct of the loop (if, case, and extended return statements).

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

         N          : Node_Id;
      begin

         for Cur in reverse Loop_Stmts.Iterate loop
            N := Element (Cur);

            if not Inv_Found then

               --  Find last loop invariant/variant from the loop

               if Is_Pragma_Check (N, Name_Loop_Invariant)
                 or else Is_Pragma (N, Pragma_Loop_Variant)
               then
                  Inv_Found := True;
               end if;
            else

               --  Check that there are no nested loops and non-scalar objects
               --  declarations before the last invariant/variant.

               case Nkind (N) is
                  when N_Full_Type_Declaration         |
                       N_Private_Extension_Declaration |
                       N_Private_Type_Declaration      |
                       N_Subtype_Declaration           =>
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
                        Violation_Detected := True;
                        if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                           Error_Msg_N
                             ("non-scalar objects declared before "
                              & "loop-invariant not yet supported", N);
                        end if;
                     end if;
                  when N_Loop_Statement =>
                     Violation_Detected := True;
                     if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                        Error_Msg_N
                          ("nested loops before loop-invariant not yet "
                             & "supported", N);
                     end if;
                  when N_Package_Declaration =>
                     Violation_Detected := True;
                     if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                        Error_Msg_N
                          ("nested packages before loop-invariant not yet "
                             & "supported", N);
                     end if;
                  when N_Subprogram_Declaration | N_Subprogram_Body =>
                     Violation_Detected := True;
                     if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                        Error_Msg_N
                          ("nested subprograms before loop-invariant not yet "
                             & "supported", N);
                     end if;

                     --  Go inside if, case, and exended return statements to
                     --  check for absence of non-scalar object declarations
                     --  and nested loops.

                  when N_If_Statement =>
                     Check_Loop_Invariant_Placement
                       (Then_Statements (N), True);
                     if Present (Elsif_Parts (N)) then
                        declare
                           Cur : Node_Id := First (Elsif_Parts (N));
                        begin
                           while Present (Cur) loop
                              Check_Loop_Invariant_Placement
                                (Then_Statements (Cur), True);
                              Next (Cur);
                           end loop;
                        end;
                     end if;
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
      --  Dispatch on node kind

      case Nkind (N) is

         when N_Abstract_Subprogram_Declaration =>
            Mark_Subprogram_Declaration (N);

         when N_Aggregate =>
            if not Is_Update_Aggregate (N)
              and then not Is_Special_Multidim_Update_Aggr (N)
            then
               if not Aggregate_Is_Fully_Initialized (N) then
                  Mark_Violation ("aggregate not fully defined", N,
                                  SRM_Reference => "SPARK RM 4.3");
               end if;
               Mark_Most_Underlying_Type_In_SPARK (Etype (N), N);
            elsif Is_Update_Aggregate (N)
              and then Is_Update_Unconstr_Multidim_Aggr (N)
            then
               Error_Msg_Name_1 := Name_Update;
               Error_Msg_N
                 ("attribute % of unconstrained multidimensional array "
                    & "is not yet supported",
                  N);
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

         when N_Case_Expression |
              N_Case_Statement  =>
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

         when N_Component_Declaration =>
            Mark_Component_Declaration (N);

         when N_Delay_Until_Statement =>
            if Is_SPARK_Tasking_Configuration then
               Mark (Expression (N));
            else
               Mark_Violation_In_Tasking (N);
            end if;

         when N_Exit_Statement =>
            if Present (Condition (N)) then
               Mark (Condition (N));
            end if;

         when N_Expanded_Name =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_Explicit_Dereference =>
            Mark_Violation ("explicit dereference", N);

         when N_Extended_Return_Statement =>
            Mark_Extended_Return_Statement (N);

         when N_Extension_Aggregate =>
            if not Aggregate_Is_Fully_Initialized (N) then
               Mark_Violation ("extension aggregate not fully defined", N,
                               SRM_Reference => "SPARK RM 4.3");
            end if;
            Mark_Most_Underlying_Type_In_SPARK (Etype (N), N);

            if Nkind (Ancestor_Part (N)) in N_Identifier | N_Expanded_Name
              and then Is_Type (Entity (Ancestor_Part (N)))
            then

               --  The ancestor part of an aggregate can be either an
               --  expression or a subtype.
               --  The second case is not currently supported in SPARK.

               Violation_Detected := True;
               if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                  Error_Msg_N ("extension aggregate with subtype ancestor "
                               & "part is not yet supported",
                               N);
               end if;
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

         when N_Identifier =>
            Mark_Identifier_Or_Expanded_Name (N);

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

--                    if Of_Present (N) then
--                       Violation_Detected := True;
--                       if SPARK_Pragma_Is (Opt.On) then
--                          Error_Msg_N
--                       ("Of quantification on types with Iterable aspect"
--                             & " is not yet supported",
--                             N);
--                       end if;
--                    end if;

                  --  Mark components of the Iterable aggregate

                  declare
                     Iterable_Component_Assoc : constant List_Id :=
                       Component_Associations (Expression
                                               (Iterable_Aspect));
                     Iterable_Field : Node_Id :=
                       First (Iterable_Component_Assoc);

                  begin

                     while Present (Iterable_Field) loop
                        Mark (Expression (Iterable_Field));
                        Next (Iterable_Field);
                     end loop;

                  end;

                  Mark (Name (N));

               elsif Of_Present (N)
                 and then Has_Array_Type (Etype (Name (N)))
               then
                  if Number_Dimensions (Etype (Name (N))) > 1 then
                     Violation_Detected := True;
                     if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                        Error_Msg_Uint_1 :=
                          UI_From_Int (Number_Dimensions (Etype (Name (N))));
                        Error_Msg_N ("iterator specification over array of "
                                     & "dimension ^ is not yet supported",
                                     N);
                     end if;
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
               Violation_Detected := True;
               if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                  Error_Msg_N
                    ("membership test on array values is not yet supported",
                     N);
               end if;
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
               Selector    : constant Entity_Id := Entity (Selector_Name (N));
               Prefix_Type : constant Entity_Id :=
                 Unique_Entity (Etype (Prefix (N)));
            begin
               if Has_Access_Type (Prefix_Type) then
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
              or else In_SPARK (Retysp (Etype (Prefix (N))))
            then
               Mark_Most_Underlying_Type_In_SPARK (Etype (Prefix (N)), N);
            elsif Ekind (Entity (Selector_Name (N))) /= E_Discriminant then
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

         when N_Type_Conversion =>
            if Has_Array_Type (Etype (N)) then
               declare
                  Target_Comp_Typ : constant Entity_Id :=
                    Retysp (Component_Type (Retysp (Etype (N))));
                  Source_Comp_Typ : constant Entity_Id :=
                    Retysp (Component_Type (Retysp (Etype (Expression (N)))));
               begin
                  if Target_Comp_Typ /= Source_Comp_Typ then
                     Violation_Detected := True;
                     if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                        Error_Msg_N
                          ("conversion between array types that have "
                           & "different element types is not yet supported",
                           N);
                     end if;
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
                  Source_Index : Node_Id :=
                    First_Index (Retysp (Etype (Expression (N))));
                  Dim          : constant Positive :=
                    Positive (Number_Dimensions (Retysp (Etype (N))));
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
                           Violation_Detected := True;
                           if Emit_Messages and then SPARK_Pragma_Is (Opt.On)
                           then
                              Error_Msg_N
                                ("this conversion between array types is not "
                                 & "yet supported", N);
                           end if;
                           exit;
                        end if;

                     elsif Has_Modular_Integer_Type (Target_Type)
                             or else
                           Has_Modular_Integer_Type (Source_Type)
                     then
                        Violation_Detected := True;
                        if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                           Error_Msg_N
                             ("this conversion between array types is not "
                              & "yet supported", N);
                        end if;
                        exit;
                     end if;

                     Target_Index := Next_Index (Target_Index);
                     Source_Index := Next_Index (Source_Index);
                  end loop;
               end;

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
                     Violation_Detected := True;
                     if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                        Error_Msg_N
                          ("conversion between different fixed-point types "
                           & "is not yet supported", N);
                     end if;
                  end if;
               end;
            end if;

            Mark (Expression (N));

         when N_Unary_Op =>
            Mark_Unary_Op (N);

         when N_Unchecked_Type_Conversion =>
            Mark (Expression (N));

            --  Source unchecked type conversion nodes were rewritten as such
            --  by SPARK_Rewrite.Rewrite_Call, keeping the original call to an
            --  instance of Unchecked_Conversion as the Original_Node of the
            --  new N_Unchecked_Type_Conversion node, and marking the node as
            --  coming from source. We translate this original node to Why, so
            --  it should be in SPARK too.

            if Comes_From_Source (N) then
               Mark (Original_Node (N));
            end if;

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

         when N_Full_Type_Declaration         |
              N_Private_Extension_Declaration |
              N_Private_Type_Declaration      |
              N_Protected_Type_Declaration    |
              N_Subtype_Declaration           |
              N_Task_Type_Declaration         =>

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
                 and then not Is_Full_View (Full_View (E)) -- ??? why needed?
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
               then

                  --  Only mark the classwide type associated to a record type
                  --  if the record type isn't constrained. Otherwise, the
                  --  classwide type is not in SPARK and should not be used.

                  if not Has_Discriminants (E)
                    or else not Is_Constrained (E)
                  then
                     Mark_Entity (Class_Wide_Type (E));
                  end if;
                  Set_Specific_Tagged (Class_Wide_Type (E), E);
               end if;

               Mark_Entity (E);
               if Is_Itype (BT) then
                  Mark_Entity (BT);
               end if;

               --  We avoid marking the subprograms of a protected type when
               --  marked the type entity. Instead, we do it here directly on
               --  the type declaration. This is needed to avoid that certain
               --  pure functions are declared before the type in Why.

               if Ekind (E) in Protected_Kind then
                  Mark_Stmt_Or_Decl_List
                    (Visible_Declarations (Protected_Definition (N)));
               end if;

            end;

         --  Supported tasking constructs

         when N_Protected_Body |
              N_Task_Body      =>
            if Is_SPARK_Tasking_Configuration then
               declare
                  Spec : constant Entity_Id := Corresponding_Spec (N);
               begin
                  --  For entries, functions and procedures of protected types
                  --  detect also violations in the enclosing type, which acts
                  --  as an implicit argument to these subprograms.

                  if Entity_In_SPARK (Spec) then
                     case Nkind (N) is
                        when N_Protected_Body =>
                           Mark_Stmt_Or_Decl_List (Declarations (N));

                        when N_Task_Body =>
                           Mark_Subprogram_Body (N);

                        when others =>
                           raise Program_Error;

                     end case;
                  else
                     Mark_Violation (N, From => Spec);
                  end if;
               end;
            else
               Mark_Violation_In_Tasking (N);
            end if;

         when N_Protected_Body_Stub |
              N_Task_Body_Stub      =>
            if Is_SPARK_Tasking_Configuration then
               Mark (Get_Body_From_Stub (N));
            else
               Mark_Violation_In_Tasking (N);
            end if;

         when N_Entry_Body =>
            if Is_SPARK_Tasking_Configuration then
               if Ekind (Unique_Defining_Entity (N)) /= E_Entry_Family then
                  Mark_Subprogram_Body (N);
               else
                  Mark_Violation ("entry family", N);
               end if;
            else
               Mark_Violation_In_Tasking (N);
            end if;

         when N_Entry_Call_Statement =>
            if Is_SPARK_Tasking_Configuration then
               Mark_Call (N);
            else
               Mark_Violation_In_Tasking (N);
            end if;

         when N_Entry_Declaration =>
            if Is_SPARK_Tasking_Configuration then
               if Ekind (Defining_Entity (N)) /= E_Entry_Family then
                  Mark_Subprogram_Declaration (N);
               else
                  Mark_Violation ("entry family", N);
               end if;
            else
               Mark_Violation_In_Tasking (N);
            end if;

         --  Unsupported tasking constructs

         when N_Abort_Statement          |
              N_Accept_Statement         |
              N_Asynchronous_Select      |
              N_Conditional_Entry_Call   |
              N_Delay_Relative_Statement |
              N_Requeue_Statement        |
              N_Selective_Accept         |
              N_Timed_Entry_Call         =>
            Mark_Violation ("tasking", N);

         --  The following kinds can be safely ignored by marking

         when N_At_Clause                              |
              N_Attribute_Definition_Clause            |
              N_Character_Literal                      |
              N_Enumeration_Representation_Clause      |
              N_Exception_Declaration                  |
              N_Exception_Renaming_Declaration         |
              N_Formal_Object_Declaration              |
              N_Formal_Package_Declaration             |
              N_Formal_Subprogram_Declaration          |
              N_Formal_Type_Declaration                |
              N_Freeze_Entity                          |
              N_Freeze_Generic_Entity                  |
              N_Function_Instantiation                 |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Package_Declaration            |
              N_Generic_Package_Renaming_Declaration   |
              N_Generic_Procedure_Renaming_Declaration |
              N_Generic_Subprogram_Declaration         |
              N_Implicit_Label_Declaration             |
              N_Incomplete_Type_Declaration            |
              N_Itype_Reference                        |
              N_Label                                  |
              N_Null_Statement                         |
              N_Operator_Symbol                        |
              N_Others_Choice                          |
              N_Package_Instantiation                  |
              N_Package_Renaming_Declaration           |
              N_Procedure_Instantiation                |
              N_Record_Representation_Clause           |
              N_String_Literal                         |
              N_Subprogram_Renaming_Declaration        |
              N_Use_Package_Clause                     |
              N_With_Clause                            |
              N_Use_Type_Clause                        |
              N_Validate_Unchecked_Conversion          =>
            null;

         when N_Real_Literal |
           N_Integer_Literal =>

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

         when N_Expression_Function          |
              N_Single_Protected_Declaration |
              N_Single_Task_Declaration      =>
            raise Program_Error;

         --  The following nodes are never generated in GNATprove mode

         when N_Expression_With_Actions |
              N_Compound_Statement      |
              N_Unchecked_Expression    =>
            raise Program_Error;

         --  Mark should not be called on other kinds

         when N_Abortable_Part                         |
              N_Accept_Alternative                     |
              N_Access_Definition                      |
              N_Access_Function_Definition             |
              N_Access_Procedure_Definition            |
              N_Access_To_Object_Definition            |
              N_Aspect_Specification                   |
              N_Compilation_Unit                       |
              N_Compilation_Unit_Aux                   |
              N_Component_Clause                       |
              N_Component_Definition                   |
              N_Component_List                         |
              N_Constrained_Array_Definition           |
              N_Contract                               |
              N_Decimal_Fixed_Point_Definition         |
              N_Defining_Character_Literal             |
              N_Defining_Identifier                    |
              N_Defining_Operator_Symbol               |
              N_Defining_Program_Unit_Name             |
              N_Delay_Alternative                      |
              N_Delta_Constraint                       |
              N_Derived_Type_Definition                |
              N_Designator                             |
              N_Digits_Constraint                      |
              N_Discriminant_Association               |
              N_Discriminant_Specification             |
              N_Function_Specification                 |
              N_Iteration_Scheme                       |
              N_Loop_Parameter_Specification           |
              N_Elsif_Part                             |
              N_Empty                                  |
              N_Entry_Body_Formal_Part                 |
              N_Enumeration_Type_Definition            |
              N_Entry_Call_Alternative                 |
              N_Entry_Index_Specification              |
              N_Error                                  |
              N_Exception_Handler                      |
              N_Floating_Point_Definition              |
              N_Formal_Decimal_Fixed_Point_Definition  |
              N_Formal_Derived_Type_Definition         |
              N_Formal_Discrete_Type_Definition        |
              N_Formal_Floating_Point_Definition       |
              N_Formal_Incomplete_Type_Definition      |
              N_Formal_Modular_Type_Definition         |
              N_Formal_Ordinary_Fixed_Point_Definition |
              N_Formal_Private_Type_Definition         |
              N_Formal_Signed_Integer_Type_Definition  |
              N_Generic_Association                    |
              N_Index_Or_Discriminant_Constraint       |
              N_Mod_Clause                             |
              N_Modular_Type_Definition                |
              N_Ordinary_Fixed_Point_Definition        |
              N_Parameter_Specification                |
              N_Pragma_Argument_Association            |
              N_Package_Specification                  |
              N_Procedure_Specification                |
              N_Protected_Definition                   |
              N_Push_Pop_xxx_Label                     |
              N_Range_Constraint                       |
              N_Real_Range_Specification               |
              N_Record_Definition                      |
              N_SCIL_Dispatch_Table_Tag_Init           |
              N_SCIL_Dispatching_Call                  |
              N_SCIL_Membership_Test                   |
              N_Signed_Integer_Type_Definition         |
              N_Subunit                                |
              N_Task_Definition                        |
              N_Terminate_Alternative                  |
              N_Triggering_Alternative                 |
              N_Unconstrained_Array_Definition         |
              N_Unused_At_Start                        |
              N_Unused_At_End                          |
              N_Variant                                =>
            raise Program_Error;
      end case;

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
        and then not In_SPARK (Etype (N))
      then
         Mark_Violation (N, From => Etype (N));
      end if;
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
               when N_Subtype_Declaration   |
                    N_Full_Type_Declaration =>
                  null;

               when N_Object_Declaration =>
                  if Constant_Present (N) then
                     null;
                  else
                     return False;
                  end if;

               when N_Null_Statement
                  | N_Freeze_Entity =>
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

      if Present (L) then
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
      end if;

      Inside_Actions := Save_Inside_Actions;
   end Mark_Actions;

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
           Attribute_Identity          |
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
           Attribute_Width
         =>
            null;

         --  These attributes are supported, but generate a warning in
         --  "pedantic" mode, owing to their implemention-defined status.
         --  These are the attributes marked "Warn" in SPARK RM 15.2.
         when Attribute_Address     |
           Attribute_Alignment      |
           Attribute_Bit_Order      |
           Attribute_Component_Size |
           Attribute_First_Bit      |
           Attribute_Last_Bit       |
           Attribute_Position       |
           Attribute_Size
         =>
            if Emit_Messages
              and then SPARK_Pragma_Is (Opt.On)
              and then Gnat2Why_Args.Pedantic
            then
               Error_Msg_Name_1 := Aname;
               Error_Msg_N
                 ("?attribute % has an implementation-defined value", N);
            end if;

         when Attribute_Valid =>
            if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
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
      if Present (Exprs) then
         Mark_List (Exprs);
      end if;
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
               Violation_Detected := True;
               if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                  Error_Msg_N ("operation between different fixed-point types"
                               & " is not yet supported", N);
               end if;

            elsif (Is_Fixed_Point_Type (L_Type)
                     and then
                   Is_Floating_Point_Type (R_Type))
                     or else
                  (Is_Fixed_Point_Type (R_Type)
                     and then
                   Is_Floating_Point_Type (L_Type))
            then
               Violation_Detected := True;
               if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                  Error_Msg_N ("operation between fixed-point type and"
                               & " universal real is not yet supported", N);
               end if;

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
                  Violation_Detected := True;
                  if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                     Error_Msg_N ("operation on fixed-point type"
                                  & " with different result type"
                                  & " is not fully supported", N);
                  end if;
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
               if Emit_Messages
                 and then SPARK_Pragma_Is (Opt.On)
                 and then Nkind (Left_Opnd (N)) in N_Op_Add | N_Op_Subtract
                 and then Paren_Count (Left_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Left_Opnd (N));
               end if;

               if Emit_Messages
                 and then SPARK_Pragma_Is (Opt.On)
                 and then Nkind (Right_Opnd (N)) in N_Op_Add | N_Op_Subtract
                 and then Paren_Count (Right_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Right_Opnd (N));
               end if;

            when N_Op_Multiply | N_Op_Divide | N_Op_Mod | N_Op_Rem =>
               if Emit_Messages
                 and then SPARK_Pragma_Is (Opt.On)
                 and then Nkind (Left_Opnd (N)) in N_Multiplying_Operator
                 and then Paren_Count (Left_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Left_Opnd (N));
               end if;

               if Emit_Messages
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
      Nam     : constant Node_Id := Name (N);
      E       : constant Entity_Id := (if Nkind (Nam) in N_Has_Entity
                                       then Entity (Nam)
                                       else Empty);
      Actuals : constant List_Id := Parameter_Associations (N);

   begin
      if Present (Actuals) then
         Mark_List (Actuals);
      end if;

      --  If this is an indirect call then the call is not in SPARK

      if not Is_Entity_Name (Nam)
        or else No (E)
      then
         if Nkind (Nam) = N_Explicit_Dereference then
            if Nkind (N) = N_Procedure_Call_Statement then
               Mark_Violation ("call through access to procedure", N);
            else
               pragma Assert (Nkind (N) = N_Function_Call);
               Mark_Violation ("call through access to function", N);
            end if;

         else
            --  Entry calls are now in SPARK
            --  ??? what is "indirect call"? should we check more?
            if not (Nkind (N) in N_Entry_Call_Statement |
                                 N_Function_Call)
            then
               --  Are there cases where we reach here??? For the moment,
               --  issue a generic error message about "indirect calls".

               Mark_Violation ("indirect call", N);
            end if;
         end if;

      --  If the subprogram called is not in SPARK then the call is not in
      --  SPARK.

      elsif not In_SPARK (E) then
         Mark_Violation (N, From => E);

      elsif Present (Controlling_Argument (N))
        and then Is_Invisible_Dispatching_Operation (E)
      then
         Mark_Violation
           ("dispatching call on primitive of untagged private", N);

      --  There should not be calls to predicate functions and invariant
      --  procedures.

      elsif Subprogram_Is_Ignored_For_Proof (E) then
         raise Program_Error;

      else
         declare
            Unit : constant Unit_Number_Type := Get_Source_Unit (Sloc (E));
            File : constant File_Name_Type   := Unit_File_Name (Unit);
         begin
            --  Issue a warning for calls to subprograms with no
            --  Global contract, either manually-written or
            --  computed. This is the case for standard and external
            --  library subprograms for which no Global contract is
            --  supplied. Note that subprograms for which an external
            --  axiomatization is provided are exempted, as they
            --  should not have any effect on global items. Exempt
            --  also pure subprograms which have no global effects.

            if Emit_Messages
              and then SPARK_Pragma_Is (Opt.On)
              and then ((Is_Imported (E)
                           and then Convention (E) not in Convention_Ada)
                          or else Is_Internal_File_Name (File))
              and then No (Get_Pragma (E, Pragma_Global))
              and then not Entity_In_Ext_Axioms (E)
              and then not Is_Pure (E)
            then
               Error_Msg_NE
                 ("?no Global contract available for &", N, E);
               Error_Msg_NE
                 ("\\assuming & has no effect on global items", N, E);
            end if;
         end;
      end if;
   end Mark_Call;

   ---------------------------
   -- Mark_Compilation_Unit --
   ---------------------------

   procedure Mark_Compilation_Unit (N : Node_Id) is
      CU        : constant Node_Id := Parent (N);
      Context_N : Node_Id;

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

      --  Mark delayed type aspects.

      --  If no SPARK_Mode is set for the type, we only mark delayed aspects
      --  for types which have been found to be in SPARK. In this case, every
      --  violation is considered an error as we can't easily backtrack the
      --  type to be out of SPARK.

      for Cur in Delayed_Type_Aspects.Iterate loop
         Current_SPARK_Pragma := Node_Maps.Element (Cur);

         --  Consider delayed aspects only if type was in a scope marked
         --  SPARK_Mode(On)...

         if Nkind (Current_SPARK_Pragma) = N_Pragma

           --  or if the type entity has been found to be in SPARK. In this
           --  second case (scope not marked SPARK_Mode(On)), the type entity
           --  was stored as value in the Delayed_Type_Aspects map.

           or else Entity_In_SPARK (Current_SPARK_Pragma)
         then
            declare
               --  Two type aspects are delayed: Predicate (and
               --  variants Static_Predicate or Dynamic_Predicate) and
               --  Default_Initial_Condition. In both cases, the subprogram
               --  generated by the frontend is stored as key in the
               --  Delayed_Type_Aspects map.

               Subp   : constant Entity_Id := Node_Maps.Key (Cur);
               Params : constant List_Id :=
                 Parameter_Specifications (Subprogram_Specification (Subp));
               Expr   : constant Node_Id :=
                 (if Is_Predicate_Function (Subp) then
                    Get_Expr_From_Return_Only_Func (Subp)
                  else
                    Get_Expr_From_Check_Only_Proc (Subp));
            begin
               pragma Assert (Present (First (Params)));
               Mark_Entity (Defining_Identifier (First (Params)));
               if Present (Expr) then
                  Mark (Expr);
               end if;
            end;
         end if;
      end loop;
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

   -----------------
   -- Mark_Entity --
   -----------------

   procedure Mark_Entity (E : Entity_Id) is

      --  Subprograms for marking specific entities. These are defined locally
      --  so that they cannot be called from other marking subprograms, which
      --  should call Mark_Entity instead.

      procedure Mark_Parameter_Entity (E : Entity_Id);
      --  E is a subprogram or a loop parameter

      procedure Mark_Number_Entity     (E : Entity_Id);
      procedure Mark_Object_Entity     (E : Entity_Id);
      procedure Mark_Package_Entity    (E : Entity_Id);
      procedure Mark_Subprogram_Entity (E : Entity_Id);
      procedure Mark_Type_Entity       (E : Entity_Id);

      ------------------------
      -- Mark_Number_Entity --
      ------------------------

      procedure Mark_Number_Entity (E : Entity_Id) is
         N    : constant Node_Id   := Parent (E);
         Expr : constant Node_Id   := Expression (N);
         T    : constant Entity_Id := Etype (E);
      begin
         if not In_SPARK (T) then
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
         N    : constant Node_Id   := Parent (E);
         Def  : constant Node_Id   := Object_Definition (N);
         Expr : constant Node_Id   := Expression (N);
         T    : constant Entity_Id := Etype (E);
         Sub  : constant Entity_Id := Actual_Subtype (E);

      begin
         --  A constant object (other than a formal parameter of mode in) shall
         --  not be effectively volatile (SPARK RM 7.1.3(4)). This legality
         --  rule is checked by the frontend for code with SPARK_Mode On, but
         --  needs to be checked here for code with SPARK_Mode Auto.

         if Ekind (E) = E_Constant and then Is_Effectively_Volatile (T) then
            Mark_Violation ("volatile constant", Def);
         end if;

         --  The object is in SPARK if-and-only-if its type is in SPARK and
         --  its initialization expression, if any, is in SPARK.

         if not In_SPARK (T) then
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

         procedure Mark_Generic_Parameters_External_Axioms (Assoc : List_Id);
         --  Mark actual parameters of a package with external axioms

         ---------------------------------------------
         -- Declare_In_Package_With_External_Axioms --
         ---------------------------------------------

         procedure Declare_In_Package_With_External_Axioms (Decls : List_Id) is
            Decl : Node_Id;
            Id   : Entity_Id;
         begin
            Decl := First (Decls);

            --  Declare entities for type and subprogram formal parameters

            while Present (Decl) and then not Comes_From_Source (Decl) loop
               if Nkind (Decl) in
                 N_Subtype_Declaration | N_Subprogram_Declaration
               then
                  Id := Defining_Entity (Decl);

                  if Is_Subprogram (Id)
                    and then Is_Generic_Actual_Subprogram (Id)
                  then

                     --  Translate specification and body of subprogram
                     --  formals to check for runtime errors.

                     Mark_Subprogram_Declaration (Decl);
                     Mark_Subprogram_Body (Subprogram_Body (Id));

                     --  Add the subprogram entity and its parameters to the
                     --  list of entities to be translated.

                     if Present (Parameter_Specifications
                                 (Subprogram_Specification (Id)))
                     then
                        declare
                           Param_Spec : Node_Id :=
                             First (Parameter_Specifications
                                    (Subprogram_Specification (Id)));
                        begin
                           while Present (Param_Spec) loop
                              Entity_List.Append
                                (Defining_Identifier (Param_Spec));
                              Next (Param_Spec);
                           end loop;
                        end;
                     end if;

                     Entity_List.Append (Id);
                  elsif Is_Type (Id) then
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
               elsif Nkind (Decl) in N_Full_Type_Declaration         |
                                     N_Private_Type_Declaration      |
                                     N_Private_Extension_Declaration |
                                     N_Subtype_Declaration           |
                                     N_Subprogram_Declaration        |
                                     N_Object_Declaration
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

         ---------------------------------------------
         -- Mark_Generic_Parameters_External_Axioms --
         ---------------------------------------------

         procedure Mark_Generic_Parameters_External_Axioms (Assoc : List_Id) is
            Cur_Assoc : Node_Id := First (Assoc);
         begin
            while Present (Cur_Assoc) loop
               declare
                  Actual : constant Node_Id :=
                    Explicit_Generic_Actual_Parameter (Cur_Assoc);
               begin
                  --  For entities passed as actual, mark the entity directly
                  --  instead of the expression.

                  if Nkind (Actual) in N_Identifier | N_Expanded_Name then
                     declare
                        EActual : constant Entity_Id :=
                          (if Ekind (Entity (Actual)) = E_Function then
                              Get_Renamed_Entity (Entity (Actual))
                           else Entity (Actual));
                     begin
                        if Ekind (EActual) /= E_Operator then

                           --  Mark the entity of the actual

                           Mark_Entity (EActual);
                        end if;
                     end;

                  --  For anonymous classwide types T'Class passed as actual,
                  --  mark the corresponding type entity.

                  elsif Nkind (Actual) in N_Attribute_Reference
                    and then Get_Attribute_Id (Attribute_Name (Actual)) =
                      Attribute_Class
                  then
                     Mark_Entity (Etype (Actual));

                  --  For constant parameters, the actual may be an expression
                  --  instead of a name. In that case, mark the expression of
                  --  the actual.

                  else
                     Mark (Actual);
                  end if;
               end;

               Next (Cur_Assoc);
            end loop;
         end Mark_Generic_Parameters_External_Axioms;

         Vis_Decls : constant List_Id :=
           Visible_Declarations (Package_Specification (E));

      --  Start of processing for Mark_Package_Entity

      begin
         --  Do not analyze specs for instantiations of the formal containers.
         --  Only mark types in SPARK or not, and mark all subprograms in
         --  SPARK, but none should be scheduled for translation into Why3.

         if Entity_In_Ext_Axioms (E) then

            --  Packages with external axioms should have SPARK_Mode On.

            pragma Assert
              (Present (SPARK_Pragma (E))
               and then Get_SPARK_Mode_From_Pragma (SPARK_Pragma (E)) = On);

            --  For other verifications, use the SPARK pragma of the package

            declare
               Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;
            begin
               Current_SPARK_Pragma := SPARK_Pragma (E);

               --  For packages with external axiomatization, check that the
               --  private part (if any) has SPARK_Mode => Off.

               if Present (Private_Declarations (Package_Specification (E)))
                 and then Present (SPARK_Aux_Pragma (E))
                 and then
                   Get_SPARK_Mode_From_Pragma (SPARK_Aux_Pragma (E)) /= Off
               then
                  Mark_Violation
                    ("private part of package with External_Axiomatization",
                     E);
               end if;

               --  If E is a package instance, mark its actual parameters

               declare
                  G_Parent : constant Node_Id :=
                    Generic_Parent (Package_Specification (E));
               begin
                  if Present (G_Parent) then
                     Mark_Generic_Parameters_External_Axioms
                       (Generic_Associations
                          (Get_Package_Instantiation_Node (E)));
                  end if;
               end;

               --  Mark types and subprograms from packages with external
               --  axioms as in SPARK or not.

               Declare_In_Package_With_External_Axioms (Vis_Decls);

               if not Violation_Detected then

                  --  Explicitly add the package declaration to the entities to
                  --  translate into Why3.

                  Entity_List.Append (E);
               end if;

               Current_SPARK_Pragma := Save_SPARK_Pragma;
            end;
         end if;
      end Mark_Package_Entity;

      ---------------------------
      -- Mark_Parameter_Entity --
      ---------------------------

      procedure Mark_Parameter_Entity (E : Entity_Id) is
         T : constant Entity_Id := Etype (E);
      begin
         if not In_SPARK (T) then
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
                     Mark_Violation ("function with IN OUT parameter", Id);

                  when others =>
                     null;
               end case;

               Next (Param);
            end loop;
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
               Elmt    : Elmt_Id;
               Item    : Node_Id;
               Item_Id : Entity_Id;
            begin
               if No (Subp_Items) then
                  return;
               end if;

               Elmt := First_Elmt (Subp_Items);
               while Present (Elmt) loop
                  Item := Node (Elmt);

                  if Nkind (Item) = N_Defining_Identifier then
                     Item_Id := Item;
                  else
                     Item_Id := Entity_Of (Item);
                  end if;

                  if Present (Item_Id) then
                     if From_Limited_With (Item_Id) then
                        Item_Id := Non_Limited_View (Item_Id);
                     end if;

                     Mark_Entity (Item_Id);
                  end if;

                  Next_Elmt (Elmt);
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
            if Ekind (Id) = E_Function then
               Mark_Function_Specification (N);
            end if;

            if Present (Formals) then
               Param_Spec := First (Formals);
               while Present (Param_Spec) loop
                  Formal := Defining_Identifier (Param_Spec);
                  if not In_SPARK (Etype (Formal)) then
                     Mark_Violation (E, From => Etype (Formal));
                  end if;
                  Mark_Entity (Formal);
                  Next (Param_Spec);
               end loop;
            end if;

            --  If the result type of a subprogram is not in SPARK, then the
            --  subprogram is not in SPARK.

            if Nkind (N) = N_Function_Specification
              and then not In_SPARK (Etype (Id))
            then
               Mark_Violation (Result_Definition (N), From => Etype (Id));
            end if;

            --  Mark global items that appear in Global and Depends contracts,
            --  so that they get translated to Why3, even if this is the only
            --  occurrence of these variables/states.

            Collect_Subprogram_Inputs_Outputs
              (Id, False, Subp_Inputs, Subp_Outputs, Global_Seen);
            Mark_Global_Items (Subp_Inputs);
            Mark_Global_Items (Subp_Outputs);
         end Mark_Subprogram_Specification;

         Prag : Node_Id;
         Expr : Node_Id;

      --  Start of processing for Mark_Subprogram_Entity

      begin
         Mark_Subprogram_Specification (if Ekind (E) = E_Entry
                                        then Parent (E)
                                        else Subprogram_Specification (E));

         Prag := (if Present (Contract (E))
                  then Pre_Post_Conditions (Contract (E))
                  else Empty);

         while Present (Prag) loop
            Expr :=
              Get_Pragma_Arg (First (Pragma_Argument_Associations (Prag)));
            Mark (Expr);
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
                  Mark (Conseq);

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
                  Violation_Detected := True;
                  if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                     Error_Msg_N
                       ("subprogram inherited from root and interface"
                        & " is not yet supported", E);
                  end if;

               --  Do not support yet a subprogram inherited from multiple
               --  interfaces.

               else
                  Violation_Detected := True;
                  if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                     Error_Msg_N
                       ("subprogram inherited from multiple interfaces"
                        & " is not yet supported", E);
                  end if;
               end if;
            end;
         end if;
      end Mark_Subprogram_Entity;

      ----------------------
      -- Mark_Type_Entity --
      ----------------------

      procedure Mark_Type_Entity (E : Entity_Id) is

         function Is_Private_Entity_Mode_Off (E : Entity_Id) return Boolean;
         --  return True if E is declared in a private part with
         --  SPARK_Mode => Off;

         function Is_Synchronous_Barrier (E : Entity_Id) return Boolean;
         --  Return True if E is Ada.Synchronous_Barriers.Synchronous_Barrier
         --
         --  Synchronous barriers are allowed by the Ravenscar profile, but we
         --  do not want them in SPARK.

         function Is_Private_Entity_Mode_Off (E : Entity_Id) return Boolean
         is
            Decl : constant Node_Id :=
              (if No (Parent (Parent (E)))
               and then Is_Itype (E) then
                    Associated_Node_For_Itype (E)
               else Parent (E));
            Pack_Decl : constant Node_Id := Parent (Parent (Decl));
         begin
            pragma Assert
              (Nkind (Pack_Decl) = N_Package_Declaration);

            return
              Present (SPARK_Aux_Pragma (Defining_Entity (Pack_Decl)))
              and then Get_SPARK_Mode_From_Pragma
                (SPARK_Aux_Pragma (Defining_Entity (Pack_Decl))) = Off;
         end Is_Private_Entity_Mode_Off;

         ----------------------------
         -- Is_Synchronous_Barrier --
         ----------------------------

         function Is_Synchronous_Barrier (E : Entity_Id) return Boolean is
            S_Ptr : Entity_Id := E;
            --  Scope pointer

            Name_Synchronous_Barrier : constant Name_Id :=
              Name_Find_Str ("synchronous_barrier");
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
            Mark_Entity (Etype (E));
            if not Entity_In_SPARK (Retysp (Etype (E))) then
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
            if Nkind (Parent (E)) = N_Subtype_Declaration
              and then Defining_Entity (Parent (E)) = E
            then
               declare
                  Subty : constant Node_Id :=
                    Subtype_Indication (Parent (E));
                  Ty : Node_Id := Empty;
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

                        Violation_Detected := True;
                        if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                           Error_Msg_N ("constrained class-wide subtypes "
                                        & "are not yet supported", E);
                        end if;
                     when others =>
                        raise Program_Error;
                  end case;

                  if Present (Ty) then
                     Set_Specific_Tagged (E, Unique_Entity (Ty));
                  end if;
               end;
            end if;

         elsif Is_Private_Type (E) then

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

            --  The same is true for a subtype or a derived type of such a
            --  type or of types whose fullview is not in SPARK.

            elsif not Is_Nouveau_Type (E)
              and then Full_View_Not_In_SPARK (Etype (E))
            then
               Full_Views_Not_In_SPARK.Insert (E, Etype (E));
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
                  Mark_Entity (Utype);
                  if not Entity_In_SPARK (Utype) then
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

            --  If the type has a Default_Initial_Condition aspect, store the
            --  corresponding procedure in the Delayed_Type_Aspects map.

            if (Has_Default_Init_Cond (E)
                  or else Has_Inherited_Default_Init_Cond (E))
              and then Present (Default_Init_Cond_Procedure (E))
            then
               declare
                  Delayed_Mapping : constant Node_Id :=
                    (if Present (Current_SPARK_Pragma)
                     then Current_SPARK_Pragma
                     else E);
               begin
                  Delayed_Type_Aspects.Include
                    (Default_Init_Cond_Procedure (E), Delayed_Mapping);
               end;
            end if;
         end if;

         --  Now mark the type itself

         --  Components of a record type should be in SPARK for the record type
         --  to be in SPARK. For a private type, we're only interested here in
         --  its publicly visible components. The same applies to concurrent
         --  types.

         if Ekind (E) in Record_Kind | Concurrent_Kind then
            declare
               --  ??? Einfo.First_Component_Or_Discriminant does not work for
               --  concurrent types; see O508-008.

               function First_Component_Or_Discriminant
                 (Id : Entity_Id) return Entity_Id;

               function Mentions_Type_Name (N : Node_Id) return Boolean;
               --  Returns True iff node [N] mentions the type name [E]

               -------------------------------------
               -- First_Component_Or_Discriminant --
               -------------------------------------

               function First_Component_Or_Discriminant
                 (Id : Entity_Id) return Entity_Id is
                  Comp_Id : Entity_Id;
               begin
                  Comp_Id := First_Entity (Id);
                  while Present (Comp_Id) loop
                     exit when Ekind_In (Comp_Id, E_Component, E_Discriminant);
                     Comp_Id := Next_Entity (Comp_Id);
                  end loop;

                  return Comp_Id;
               end First_Component_Or_Discriminant;

               ------------------------
               -- Mentions_Type_Name --
               ------------------------

               function Mentions_Type_Name (N : Node_Id) return Boolean is
                  Found : Boolean := False;

                  function Find_Type (N : Node_Id) return Traverse_Result;
                  --  Sets [Found] to True if type name for [E] is found

                  ---------------
                  -- Find_Type --
                  ---------------

                  function Find_Type (N : Node_Id) return Traverse_Result is
                  begin
                     case Nkind (N) is
                        when N_Identifier | N_Expanded_Name =>
                           if Present (Entity (N))
                                and then
                              Unique_Entity (Entity (N)) = Unique_Entity (E)
                           then
                              Found := True;
                           end if;
                        when others => null;
                     end case;
                     return OK;
                  end Find_Type;

                  procedure Maybe_Find_Type is new Traverse_Proc (Find_Type);
               begin
                  Maybe_Find_Type (N);
                  return Found;
               end Mentions_Type_Name;

               Comp : Node_Id := First_Component_Or_Discriminant (E);

            begin
               while Present (Comp) loop
                  if Component_Is_Visible_In_SPARK (Comp) then
                     Mark_Entity (Etype (Comp));

                     --  Mark default value of component or discriminant

                     if Present (Expression (Parent (Comp))) then

                        --  The default expression of a component declaration
                        --  shall not contain a name denoting the current
                        --  instance of the enclosing type. (SPARK RM 3.8(2))

                        if Mentions_Type_Name (Expression (Parent (Comp))) then
                           Violation_Detected := True;
                           if Emit_Messages and then SPARK_Pragma_Is (Opt.On)
                           then
                              Error_Msg_Node_1 := E;
                              Error_Msg_N
                                ("default expression cannot mention }", E);
                           end if;
                        end if;

                        Mark (Expression (Parent (Comp)));
                     end if;
                  end if;

                  Next_Component_Or_Discriminant (Comp);
               end loop;
            end;
         end if;

         if Has_Invariants (E) then

            --  Do not issue a warning on both the partial view and the full
            --  view, in the case where the invariant is declared on the
            --  partial view.

            if Present (Full_View (E))
              and then Has_Invariants (Full_View (E))
            then
               null;

            --  Do not issue a warning on an Itype derived from a user type, as
            --  a warning is already generated for the user type.

            elsif Is_Itype (E) then
               null;

            elsif Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
               Error_Msg_N ("?type invariant ignored (not yet supported)", E);
            end if;
         end if;

         --  If the type has a predicate, store the corresponding
         --  frontend-generated checking function in the
         --  Delayed_Type_Aspects map.

         if Has_Predicates (E) then
            declare
               Delayed_Mapping : constant Node_Id :=
                 (if Present (Current_SPARK_Pragma)
                  then Current_SPARK_Pragma
                  else E);
            begin
               pragma Assert (Present (Predicate_Function (E)));
               Delayed_Type_Aspects.Include
                 (Predicate_Function (E), Delayed_Mapping);
            end;
         end if;

         --  Check default initialization
         declare
            DI : constant Default_Initialization_Kind :=
              SPARK_Util.Default_Initialization (E);
         begin
            --  Protected types need full default initialization
            if Ekind (E) in Protected_Kind then
               if DI not in
                 Full_Default_Initialization | No_Possible_Initialization
               then
                  Mark_Violation ("protected type "
                                  & "with no default initialization",
                                  E,
                                  SRM_Reference => "SPARK RM 9.4");
               end if;
            else
               --  Other types are not allowed to have partial default
               --  initialization.
               if DI = Mixed_Initialization then
                  Mark_Violation ("type with partial default initialization",
                                  E,
                                  SRM_Reference => "SPARK RM 3.8(1)");
               end if;
            end if;
         end;

         if Is_Array_Type (E) then
            declare
               Component_Typ : constant Node_Id := Component_Type (E);
               Index         : Node_Id := First_Index (E);

            begin
               if Positive (Number_Dimensions (E)) > Max_Array_Dimensions then
                  Violation_Detected := True;
                  if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                     Error_Msg_Node_1 := E;
                     Error_Msg_N ("} of dimension greater than" &
                                    Max_Array_Dimensions'Img &
                                    " is not yet supported", E);
                  end if;
               end if;

               --  Check that all index types are in SPARK

               while Present (Index) loop
                  if not In_SPARK (Etype (Index)) then
                     Mark_Violation (E, From => Etype (Index));
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
                 with Pre => UI_Gt (Num, Uint_0)
                 and then UI_Gt (Factor, Uint_0);
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
                  Violation_Detected := True;
                  if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                     Error_Msg_N
                       ("fixed-point type whose small is not a negative power "
                        & "of 2 or 10 is not yet supported", E);
                  end if;
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

            if Is_Modular_Integer_Type (E)
              and then Modulus (E) > UI_Expon (2, 64)
            then
               Violation_Detected := True;
               if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                  Error_Msg_N ("modulus greater than 2 ** 64 "
                               & "is not yet supported", E);
               end if;
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
               if not In_SPARK (Specific_Type) then
                  Mark_Violation (E, From => Specific_Type);

               --  Constrained class-wide types are not supported yet as it is
               --  unclear wether we should do discriminant checks for them
               --  or not.

               elsif Has_Discriminants (Retysp (Specific_Type))
                 and then Is_Constrained (Retysp (Specific_Type))
               then
                  Violation_Detected := True;
                  if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
                     Error_Msg_N ("Class attribute of a constrained type "
                                  & "is not yet supported", E);
                  end if;
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

         elsif Is_Record_Type (E) then

            if Ekind (E) = E_Record_Subtype
              and then not In_SPARK (Base_Type (E))
            then
               Mark_Violation (E, From => Base_Type (E));
            end if;

            if not Is_Interface (E) then
               declare
                  Field : Node_Id := First_Component_Or_Discriminant (E);
                  Typ   : Entity_Id;

               begin
                  while Present (Field) loop
                     Typ := Etype (Field);

                     if not Is_Tag (Field)
                       and then Is_Object (Field)
                       and then not In_SPARK (Typ)
                     then
                        Mark_Violation (Typ, From => Typ);
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

               case Ekind (E) is
                  when E_Protected_Subtype | E_Task_Subtype =>
                     if not In_SPARK (Base_Type (E))
                     then
                        Mark_Violation (E, From => Base_Type (E));
                     end if;
                     if Ekind (E) = E_Task_Subtype
                       and then SPARK_Pragma_Is (Opt.On)
                     then
                        Specs_In_SPARK.Include (E);
                     end if;

                  when E_Protected_Type | E_Task_Type =>
                     declare
                        Type_Decl : constant Node_Id := Parent (E);
                        Type_Def  : constant Node_Id :=
                          (if Ekind (E) = E_Protected_Type
                           then Protected_Definition (Type_Decl)
                           else Task_Definition (Type_Decl));
                     begin
                        Mark_List (Interface_List (Type_Decl));

                        if Present (Type_Def) then
                           --  We do not mark the visible declarations here, we
                           --  mark them independently of the type entity when
                           --  processing the type declaration

                           --  ??? components of protected types were already
                           --  marked when dealing with discriminants
                           Mark_Stmt_Or_Decl_List
                             (Private_Declarations (Type_Def));
                        end if;
                        if Ekind (E) = E_Task_Type
                          and then SPARK_Pragma_Is (Opt.On)
                        then
                           Specs_In_SPARK.Include (E);
                        end if;

                     end;

                  when others =>
                     raise Program_Error;

               end case;
            else
               Mark_Violation_In_Tasking (E);
            end if;
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

      --  Ignore some functions generated by the frontend for aspects
      --  Type_Invariant and Default_Initial_Condition. This does not include
      --  the functions generated for Predicate aspects, as these functions
      --  are translated to check absence of RTE in the predicate in the most
      --  general context.

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

      --  Types may be marked out of order, because completions of private
      --  types need to be marked at the point of their partial view
      --  declaration, to avoid out-of-order declarations in Why.
      --  Retrieve the appropriate SPARK_Mode pragma before marking.

      if Is_Type (E) then
         declare
            Decl : constant Node_Id :=
              (if No (Parent (Parent (E)))
                 and then Is_Itype (E)
               then Associated_Node_For_Itype (E)
               else Parent (E));

         begin
            if Present (Parent (Decl))
              and then Nkind (Parent (Decl)) = N_Package_Specification
            then
               declare
                  Pack_Decl : constant Node_Id := Parent (Parent (Decl));
               begin

                  pragma Assert (Nkind (Pack_Decl) = N_Package_Declaration);

                  Current_SPARK_Pragma :=
                    (if In_Private_Declarations (Decl)
                     then SPARK_Aux_Pragma (Defining_Entity (Pack_Decl))
                     else SPARK_Pragma (Defining_Entity (Pack_Decl)));
               end;
            end if;
         end;
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
         when E_Loop_Parameter |
              Formal_Kind      => Mark_Parameter_Entity (E);

         --  Discriminants of task types are marked, but those of records and
         --  protected objects are not.

         when E_Discriminant   => Mark_Object_Entity (E);

         when Named_Kind       => Mark_Number_Entity (E);
         when E_Package        => Mark_Package_Entity (E);

         --  The identifier of a loop is used to generate the needed
         --  exception declarations in the translation phase.

         when E_Loop           => null;

         --  Mark_Entity is called on all abstract state variables

         when E_Abstract_State => null;

         when E_Entry          => Mark_Subprogram_Entity (E);

         when others           =>
            Ada.Text_IO.Put_Line ("[Mark_Entity] kind ="
                                  & Entity_Kind'Image (Ekind (E)));
            raise Program_Error;
      end case;

      --  If a violation was detected, remove E from the set of SPARK entities

      if Violation_Detected then
         Entities_In_SPARK.Delete (E);
      end if;

      --  Add entity to appropriate list. Entities from packages with external
      --  axioms are handled by a specific mechanism and thus should not be
      --  translated.

      if not Entity_In_Ext_Axioms (E) then
         Entity_List.Append (E);
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
      E : Entity_Id;
   begin
      if Is_Entity_Name (N) and then Present (Entity (N)) then
         E := Entity (N);

         case Ekind (E) is
            when Object_Kind =>
               if (Ekind_In (E, E_Variable, E_Constant)
                    or else Is_Formal (E))
                 and then not In_SPARK (Entity (N))
               then
                  Mark_Violation (N, From => Entity (N));
               end if;

            when Named_Kind =>
               if not In_SPARK (Entity (N)) then
                  Mark_Violation (N, From => Entity (N));
               end if;

            when Type_Kind =>
               if not In_SPARK (Entity (N)) then
                  Mark_Violation (N, From => Entity (N));
               end if;

            --  Subprogram name appears for example in Sub'Result

            when E_Void                  |
                 E_Enumeration_Literal   |
                 Subprogram_Kind         |
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

            --  Entry name appears for example in Sub'Caller

            when E_Entry =>
               null;

            when E_Entry_Family          |
                 E_Entry_Index_Parameter |
                 E_Protected_Object      |
                 E_Protected_Body        |
                 E_Task_Body             =>
               Mark_Violation ("tasking", N);
         end case;
      end if;
   end Mark_Identifier_Or_Expanded_Name;

   ------------------------
   -- Mark_If_Expression --
   ------------------------

   procedure Mark_If_Expression (N : Node_Id) is
      Condition : constant Node_Id := First (Expressions (N));
      Then_Expr : constant Node_Id := Next (Condition);
      Else_Expr : Node_Id;

   begin
      Mark_Actions (N, Then_Actions (N));
      Mark_Actions (N, Else_Actions (N));

      Else_Expr := Next (Then_Expr);

      Mark (Condition);
      Mark (Then_Expr);

      if Present (Else_Expr) then
         Mark (Else_Expr);
      end if;
   end Mark_If_Expression;

   -----------------------
   -- Mark_If_Statement --
   -----------------------

   procedure Mark_If_Statement (N : Node_Id) is
   begin
      Mark (Condition (N));

      Mark_Stmt_Or_Decl_List (Then_Statements (N));

      if Present (Elsif_Parts (N)) then
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
      end if;

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

   procedure Mark_Number_Declaration (N : Node_Id) is
      E : constant Entity_Id := Defining_Entity (N);
   begin
      Mark_Entity (E);
   end Mark_Number_Declaration;

   -----------------------------
   -- Mark_Object_Declaration --
   -----------------------------

   procedure Mark_Object_Declaration (N : Node_Id) is
      E : constant Entity_Id := Defining_Entity (N);

   begin
      --  Mark entity
      Mark_Entity (E);
   end Mark_Object_Declaration;

   -----------------------
   -- Mark_Package_Body --
   -----------------------

   procedure Mark_Package_Body (N : Node_Id) is
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;
      Id  : constant Entity_Id := Unique_Defining_Entity (N);
      HSS : constant Node_Id := Handled_Statement_Sequence (N);

   begin
      --  Do not analyze generic bodies

      if Ekind (Id) = E_Generic_Package then
         return;
      end if;

      Current_SPARK_Pragma := SPARK_Pragma (Defining_Entity (N));

      --  Do not analyze bodies for packages with external axioms. Only check
      --  that their SPARK_Mode is Off, and restore SPARK_Mode pragma before
      --  returning.

      if Entity_In_Ext_Axioms (Id) then
         if Present (SPARK_Pragma (Defining_Entity (N)))
           and then Get_SPARK_Mode_From_Pragma
             (SPARK_Pragma (Defining_Entity (N))) /= Off
         then
            Mark_Violation ("Body of package with External_Axiomatization", N);
         end if;

         Current_SPARK_Pragma := Save_SPARK_Pragma;
         return;
      end if;

      Mark_Stmt_Or_Decl_List (Declarations (N));

      Current_SPARK_Pragma := SPARK_Aux_Pragma (Defining_Entity (N));

      --  Only analyze package body statements in SPARK_Mode => On

      if SPARK_Pragma_Is (Opt.On) then

         --  Always mark the body in SPARK

         Bodies_In_SPARK.Include (Id);

         if Present (HSS) then
            Mark (HSS);
         end if;
      end if;

      --  Postprocessing: indicate in output file if package is in
      --  SPARK or not, for reporting, debug and verification.

      Generate_Output_In_Out_SPARK (Id);

      Current_SPARK_Pragma := Save_SPARK_Pragma;
   end Mark_Package_Body;

   ------------------------------
   -- Mark_Package_Declaration --
   ------------------------------

   procedure Mark_Package_Declaration (N : Node_Id) is
      Id                : constant Entity_Id := Defining_Entity (N);
      Spec              : constant Node_Id := Specification (N);
      Vis_Decls         : constant List_Id := Visible_Declarations (Spec);
      Priv_Decls        : constant List_Id := Private_Declarations (Spec);
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;

   begin

      if Entity_In_Ext_Axioms (Id) then

         --  Mark the package entity.

         Mark_Entity (Id);
         Specs_In_SPARK.Include (Id);

         return;
      end if;

      --  Mark package in SPARK if fully in SPARK_Mode => On (including the
      --  private part).

      Current_SPARK_Pragma := SPARK_Aux_Pragma (Id);

      Mark_Entity (Id);

      Current_SPARK_Pragma := SPARK_Pragma (Id);

      --  Mark abstract state entities

      declare
         States : constant Elist_Id := Abstract_States (Id);
         State  : Elmt_Id;
      begin
         if Present (States) then
            State := First_Elmt (States);
            while Present (State)
              and then not Is_Null_State (Node (State))
            loop
               Mark_Entity (Node (State));
               Next_Elmt (State);
            end loop;
         end if;
      end;

      if SPARK_Pragma_Is (Opt.On) then
         Specs_In_SPARK.Include (Id);
      end if;

      Mark_Stmt_Or_Decl_List (Vis_Decls);

      Current_SPARK_Pragma := SPARK_Aux_Pragma (Id);

      Mark_Stmt_Or_Decl_List (Priv_Decls);

      Current_SPARK_Pragma := Save_SPARK_Pragma;

      --  Postprocessing: indicate in output file if package is in SPARK or
      --  not, for reporting, debug and verification. Only do so if there
      --  is no corresponding package body, otherwise it is reported when
      --  marking the package body.

      if In_Main_Unit (Id) and then No (Package_Body (Id)) then
         Generate_Output_In_Out_SPARK (Id);
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

         if Present (Arg1) then
            Arg2 := Next (Arg1);
         end if;
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

         --  Do not issue a warning on invariant pragmas, as one is already
         --  issued on the corresponding type.

         when Pragma_Invariant
            | Pragma_Type_Invariant
            | Pragma_Type_Invariant_Class =>
            null;

         --  Emit warning on pragma Overflow_Mode being currently ignored, even
         --  in code not marked SPARK_Mode On, as otherwise no warning would
         --  be issued on configuration pragmas at the start of units whose
         --  top level declaration is marked later SPARK_Mode On. Do not emit
         --  a warning in code marked SPARK_Mode Off though.

         when Pragma_Overflow_Mode =>
            if Emit_Messages and then not SPARK_Pragma_Is (Opt.Off) then
               Error_Msg_F ("?pragma Overflow_Mode in code is ignored", N);
            end if;

         --  Need to mark the expression of a pragma Attach_Handler and
         --  Priority

         when Pragma_Attach_Handler |
              Pragma_Priority        =>
            Mark (Expression (Arg1));

         when Unknown_Pragma =>
            Error_Msg_Name_1 := Pname;
            Mark_Violation ("unknown pragma %", N);

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
              Pragma_Part_Of                      |
              Pragma_Postcondition                |
              Pragma_Precondition                 |
              Pragma_Refined_Depends              |
              Pragma_Refined_Global               |
              Pragma_Refined_Post                 |
              Pragma_Refined_State                |
              Pragma_SPARK_Mode                   |
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
              Pragma_No_Tagged_Streams            |
              Pragma_Pure_Function                |
              Pragma_Restriction_Warnings         |
              Pragma_Style_Checks                 |
              Pragma_Test_Case                    |
              Pragma_Unmodified                   |
              Pragma_Unreferenced                 |
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
           Pragma_Interrupt_Priority             |
           Pragma_Lock_Free                      |
           Pragma_Storage_Size                   =>

            if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
               Error_Msg_Name_1 := Pname;
               Error_Msg_N ("?pragma % ignored (not yet supported)", N);
            end if;
      end case;
   end Mark_Pragma;

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

         S_Short_Float         => True,
         S_Float               => True,
         S_Long_Float          => True,
         S_Long_Long_Float     => True,

         S_Character           => True,
         S_Wide_Character      => True,
         S_Wide_Wide_Character => True,

         S_String              => True,
         S_Wide_String         => True,
         S_Wide_Wide_String    => True,

         S_Duration            => True);

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

      if not Present (Cur) then
         return;
      end if;

      Preceding := Parent (L);

      while Present (Cur) loop

         --  We peek into the statement node to handle the case of the Annotate
         --  pragma separately here, to avoid passing the "Preceding" node
         --  around. All other cases are handled by Mark.

         if Is_Pragma_Annotate_GNATprove (Cur) then

            --  Handle all the following pragma Annotate, with the same
            --  "Preceding" node

            loop
               Mark_Pragma_Annotate (Cur, Preceding,
                                     Consider_Next => not Is_Parent);
               Next (Cur);
               exit when
                 not Present (Cur)
                 or else not Is_Pragma_Annotate_GNATprove (Cur);
            end loop;

         else
            Mark (Cur);

            --  if the current declaration does not come from source, we
            --  consider it to be part of the preceding one as far as pragma
            --  Annotate is concerned, so we don't update the "preceding" node
            --  in that case.

            if Comes_From_Source (Cur) then
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
      E   : constant Entity_Id := Unique_Defining_Entity (N);
      HSS : constant Node_Id   := Handled_Statement_Sequence (N);

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

      else
         --  For entries and task bodies reuse the value of SPARK_Pragma from
         --  the context; workaround for O506-007.
         Current_SPARK_Pragma := SPARK_Pragma (Defining_Entity (N));

         --  Only analyze subprogram body declarations in SPARK_Mode => On

         if SPARK_Pragma_Is (Opt.On) then

            --  Issue warning on unreferenced local subprograms, which are
            --  analyzed anyway, unless the subprogram is marked with pragma
            --  Unreferenced.

            if Is_Local_Subprogram_Always_Inlined (E)
              and then not Referenced (E)
              and then not Has_Unreferenced (E)
              and then Emit_Messages and then SPARK_Pragma_Is (Opt.On)
            then
               case Ekind (E) is
               when E_Function =>
                  Error_Msg_NE ("?analyzing unreferenced function &", N, E);

               when E_Procedure =>
                  Error_Msg_NE ("?analyzing unreferenced procedure &", N, E);

               when others =>
                  raise Program_Error;

               end case;
            end if;

            --  Always mark the body in SPARK

            Bodies_In_SPARK.Include (E);

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
               if Present (Formals) then
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
               end if;
            end;

            --  Mark Task discriminants

            if Nkind (N) = N_Task_Body
              and then Has_Discriminants (E)
            then
               declare
                  Disc : Entity_Id := First_Discriminant (E);
               begin
                  while Present (Disc) loop
                     Mark_Entity (Disc);
                     Next_Discriminant (Disc);
                  end loop;
               end;
            end if;

            --  Mark entry barrier

            if Nkind (E) = N_Entry_Body then
               --  Entry barriers in Ravenscar are always of N_Identifier kind
               Mark_Identifier_Or_Expanded_Name
                (Condition (Entry_Body_Formal_Part (N)));
            end if;

            --  For subprogram bodies (but not other subprogram-like nodes
            --  which are also processed by this procedure) mark Refined_Post
            --  aspect if present.
            if Nkind (N) = N_Subprogram_Body then
               declare
                  C : constant Entity_Id :=
                    Contract (Defining_Entity (Specification (N)));
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
            Mark (HSS);

            --  For the special case of an expression function, the frontend
            --  generates a distinct body if not already in source code. Use as
            --  entity for the body the distinct E_Subprogram_Body entity. This
            --  allows a separate definition of theories in Why3 for declaring
            --  the logic function and its axiom. This is necessary so that
            --  they are defined with the proper visibility over previously
            --  defined entities.

            if Ekind (E) = E_Function
              and then Present (Get_Expression_Function (E))
            then
               Entity_List.Append (Defining_Entity (N));
            end if;

            if not Violation_Detected then
               Bodies_Valid_SPARK.Insert (E);
            end if;
         end if;

         --  Postprocessing: indicate in output file if subprogram is in
         --  SPARK or not, for reporting, debug and verification.

         Generate_Output_In_Out_SPARK (E);

         Current_SPARK_Pragma := Save_SPARK_Pragma;
      end if;
   end Mark_Subprogram_Body;

   ---------------------------------
   -- Mark_Subprogram_Declaration --
   ---------------------------------

   procedure Mark_Subprogram_Declaration (N : Node_Id) is
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;
      E : constant Entity_Id := Defining_Entity (N);

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

      --  Mark entity

      else
         Current_SPARK_Pragma := SPARK_Pragma (E);

         if SPARK_Pragma_Is (Opt.On) then
            Specs_In_SPARK.Include (E);
         end if;

         Mark_Entity (E);

         Current_SPARK_Pragma := Save_SPARK_Pragma;
      end if;
   end Mark_Subprogram_Declaration;

   -----------------------------
   -- Mark_Subtype_Indication --
   -----------------------------

   procedure Mark_Subtype_Indication (N : Node_Id) is
      T    : constant Entity_Id := (if Nkind (N) = N_Subtype_Indication
                                    then Etype (Subtype_Mark (N))
                                    else Etype (N));
      Cstr : Node_Id;

   begin
      --  Check that the base type is in SPARK

      if not In_SPARK (T) then
         Mark_Violation (N, From => T);
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

            when N_Digits_Constraint |
                 N_Delta_Constraint  =>
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
      From : Entity_Id)
   is
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

   procedure Mark_Violation_In_Tasking (N : Node_Id)
   is
      Msg_Prefix : constant String := "tasking in SPARK requires ";
      Msg_Suffix : constant String := " (SPARK RM 9(2))";
   begin
      --  Flag the violation, so that the current entity is marked accordingly

      Violation_Detected := True;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then

         if not Ravenscar_Profile then
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

   procedure Mark_Violation_Of_SPARK_Mode (N : Node_Id)
   is
   begin
      Error_Msg_Sloc := Sloc (Current_SPARK_Pragma);

      if Nkind (Current_SPARK_Pragma) /= N_Pragma then
         pragma Assert (Nkind (Current_SPARK_Pragma) in N_Entity);
         Error_Msg_FE
           ("\\delayed type aspect on & is required to be in SPARK", N,
            Current_SPARK_Pragma);
      elsif From_Aspect_Specification (Current_SPARK_Pragma) then
         Error_Msg_F ("\\violation of aspect SPARK_Mode #", N);
      else
         Error_Msg_F ("\\violation of pragma SPARK_Mode #", N);
      end if;
   end Mark_Violation_Of_SPARK_Mode;

   ----------------------------------
   -- Most_Underlying_Type_In_SPARK --
   ----------------------------------

   procedure Mark_Most_Underlying_Type_In_SPARK (Id : Entity_Id; N : Node_Id)
   is
      Typ : constant Entity_Id := Retysp (Id);
   begin
      if not In_SPARK (Typ) then
         Mark_Violation (N, From => Typ);
      end if;
   end Mark_Most_Underlying_Type_In_SPARK;

   ---------------------
   -- SPARK_Pragma_Is --
   ---------------------

   function SPARK_Pragma_Is (Mode : Opt.SPARK_Mode_Type) return Boolean is
     (Present (Current_SPARK_Pragma)
        and then

     --  In the usual case where Current_SPARK_Pragma is a pragma node, get the
     --  current mode from the pragma.

     (if Nkind (Current_SPARK_Pragma) = N_Pragma then
        Get_SPARK_Mode_From_Pragma (Current_SPARK_Pragma) = Mode

     --  If Current_SPARK_Pragma is not a pragma node, then we are analyzing a
     --  deferred type aspect of a type marked to be in SPARK although no
     --  SPARK_Mode was set for the enclosing unit (discovery mode). In this
     --  case, we consider SPARK_Mode to be On as we can't mark the type out of
     --  SPARK easily.

      else Mode = Opt.On));

   --------------------------
   -- Register_Task_Object --
   --------------------------

   procedure Register_Task_Object
     (Type_Name : Entity_Name;
      Object    : Task_Object)
   is
      C : Task_Instances_Maps.Cursor;
      --  Cursor with a list of instances of a given task type

      Inserted : Boolean;
      --  Flag that indicates if a key was inserted or if it already existed in
      --  a map. It is required by the hashed-maps API, but not used here.

      procedure Append_Object (Key     : Entity_Name;
                               Element : in out Task_Lists.List);
      --  Append object to a list of task type instances

      -------------------
      -- Append_Object --
      -------------------

      procedure Append_Object (Key     : Entity_Name;
                               Element : in out Task_Lists.List)
      is
         pragma Unreferenced (Key);
      begin
         Element.Append (Object);
      end Append_Object;
   begin
      --  Find a list of instances of the task type; if it does not exist then
      --  initialize with an empty list.
      Task_Instances.Insert (Key      => Type_Name,
                             Position => C,
                             Inserted => Inserted);
      Task_Instances.Update_Element (C, Append_Object'Access);
   end Register_Task_Object;

end SPARK_Definition;
