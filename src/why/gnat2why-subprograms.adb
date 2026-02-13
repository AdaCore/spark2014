------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
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

with Ada.Containers;
use type Ada.Containers.Count_Type;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Strings.Unbounded;          use Ada.Strings.Unbounded;
with Atree;
with Errout_Wrapper;                 use Errout_Wrapper;
with Erroutc;                        use Erroutc;
with Exp_Util;
with Flow_Dependency_Maps;           use Flow_Dependency_Maps;
with Flow_Generated_Globals;         use Flow_Generated_Globals;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Refinement;                use Flow_Refinement;
with Flow_Utility;                   use Flow_Utility;
with GNAT.Source_Info;
with Gnat2Why.Data_Decomposition;    use Gnat2Why.Data_Decomposition;
with Gnat2Why.Error_Messages;        use Gnat2Why.Error_Messages;
with Gnat2Why.Expr;                  use Gnat2Why.Expr;
with Gnat2Why_Opts;                  use Gnat2Why_Opts;
with Gnat2Why.Tables;                use Gnat2Why.Tables;
with Gnat2Why.Unchecked_Conversion;  use Gnat2Why.Unchecked_Conversion;
with Gnat2Why_Args;
with Namet;                          use Namet;
with Nlists;                         use Nlists;
with Opt;
use type Opt.Warning_Mode_Type;
with Rtsfind;                        use Rtsfind;
with Sinput;                         use Sinput;
with Snames;                         use Snames;
with SPARK_Definition;               use SPARK_Definition;
with SPARK_Util;                     use SPARK_Util;
with SPARK_Util.Subprograms;         use SPARK_Util.Subprograms;
with SPARK_Util.Types;               use SPARK_Util.Types;
with Stand;                          use Stand;
with Uintp;                          use Uintp;
with VC_Kinds;                       use VC_Kinds;
with Why;                            use Why;
with Why.Atree.Accessors;            use Why.Atree.Accessors;
with Why.Atree.Builders;             use Why.Atree.Builders;
with Why.Atree.Modules;              use Why.Atree.Modules;
with Why.Atree.Mutators;             use Why.Atree.Mutators;
with Why.Gen.Arrays;                 use Why.Gen.Arrays;
with Why.Gen.Decl;                   use Why.Gen.Decl;
with Why.Gen.Init;                   use Why.Gen.Init;
with Why.Gen.Names;                  use Why.Gen.Names;
with Why.Gen.Pointers;               use Why.Gen.Pointers;
with Why.Gen.Progs;                  use Why.Gen.Progs;
with Why.Gen.Records;                use Why.Gen.Records;
with Why.Inter;                      use Why.Inter;
with Why.Types;                      use Why.Types;

package body Gnat2Why.Subprograms is

   Subprogram_Exceptions : Why_Node_Sets.Set;
   --  Set of exception declarations

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Add_Logic_Binders
     (E           : Entity_Id;
      Raw_Binders : Item_Array;
      More_Reads  : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return Item_Array;
   --  Return Why binders for the parameters and read effects of function E.
   --  The array is a singleton of unit type if E has no parameters and no
   --  effects. More_Reads is a set of globals that should be considered as
   --  read by the subprogram in addition to its actual inputs. It is used to
   --  handle calls with higher order specialization.

   function Assume_Initial_Condition_Of_Withed_Units
     (Main : Entity_Id; Params : Transformation_Params) return W_Prog_Id
   with
     Pre =>
       Ekind (Main) in Subprogram_Kind | E_Package | E_Package_Body
       and then Is_Compilation_Unit (Main);
   --  Assume the Initial_Condition of every unit withed by a compilation unit.
   --  @param Main entity for a compilation unit
   --  @param Params the transformation parameters
   --  @result a sequence of assumptions, one for each withed unit which has an
   --          Initial_Condition.

   function Check_Ceiling_Protocol
     (Params : Transformation_Params; E : Entity_Id) return W_Prog_Id
   with Pre => Ekind (E) in E_Task_Type | E_Entry | E_Function | E_Procedure;
   --  @param Params the transformation params
   --  @param E a task type, entry, main-like or protected subprogram entity
   --  @return an assertion or sequence of assertion that expresses that the
   --    ceiling protocol is respected in the call graph starting from this
   --    entity, i.e. that external calls to protected operations are made with
   --    a priority lower or equal to the priority of the object in question.

   function Check_Type_Invariants_For_Package
     (E : Entity_Id; Params : Transformation_Params) return W_Prog_Id
   with Pre => Ekind (E) = E_Package;
   --  @param E Entity of a package
   --  @param Params the transformation parameters
   --  @result program peforming an invariant check after E's elaboration

   procedure Clear_Exceptions;
   --  Initialization procedure to call before start of subprogram/package
   --  handling.

   function Compute_Args
     (E          : Entity_Id;
      Binders    : Binder_Array;
      More_Reads : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return W_Expr_Array;
   --  Given a function entity, and an array of program binders,
   --  compute a call of the logical Why function corresponding to E.
   --  In general, the resulting expression array has *more* arguments than the
   --  Ada entity, because of effects. Note that these effect variables are not
   --  bound here, they refer to the global variables.
   --  More_Reads is a set of globals that should be considered as read by
   --  the subprogram in addition to its actual inputs. It is used to handle
   --  calls with higher order specialization.

   function Compute_Attach_Handler_Check
     (Ty : Entity_Id; Params : Transformation_Params) return W_Prog_Id
   with Pre => Is_Protected_Type (Ty);
   --  @param Ty a protected type
   --  @return an assertion (if necessary) that checks if any of the
   --    Attach_Handler pragmas of the procedures of the type is reserved
   --    see also Ada RM C.3.1(10/3)

   function Compute_Binders
     (E          : Entity_Id;
      Domain     : EW_Domain;
      More_Reads : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return Item_Array;
   --  Return Why binders for the parameters of subprogram E.
   --  More_Reads is a set of globals that should be considered as read by
   --  the subprogram in addition to its actual inputs. It is used to handle
   --  calls with higher order specialization.
   --  If Domain is EW_Term also generates binders for E's read effects.
   --  The array is a singleton of unit type if the array is empty.

   function Compute_Cases_Entry_Checks
     (Aggr           : Node_Id;
      Guard_Map      : Ada_To_Why_Ident.Map;
      Check_Complete : Boolean) return W_Prog_Id;
   --  Returns the Why program for checking that the guards of a Contract_Cases
   --  or Exit_Cases pragma with parameter Aggr are disjoint, and, if
   --  Check_Complete is True, that they cover all cases prescribed by the
   --  precondition. The checks that evaluating guards do not raise run-time
   --  errors are done separately, based on the result of
   --  Compute_Cases_Guard_Map. Guard_Map stores a mapping from guard AST nodes
   --  to temporary Why names, so that the caller can compute the Why
   --  expression for these in the pre-state, and bind them appropriately.

   function Compute_Contract_Cases_Exit_Checks
     (Params    : Transformation_Params;
      E         : Entity_Id;
      Guard_Map : Ada_To_Why_Ident.Map) return W_Prog_Id;
   --  Returns in Result the Why program for checking that the consequences of
   --  enabled guards of the Contract_Cases pragmas attached to subprogram E
   --  (if any) do not raise a run-time error, and that they hold. Guard_Map
   --  stores a mapping from guard AST nodes to temporary Why names, so that
   --  the caller can compute the Why expression for these in the pre-state,
   --  and bind them appropriately.

   procedure Compute_Cases_Guard_Map
     (Aggr : Node_Id; Guard_Map : out Ada_To_Why_Ident.Map);
   --  Returns the map from contracts cases or exit cases nodes in Aggr,
   --  to Why identifiers for the value of these guards in the Why3
   --  program. If the cases contain an "others" case, associate an
   --  identifier to Aggr in Guard_Map for a Boolean value set to true when
   --  this case is enabled.

   function Compute_Cases_Others_Expr
     (Aggr : Node_Id; Guard_Map : Ada_To_Why_Ident.Map) return W_Term_Id;
   --  Return the Why3 expression that should be used to define the identifier
   --  for the others case in Aggr. If there is no "others" case, return
   --  Why_Empty.

   function Compute_Exit_Cases_Simple_Checks
     (E : Entity_Id; Name : Name_Id; Guard_Map : Ada_To_Why_Ident.Map)
      return W_Prog_Id;
   --  Returns in Result the Why program for checking the exit kind of
   --  enabled guard of the Exit_Cases pragma attached to subprogram E (if
   --  any) on exit kind Name. Guard_Map stores a mapping from guard AST nodes
   --  to temporary Why names, so that the caller can compute the Why
   --  expression for these in the pre-state, and bind them appropriately. This
   --  only works for "simple" exit kinds like Normal_Return and Program_Exit,
   --  not for Raised_Exception which might be associated to a value.

   function Compute_Exit_Cases_Exceptional_Exit_Checks
     (E         : Entity_Id;
      Guard_Map : Ada_To_Why_Ident.Map;
      Exc_Id    : W_Identifier_Id) return W_Prog_Id;
   --  Returns in Result the Why program for checking the exit kind of
   --  enabled guard of the Exit_Cases pragma attached to subprogram E (if
   --  any) on exceptional exit. Guard_Map stores a mapping from guard AST
   --  nodes to temporary Why names, so that the caller can compute the Why
   --  expression for these in the pre-state, and bind them appropriately.

   function Compute_Exit_Cases_Simple_Post
     (Params : Transformation_Params; E : Entity_Id; Name : Name_Id)
      return W_Pred_Id;
   --  Returns the postcondition for the exit kind Name corresponding to the
   --  Exit_Cases pragma for subprogram E (if any). This only works for
   --  "simple" exit kinds like Normal_Return and Program_Exit, not for
   --  Raised_Exception which might be associated to a value.

   function Compute_Exit_Cases_Exceptional_Post
     (Params : Transformation_Params; E : Entity_Id; Exc_Id : W_Identifier_Id)
      return W_Pred_Id;
   --  Returns the exceptional postcondition corresponding to the Exit_Cases
   --  pragma for subprogram E (if any), to be used in the raises effect of the
   --  program function.

   function Compute_Contract_Cases_Postcondition
     (Params : Transformation_Params; E : Callable_Kind_Id) return W_Pred_Id;
   --  Returns the postcondition corresponding to the Contract_Cases pragma for
   --  subprogram E (if any), to be used in the postcondition of the program
   --  function.

   function Compute_Exceptional_Cases_Postcondition
     (Params : Transformation_Params;
      E      : Callable_Kind_Id;
      Exc_Id : W_Identifier_Id) return W_Pred_Id;
   --  Returns the postcondition corresponding to the Exceptional_Cases pragma
   --  for subprogram E (if any), to be used in the raises effect of the
   --  program function.

   function Compute_Program_Exit_Postcondition
     (Params : Transformation_Params; E : Callable_Kind_Id) return W_Pred_Id
   with Pre => Has_Program_Exit (E);
   --  Returns the postcondition corresponding to the Program_Exit pragma for
   --  subprogram E (if any), to be used in the raises effect of the program
   --  function.

   function Compute_Dynamic_Property_For_Effects
     (E           : Entity_Id;
      Params      : Transformation_Params;
      Exceptional : Boolean := False) return W_Pred_Id;
   --  Returns an assumption including the dynamic property of every object
   --  modified by a subprogram. If Exceptional is True, only consider
   --  parameters passed by reference and no not assume top-level
   --  initialization of by reference formals with Relaxed_Initialization.

   function Compute_Effects
     (E             : Entity_Id;
      Global_Params : Boolean := False;
      More_Reads    : Flow_Types.Flow_Id_Sets.Set :=
        Flow_Types.Flow_Id_Sets.Empty_Set) return W_Effects_Id;
   --  Compute the effects of the generated Why function. If Global_Params is
   --  True, then the global version of the parameters is used.
   --  More_Reads is a set of globals that should be considered as read by
   --  the subprogram in addition to its actual inputs. It is used to handle
   --  calls with higher order specialization.

   function Compute_Guard_Formula
     (Binders : Item_Array; Params : Transformation_Params) return W_Pred_Id;
   --  For every object in the binder array, build a predicate for the dynamic
   --  invariant of the object and join everything together with a conjunction.

   function Compute_Guard_For_Dispatch
     (Subp    : Entity_Id;
      Binders : Item_Array;
      W_Tag   : W_Term_Id;
      Params  : Transformation_Params) return W_Pred_Id;
   --  For every object in the binder array whose type matches the dispatching
   --  type of Subp, state that the tag of the object is equal to W_Tag.

   function Compute_Inlined_Expr
     (Function_Entity    : Entity_Id;
      Logic_Func_Binders : Item_Array;
      W_Return_Type      : W_Type_Id;
      Params             : Transformation_Params) return W_Term_Id;
   --  @param Function_Entity entity of a function
   --  @param Logic_Func_Binders binders for Function_Entity's declaration if
   --     local names should be used for these binders
   --  @param W_Return_Type Why3 type for Function_Entity's return type
   --  @param Params parameters for the translation
   --  @return if Function_Entity is non recursive and has a pragma
   --     Annotate (GNATprove, Inline_For_Proof), return the Why3 expression
   --     for its value; if Function_Entity has a pragma Annotate (GNATprove,
   --     Logic_Equal), return a call to the builtin equality of Why3;
   --     otherwise return Why_Empty.

   function Compute_Moved_Property_For_Deep_Outputs
     (E : Entity_Id; Params : Transformation_Params) return W_Prog_Id
   with
     Pre =>
       Ekind (E)
       in E_Procedure
        | E_Function
        | E_Package
        | E_Task_Type
        | E_Entry
        | E_Subprogram_Type;
   --  Compute the program assuming that deep outputs of E have all pointers
   --  moved at subprogram entry.

   function Compute_Raw_Binders (E : Entity_Id) return Item_Array;
   --  Return Why binders for the parameters of subprogram E. The array is
   --  empty if E has no parameters.

   function Compute_Type_Invariants_For_Subprogram
     (E           : Entity_Id;
      Params      : Transformation_Params;
      For_Input   : Boolean;
      Exceptional : Boolean := False) return W_Pred_Id
   with
     Pre =>
       (Is_Subprogram_Or_Entry (E) or Ekind (E) = E_Subprogram_Type)
       and then (if Exceptional then not For_Input);
   --  Conjuncts all invariants produced by
   --  Process_Type_Invariants_For_Subprogram. E is used as a scope for
   --  invariants.

   procedure Declare_Exceptions (Th : Theory_UC);
   --  Declare exceptions needed for translation of the current unit. Those
   --  are introduced when translating loop exit statements and goto
   --  statements.

   procedure Generate_Dispatch_Compatibility_Axioms
     (Th : Theory_UC; E : Entity_Id)
   with
     Pre =>
       Is_Dispatching_Operation (E)
       and then not Is_Hidden_Dispatching_Operation (E);
   --  @param E a dispatching subprogram
   --  Emit compatibility axioms between the dispatching version of E and each
   --  visible overriding / inherited versions of E.

   procedure Generate_Ref_For_Concurrent_Self
     (Th : Theory_UC; Prot_Ty : Entity_Id; Location : Source_Ptr)
   with Pre => Is_Protected_Type (Prot_Ty);
   --  Generate the self reference for Prot_Ty in Th

   function Get_Location_For_Aspect
     (E         : Entity_Id;
      Kind      : Pragma_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Node_Id
   with
     Pre =>
       Kind
       in Pragma_Precondition
        | Pragma_Postcondition
        | Pragma_Refined_Post
        | Pragma_Contract_Cases;
   --  Return a node with a proper location for the pre- or postcondition of E,
   --  if any.

   function Include_All_Global_Invariants_For_Subp
     (E : Entity_Id) return Boolean
   is (Is_Globally_Visible (E) or else Is_Declared_In_Main_Unit_Or_Parent (E));
   --  If E is a private subprogram, type invariants of its enclosing units may
   --  be broken for its parameters and result. Ignore type invariants for
   --  private subprograms declared in other library units (for those declared
   --  in the current unit, it is OK, as local type invariants are already not
   --  part of the dynamic invariant). This is an over approximation.

   function Insert_Bindings_For_Variants
     (E      : Entity_Id;
      Prog   : W_Prog_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Prog_Id;
   --  Add binding for the initial value of variants

   function Number_Of_Func_Args (E : Entity_Id) return Natural
   is (Number_Formals (E) + (if Need_Self_Binder (E) then 1 else 0));

   function Preservation_Of_Access_Parameters
     (E : Entity_Id; Params : Transformation_Params) return W_Pred_Id;
   --  Access parameters are mutable, but the bounds or discriminants of their
   --  designated value cannot be modified. Generate an assumption saying they
   --  are preserved.

   function Procedure_Logic_Binders (E : Entity_Id) return Binder_Array;
   --  Return binders that should be used for specific_post of a procedure E

   function Tag_Binder return Binder_Type
   is (Binder_Type'
         (Ada_Node => Empty,
          B_Name   =>
            New_Identifier
              (Name => To_String (WNE_Attr_Tag), Typ => EW_Int_Type),
          B_Ent    => Null_Entity_Name,
          Mutable  => False,
          Labels   => <>));
   --  Binder to be used as additional tag argument for dispatching functions

   function Wrap_Post_Of_Traversal
     (E      : Entity_Id;
      Post   : W_Pred_Id;
      Args   : W_Expr_Array;
      Params : Transformation_Params) return W_Pred_Id
   with Pre => Is_Borrowing_Traversal_Function (E);
   --  The postcondition of traversal functions might refer to the value of the
   --  result of the function and the borrowed parameter at the end of the
   --  borrow (if it contains a call to a pledge function). Introduce bindings
   --  for them.

   function Wrap_Post_Of_Potentially_Invalid
     (E : Entity_Id; Post : W_Pred_Id) return W_Pred_Id;
   --  Introduce bindings for the value part and the validity flag of functions
   --  with a potentially invalid result.

   ----------------------------------------------
   -- Assume_Initial_Condition_Of_Withed_Units --
   ----------------------------------------------

   function Assume_Initial_Condition_Of_Withed_Units
     (Main : Entity_Id; Params : Transformation_Params) return W_Prog_Id
   is
      CU           : constant Node_Id := Enclosing_Comp_Unit_Node (Main);
      Context_Item : Node_Id;
      Assumption   : W_Prog_Id := +Void;
      Withed_Unit  : Node_Id;
      Withed       : Entity_Id;

   begin
      pragma Assert (Present (CU));

      --  For each withed unit which is a package declaration, assume its
      --  Initial_Condition if the elaboration of the withed unit is known
      --  to precede the elaboration of E or if E is a subprogram (all withed
      --  units are elaborated before the main subprogram is called).

      Context_Item := First (Context_Items (CU));
      while Present (Context_Item) loop
         if Nkind (Context_Item) = N_With_Clause
           and then not Limited_Present (Context_Item)
         then
            Withed_Unit := Unit (Library_Unit (Context_Item));
            Withed :=
              (if Present (Withed_Unit)
               then Unique_Defining_Entity (Withed_Unit)
               else Empty);

            if Nkind (Withed_Unit) = N_Package_Declaration
              and then (Is_Subprogram (Main)
                        or else Known_To_Precede
                                  (Withed => Withed, Main => Main))
            then
               declare
                  Init_Conds : constant Node_Lists.List :=
                    Find_Contracts (Withed, Pragma_Initial_Condition);
               begin
                  for Expr of Init_Conds loop
                     Append
                       (Assumption,
                        New_Assume_Statement
                          (Pred =>
                             Transform_Pred (Expr, EW_Bool_Type, Params)));
                  end loop;
               end;

            --  Otherwise raise a warning if --info is given and there is an
            --  Initial_Condition.

            elsif Nkind (Withed_Unit) = N_Package_Declaration
              and then Has_Contracts (Withed, Pragma_Initial_Condition)
              and then (Ekind (Main) /= E_Package_Body
                        or else Withed /= Unique_Entity (Main))
            then
               Warning_Msg_N
                 (Warn_Init_Cond_Ignored,
                  Main,
                  Names         => [Withed],
                  Continuations =>
                    [Create
                       ("the elaboration of & is not known to"
                        & " precede the elaboration of the current"
                        & " unit",
                        Names => [Withed]),
                     Create
                       ("use pragma Elaborate_Body in & or pragma"
                        & " Elaborate in the current unit",
                        Names => [Withed])]);
            end if;
         end if;

         Next (Context_Item);
      end loop;

      return Assumption;
   end Assume_Initial_Condition_Of_Withed_Units;

   ----------------------------
   -- Check_Ceiling_Protocol --
   ----------------------------

   function Check_Ceiling_Protocol
     (Params : Transformation_Params; E : Entity_Id) return W_Prog_Id
   is

      function Self_Priority return W_Term_Id;
      --  @return expression for the priority of entity E

      -------------------
      -- Self_Priority --
      -------------------

      function Self_Priority return W_Term_Id is
         --  If the priority is not explicitly specified then assume:
         --    * for main-like subprograms -> System.Default_Priority,
         --    * for tasks                 -> System.Priority'Last
         --    * for protected subprograms ->
         --        System.Priority'Last or System.Interrupt_Priority'Last
         --  which are worst-cases for tasks and protected subprograms
         --  and exact value for main-like subprograms.

         --  To know the exact value for tasks we would have to know the
         --  priority inherited from the enviromental task; the exact value
         --  for protected subprograms with Interrupt_Handler or Attach_Handler
         --  present is implementation-specific (but in GNAT it is
         --  System.Interrupt_Priority'Last, so we are exact).
         --
         --  For details on default priorities see RM D.1 (19) and D.3 (10,11).

         Pragma_Entity : constant Entity_Id :=
           (if Ekind (E) = E_Task_Type
            then E
            elsif Ekind (E) in Subprogram_Kind and then Might_Be_Main (E)
            then E
            elsif Is_Protected_Operation (E)
            then Enclosing_Type (E)
            else raise Program_Error);
         --  Entity where Priority or Interrupt_Priority pragma is attached

         Prio_Expr : constant Node_Id :=
           Get_Priority_Or_Interrupt_Priority (Pragma_Entity);
         --  Priority expression

      begin
         if Present (Prio_Expr) then
            return Transform_Term (Prio_Expr, EW_Int_Type, Params);
         end if;

         --  No explicit priority was given

         if Ekind (E) = E_Task_Type then
            --  If pragma Interrupt_Priority is present then build expression
            --  for System.Interrupt_Priority'Last; otherwise for
            --  System.Priority'Last.
            return
              +New_Attribute_Expr
                 (Domain => EW_Term,
                  Ty     =>
                    RTE
                      (if Present (Get_Rep_Item (E, Name_Interrupt_Priority))
                       then RE_Interrupt_Priority
                       else RE_Priority),
                  Attr   => Attribute_Last,
                  Params => Params);

         elsif Ekind (E) in Subprogram_Kind and then Might_Be_Main (E) then
            --  Return expression used that defined System.Default_Priority
            return
              Transform_Term
                (Expr   =>
                   Expression
                     (Enclosing_Declaration (RTE (RE_Default_Priority))),
                 Params => Params);

         else
            pragma Assert (Is_Protected_Operation (E));
            declare
               PT : constant Entity_Id := Enclosing_Type (E);

               Type_Id : RE_Id;
               Attr_Id : Supported_Attribute_Id;
               --  Type and attribute for priority expression
            begin
               if Present (Get_Rep_Item (PT, Name_Interrupt_Priority)) then
                  --  Pragma Interrupt_Priority without expression defaults to
                  --  Interrupt_Priority'Last; RM J.15(12).
                  Type_Id := RE_Interrupt_Priority;
                  Attr_Id := Attribute_Last;

               elsif Has_Interrupt_Handler (PT) or else Has_Attach_Handler (PT)
               then
                  --  Assume the worst case of implementation-defined value
                  --  within Interrupt_Priority; RM D.3(10).
                  Type_Id := RE_Interrupt_Priority;
                  Attr_Id := Attribute_First;

               else
                  --  Default priority for protected type is Priority'Last
                  Type_Id := RE_Priority;
                  Attr_Id := Attribute_Last;

               end if;

               return
                 +New_Attribute_Expr
                    (Domain => EW_Term,
                     Ty     => RTE (Type_Id),
                     Attr   => Attr_Id,
                     Params => Params);

            end;
         end if;

      end Self_Priority;

      function To_String (Trace : Name_Lists.List) return String
      with Pre => not Trace.Is_Empty;
      --  Helper to generate a string for the call trace.

      procedure Msg_Details
        (Locked_Obj : Entity_Name;
         Trace      : Name_Lists.List;
         Subject    : out Unbounded_String;
         Details    : out Unbounded_String)
      with Pre => not Trace.Is_Empty;
      --  Generates contents for the subject and details sections of a ceiling
      --  priority check message.
      --
      --  Typically Trace has at least 2 elements - the source and target
      --  operations. Exceptionally, in the case of recursion it will have
      --  length 1. This function must support such traces as well. However,
      --  such traces will typically not appear in the output due to other
      --  constraints.

      ---------------
      -- To_String --
      ---------------

      function To_String (Trace : Name_Lists.List) return String is
         Result         : Unbounded_String;
         Position       : Ada.Containers.Count_Type := 1;
         In_Elaboration : Boolean := False;
         Split_Lines    : constant Boolean :=
           Trace.Length > 2 and then Gnat2Why_Args.Output_Mode in GPO_Pretty;
      begin

         --  Typically the chain elements are subprograms. However, in call
         --  traces involving a "main" subprogram and elaboration code of
         --  withed units the 2nd element of a chain is a package.
         --
         --  Note: This might be made more exact by checking if the entity is a
         --  package. In general the call trace can include the elaboration of
         --  multiple packages. However, currently only the package whose
         --  elaboration contains the actual call is provided in the trace at
         --  position 2. (That's because the withed units are flattened to a
         --  closure.)

         if Trace.Length >= 2
           and then Top_Level_Packages.Contains
                      (Trace (Name_Lists.Next (Trace.First)))
         then
            In_Elaboration := True;
         end if;

         --  Build the message string

         if Split_Lines then
            Append (Result, ':' & ASCII.LF & "        ");
         else
            Append (Result, ' ');
         end if;

         for Call of Trace loop
            if Position > 1 then
               if Split_Lines then
                  Append
                    (Result, ASCII.LF & SGR_Note & "        -> " & SGR_Reset);
               else
                  Append (Result, " -> ");
               end if;
            end if;

            Append (Result, '"' & Pretty_Print (Call) & '"');

            if In_Elaboration and then Position <= 2 then
               Append (Result, " (elaboration)");
            end if;
            Position := Position + 1;
         end loop;

         return To_String (Result);
      end To_String;

      -----------------
      -- Msg_Details --
      -----------------

      procedure Msg_Details
        (Locked_Obj : Entity_Name;
         Trace      : Name_Lists.List;
         Subject    : out Unbounded_String;
         Details    : out Unbounded_String)
      is
         Source renames Trace.First_Element;

         Locked_Obj_Pretty : constant String := Pretty_Print (Locked_Obj);

      begin
         Append (Subject, "for """ & Locked_Obj_Pretty & '"');

         --  The details of the proved and unproved messages currently differ
         --  only at the end. For the unproved message we show *one* failing
         --  trace. In the proved case *all* the potential calls to the given
         --  protected object are proven to be safe.
         Append (Details, "ceiling priority of the protected object """);
         Append (Details, Locked_Obj_Pretty);
         Append (Details, """ must be >= the priority of the");
         Append (Details, " caller """);
         Append (Details, Pretty_Print (Source) & '"');
         Append (Details, " in the call");

         if Trace.Length > 2 then
            Append (Details, " chain");
         end if;

         Append (Details, To_String (Trace));
      end Msg_Details;

      --  Start of processing for Check_Ceiling_Protocol

   begin
      if Ekind (E) not in E_Task_Type | E_Entry
        and then not Might_Be_Main (E)
        and then not Is_Protected_Operation (E)
      then
         return +Void;
      end if;

      declare
         Self_Prio : constant W_Term_Id := Self_Priority;
         S         : W_Prog_Id := +Void;
         --  Placeholder for a Why3 sequence that will represent the check

         procedure Create_Check
           (Obj_Name : Entity_Name;
            Obj_Prio : Priority_Value;
            Trace    : Name_Lists.List);
         --  Create check for accessing the protected object Obj_Name with
         --  priority Obj_Prio via call chain Trace.
         ------------------
         -- Create_Check --
         ------------------

         procedure Create_Check
           (Obj_Name : Entity_Name;
            Obj_Prio : Priority_Value;
            Trace    : Name_Lists.List) is
         begin
            --  Create a check that compares the priority of the calling
            --  context and the locked object or protected component. See ARM,
            --  D.3 (7-11) for details.

            declare
               Obj_Prio_Expr : constant W_Term_Id :=
                 (case Obj_Prio.Kind is
                    --  ??? if type of the component is visible we
                    --  should try to transform the expression.
                    when Nonstatic              =>
                      +New_Attribute_Expr
                         (Domain => EW_Term,
                          Ty     => RTE (RE_Any_Priority),
                          Attr   => Attribute_First,
                          Params => Params),

                    when Static                 =>
                      New_Integer_Constant
                        (Value => UI_From_Int (Obj_Prio.Value)),

                    when Default_Prio           =>
                      +New_Attribute_Expr
                         (Domain => EW_Term,
                          Ty     => RTE (RE_Priority),
                          Attr   => Attribute_Last,
                          Params => Params),

                    when Default_Interrupt_Prio =>
                      +New_Attribute_Expr
                         (Domain => EW_Term,
                          Ty     => RTE (RE_Interrupt_Priority),
                          Attr   => Attribute_First,
                          Params => Params),

                    when Last_Interrupt_Prio    =>
                      +New_Attribute_Expr
                         (Domain => EW_Term,
                          Ty     => RTE (RE_Interrupt_Priority),
                          Attr   => Attribute_Last,
                          Params => Params));

               Pred : constant W_Pred_Id :=
                 New_Comparison
                   (Symbol =>
                      (case Obj_Prio.Kind is
                         when Nonstatic => Why_Eq,
                         when others    => Int_Infix_Le),
                    Left   => Self_Prio,
                    Right  => Obj_Prio_Expr);

               Info    : Check_Info_Type;
               Subject : Unbounded_String;
               Details : Unbounded_String;
               Check   : W_Prog_Id;

            begin
               Msg_Details
                 (Locked_Obj => Obj_Name,
                  Trace      => Trace,
                  Subject    => Subject,
                  Details    => Details);

               Info :=
                 New_Check_Info
                   (Subject => To_String (Subject),
                    Details => To_String (Details));

               Check :=
                 New_Located_Assert
                   (Ada_Node   => E,
                    Pred       => Pred,
                    Reason     => VC_Ceiling_Priority_Protocol,
                    Kind       => EW_Check,
                    Check_Info => Info);
               Append (S, Check);
            end;
         end Create_Check;

      begin

         --  Loop over the protected objects that are reachable from the caller

         for Locking of Directly_Called_Protected_Objects (E) loop
            Create_Check
              (Obj_Name => Locking.Obj,
               Trace    => Locking.Trace,
               Obj_Prio => Protected_Object_Priority (Locking.Obj));
         end loop;

         return S;
      end;
   end Check_Ceiling_Protocol;

   ----------------------------------------
   --  Check_Type_Invariants_For_Package --
   ----------------------------------------

   function Check_Type_Invariants_For_Package
     (E : Entity_Id; Params : Transformation_Params) return W_Prog_Id
   is
      Checks : W_Statement_Sequence_Id := Void_Sequence;

   begin
      --  We use the Initializes aspect to get the variables initialized during
      --  elaboration.
      --  We don't do it for wrapper packages as they do not have local
      --  variables / constants.

      if not Is_Wrapper_Package (E) then
         declare
            Init_Map   : constant Dependency_Maps.Map :=
              Parse_Initializes (E, Get_Flow_Scope (E));
            Check_Info : Check_Info_Type := New_Check_Info;

         begin
            --  The checks will be localized at the global declaration. Add a
            --  continuation to make it clear that the checks are done after
            --  the package's elaboration.

            Check_Info.Continuation.Append
              (Continuation_Type'
                 (E,
                  To_Unbounded_String
                    ("at the end of the elaboration of package")));

            for Cu in Init_Map.Iterate loop
               declare
                  K  : Flow_Id renames Dependency_Maps.Key (Cu);
                  FS : constant Flow_Id_Sets.Set := Expand_Abstract_State (K);

                  --  From the expansion of the LHS of an Initializes contract
                  --  we only get constants, variables and abstract states
                  --  (when the expansion stops at a SPARK_Mode => Off); these
                  --  are known by an Entity_Id but are wrapped in a
                  --  Direct_Mapping or Magic_String kinds of Flow_Id,
                  --  depending whether they are in SPARK.

               begin
                  for F of FS loop
                     case F.Kind is
                        when Direct_Mapping =>
                           declare
                              Obj : Entity_Id := Get_Direct_Mapping_Id (F);

                              pragma
                                Assert
                                  (Ekind (Obj)
                                   in E_Abstract_State
                                    | E_Constant
                                    | E_Variable);

                           begin
                              --  Only partial views of constants are stored in
                              --  the symbol map.

                              if Ekind (Obj) = E_Constant
                                and then Is_Full_View (Obj)
                              then
                                 Obj := Partial_View (Obj);
                              end if;

                              --  Only consider objects that are in SPARK.
                              --  Other objects (and abstract states) are
                              --  translated to a private type in Why.

                              if Is_Object (Obj)
                                and then not Is_Part_Of_Concurrent_Object (Obj)
                              then
                                 declare
                                    Binder  : constant Item_Type :=
                                      Ada_Ent_To_Why.Element
                                        (Symbol_Table, Obj);
                                    Expr    : constant W_Term_Id :=
                                      Reconstruct_Item
                                        (Binder,
                                         Ref_Allowed => Params.Ref_Allowed);
                                    Dyn_Inv : constant W_Pred_Id :=
                                      Compute_Type_Invariant
                                        (Expr   => Expr,
                                         Ty     => Etype (Obj),
                                         Kind   => For_Check,
                                         Params => Params,
                                         Scop   => E);
                                 begin
                                    if not Is_True_Boolean (+Dyn_Inv) then
                                       Append
                                         (Checks,
                                          Right =>
                                            New_Assert
                                              (Pred        =>
                                                 New_VC_Pred
                                                   (Obj,
                                                    Dyn_Inv,
                                                    VC_Invariant_Check,
                                                    Check_Info),
                                               Assert_Kind => EW_Assert));
                                    end if;
                                 end;
                              end if;
                           end;

                        when Magic_String   =>
                           pragma Assert (Is_Opaque_For_Proof (F));

                        when others         =>
                           raise Program_Error;
                     end case;
                  end loop;
               end;
            end loop;
         end;
      end if;

      return +Checks;
   end Check_Type_Invariants_For_Package;

   ----------------------
   -- Clear_Exceptions --
   ----------------------

   procedure Clear_Exceptions is
   begin
      Subprogram_Exceptions.Clear;
   end Clear_Exceptions;

   --------------------------------
   -- Collect_Old_For_Subprogram --
   --------------------------------

   procedure Collect_Old_For_Subprogram
     (E                 : Callable_Kind_Id;
      Old_Parts         : in out Node_Sets.Set;
      Exclude_Classwide : Boolean := True;
      Exclude_CC        : Boolean := False)
   is
      CC_List   : constant Node_Lists.List :=
        (if Exclude_CC
         then Node_Lists.Empty_List
         else Find_Contracts (E, Pragma_Contract_Cases));
      EC_Prag   : constant Node_Id := Get_Pragma (E, Pragma_Exceptional_Cases);
      PE_Prag   : constant Node_Id := Get_Pragma (E, Pragma_Program_Exit);
      Post_List : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Postcondition);
   begin
      Collect_Old_Parts (Post_List, Old_Parts);

      --  If there are no post pragmas or contract cases, the post defaults to
      --  the classwide one.

      if not Exclude_Classwide
        and then Post_List.Is_Empty
        and then CC_List.Is_Empty
      then
         declare
            Classwide_List : constant Node_Lists.List :=
              Find_Contracts (E, Pragma_Postcondition, Classwide => True);
         begin
            Collect_Old_Parts (Classwide_List, Old_Parts);

            --  If no classwide post is specified for E, use the inherited one.

            if Classwide_List.Is_Empty then
               Collect_Old_Parts
                 (Find_Contracts (E, Pragma_Postcondition, Inherited => True),
                  Old_Parts);
            end if;
         end;
      end if;

      --  Go over contract cases to collect the old attributes. Also collect
      --  the guards which have to be evaluated in the pre-state.

      if not Exclude_CC then
         for Aggr of CC_List loop
            declare
               Contract_Case : Node_Id :=
                 First (Component_Associations (Aggr));
            begin
               while Present (Contract_Case) loop
                  Collect_Old_Parts (Expression (Contract_Case), Old_Parts);
                  if not Is_Others_Choice (Choice_List (Contract_Case)) then
                     Old_Parts.Include (First (Choice_List (Contract_Case)));
                  end if;

                  Next (Contract_Case);
               end loop;
            end;
         end loop;
      end if;

      --  Go over exceptional cases to collect the old attributes

      if Present (EC_Prag) then
         declare
            Aggr             : constant Node_Id :=
              Expression (First (Pragma_Argument_Associations (EC_Prag)));
            Exceptional_Case : Node_Id :=
              First (Component_Associations (Aggr));
         begin
            while Present (Exceptional_Case) loop
               Collect_Old_Parts (Expression (Exceptional_Case), Old_Parts);

               Next (Exceptional_Case);
            end loop;
         end;
      end if;

      --  Collect the old attributes in the program exit contract

      if Present (PE_Prag) then
         declare
            Assoc : constant List_Id := Pragma_Argument_Associations (PE_Prag);
         begin
            if Present (Assoc) then
               Collect_Old_Parts (Expression (First (Assoc)), Old_Parts);
            end if;
         end;
      end if;
   end Collect_Old_For_Subprogram;

   ------------------
   -- Compute_Args --
   ------------------

   function Compute_Args
     (E          : Entity_Id;
      Binders    : Binder_Array;
      More_Reads : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return W_Expr_Array
   is
      Logic_Args : constant W_Expr_Array :=
        Get_Logic_Args (E, True, More_Reads);
      Params     : constant W_Expr_Array :=
        (if Number_Of_Func_Args (E) = 0
         then (1 .. 0 => <>)
         else Get_Args_From_Binders (Binders, True));

   begin
      if Params'Length = 0 and then Logic_Args'Length = 0 then
         return W_Expr_Array'(1 => +Void);
      end if;

      return Params & Logic_Args;
   end Compute_Args;

   ----------------------------------
   -- Compute_Attach_Handler_Check --
   ----------------------------------

   function Compute_Attach_Handler_Check
     (Ty : Entity_Id; Params : Transformation_Params) return W_Prog_Id
   is
      function Single_Attach_Handler_Check (Proc : Entity_Id) return W_Prog_Id;
      --  @param Proc a procedure with an Attach_Handler pragma
      --  @return an assertion statement that expresses the attach handler
      --    check for this pragma

      procedure Process_Declarations (L : List_Id);
      --  @param L list of declarations to check for interrupt attachments

      Stat : W_Prog_Id := +Void;
      --  Why3 program with static checks

      ---------------------------------
      -- Single_Attach_Handler_Check --
      ---------------------------------

      function Single_Attach_Handler_Check (Proc : Entity_Id) return W_Prog_Id
      is

         --  The interrupt is given as the second argument of the pragma
         --  Attach_Handler.
         Att_Val : constant Node_Id :=
           Expression
             (Next
                (First
                   (Pragma_Argument_Associations
                      (Get_Pragma (Proc, Pragma_Attach_Handler)))));

         --  To check whether the attach handler is reserved, we call the
         --  Ada.Interrupts.Is_Reserved. However, this function reads a global
         --  state, which makes it a bit difficult to generate a call in
         --  the logic (we would have to come up with the state object - not
         --  impossible but not currently proposed by frontend). Instead,
         --  we call the program function, which has only the interrupt as
         --  argument, store the result in a temp and assert that the result
         --  is false. So we are essentially asserting "not is_reserved(int)".

         Res : constant W_Expr_Id :=
           New_Temp_For_Expr
             (New_Call
                (Name   => To_Why_Id (RTE (RE_Is_Reserved), Domain => EW_Prog),
                 Domain => EW_Prog,
                 Args   =>
                   (1 =>
                      Transform_Expr (Att_Val, EW_Int_Type, EW_Prog, Params)),
                 Typ    => EW_Bool_Type));

         Pred : constant W_Pred_Id :=
           New_Call
             (Name => Why_Eq, Args => (1 => +Res, 2 => Bool_False (EW_Term)));
      begin
         return
           +Binding_For_Temp
              (Domain  => EW_Prog,
               Tmp     => Res,
               Context =>
                 +New_Located_Assert
                    (Ada_Node => Att_Val,
                     Reason   => VC_Interrupt_Reserved,
                     Kind     => EW_Check,
                     Pred     => Pred));
      end Single_Attach_Handler_Check;

      --------------------------
      -- Process_Declarations --
      --------------------------

      procedure Process_Declarations (L : List_Id) is
         Proc : Node_Id := First (L);
      begin
         while Present (Proc) loop
            if Nkind (Proc) = N_Subprogram_Declaration then
               declare
                  Ent : constant Entity_Id := Unique_Defining_Entity (Proc);
               begin
                  if Ekind (Ent) = E_Procedure
                    and then Present (Get_Pragma (Ent, Pragma_Attach_Handler))
                  then
                     Append (Stat, Single_Attach_Handler_Check (Ent));
                  end if;
               end;
            end if;
            Next (Proc);
         end loop;
      end Process_Declarations;

      --  Start of processing for Compute_Attach_Handler_Check

   begin
      Process_Declarations (Visible_Declarations_Of_Prot_Type (Ty));

      if Private_Spec_In_SPARK (Ty) then
         Process_Declarations (Private_Declarations_Of_Prot_Type (Ty));
      end if;

      return Stat;
   end Compute_Attach_Handler_Check;

   ---------------------
   -- Compute_Binders --
   ---------------------

   function Compute_Binders
     (E          : Entity_Id;
      Domain     : EW_Domain;
      More_Reads : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return Item_Array
   is
      Binders : constant Item_Array :=
        Compute_Subprogram_Parameters (E, Domain, More_Reads);
   begin
      --  If E has no parameters, return a singleton of unit type.

      if Binders'Length = 0 then
         return
           (1 =>
              (Regular,
               Local    => True,
               Init     => <>,
               Is_Moved => <>,
               Valid    => <>,
               Main     => Unit_Param));
      else
         return Binders;
      end if;
   end Compute_Binders;

   --------------------------
   -- Compute_Call_Effects --
   --------------------------

   function Compute_Call_Effects
     (Params : Transformation_Params; E : Callable_Kind_Id) return W_Prog_Id
   is
      Call_Effects : W_Prog_Id;
   begin
      Call_Effects :=
        New_Havoc_Statement
          (Ada_Node => E,
           Effects  => +Compute_Effects (E, Global_Params => True));

      Append
        (Call_Effects,
         New_Assume_Statement
           (Ada_Node => E,
            Pred     => Compute_Dynamic_Property_For_Effects (E, Params)));

      return Call_Effects;
   end Compute_Call_Effects;

   -------------------------------------
   -- Compute_CC_And_EC_Postcondition --
   -------------------------------------

   function Compute_CC_And_EC_Postcondition
     (Params : Transformation_Params; E : Callable_Kind_Id) return W_Pred_Id
   is (New_And_Pred
         (Left  => Compute_Contract_Cases_Postcondition (Params, E),
          Right =>
            Compute_Exit_Cases_Simple_Post (Params, E, Name_Normal_Return)));

   -----------------------------------------
   -- Compute_Dynamic_Property_For_Inputs --
   -----------------------------------------

   function Compute_Dynamic_Property_For_Inputs
     (E              : Unit_Kind_Id;
      Params         : Transformation_Params;
      Pred_Fun_Param : Entity_Id := Empty) return W_Prog_Id
   is
      Includes : Node_Sets.Set;

      procedure Include_Entity (E : Entity_Id; Kind : Formal_Kind);
      --  Add an entity to Includes

      --------------------
      -- Include_Entity --
      --------------------

      procedure Include_Entity (E : Entity_Id; Kind : Formal_Kind) is
         pragma Unreferenced (Kind);
      begin
         Includes.Include (E);
      end Include_Entity;

      procedure Include_Referenced_Entities is new
        Process_Referenced_Entities (Include_Entity);
   begin
      --  Collect global variables read or written in E

      case Ekind (E) is
         when E_Entry
            | E_Function
            | E_Procedure
            | E_Task_Type
            | E_Package
            | E_Subprogram_Type =>
            Include_Referenced_Entities (E);

            --  Collect parameters of E if any

            if Is_Subprogram_Or_Entry (E) then
               Includes.Union (Get_Explicit_Formals (E));

               --  If E is a protected subprogram, add the type itself to stand
               --  for the self reference.

               if Need_Self_Binder (E) and then Entity_Body_In_SPARK (E) then
                  Includes.Include (Containing_Protected_Type (E));
               end if;

            --  Collect discriminants of task types

            elsif Is_Task_Type (E) and then Has_Discriminants (E) then
               declare
                  Discr : Entity_Id := First_Discriminant (E);
               begin
                  while Present (Discr) loop
                     Includes.Include (Discr);
                     Next_Discriminant (Discr);
                  end loop;
               end;
            end if;

         when others            =>
            raise Program_Error;
      end case;

      return
        Assume_Dynamic_Invariant_For_Variables
          (Vars             => Includes,
           Params           => Params,
           Scope            => E,
           Exclude_Top_Pred => Pred_Fun_Param,
           Initialized      => False);
   end Compute_Dynamic_Property_For_Inputs;

   ------------------------------------------
   -- Compute_Dynamic_Property_For_Effects --
   ------------------------------------------

   function Compute_Dynamic_Property_For_Effects
     (E           : Entity_Id;
      Params      : Transformation_Params;
      Exceptional : Boolean := False) return W_Pred_Id
   is
      All_Global_Inv       : constant Boolean :=
        Include_All_Global_Invariants_For_Subp (E);
      Func_Why_Binders     : constant Item_Array :=
        Compute_Binders (E, EW_Prog);
      Dynamic_Prop_Effects : W_Pred_Id := True_Pred;
      Formal               : Entity_Id;
   begin
      --  Compute the dynamic property of mutable parameters

      for I in Func_Why_Binders'Range loop
         Formal := Get_Ada_Node_From_Item (Func_Why_Binders (I));

         --  Only assume dynamic property of concurrent self if the containing
         --  protected type is in SPARK. Otherwise, self will have the type
         --  EW_Private_Type and no dynamic property applies.

         if Func_Why_Binders (I).Kind = Concurrent_Self then
            declare
               Ada_Type : constant Node_Id :=
                 Func_Why_Binders (I).Main.Ada_Node;
            begin
               if Entity_In_SPARK (Ada_Type) then
                  declare
                     Self_Expr : constant W_Expr_Id :=
                       (if Self_Is_Mutable
                        then
                          New_Deref
                            (Right => Self_Name, Typ => Get_Typ (Self_Name))
                        else +Self_Name);
                     Dyn_Prop  : constant W_Pred_Id :=
                       Compute_Dynamic_Inv_And_Initialization
                         (Expr           => +Self_Expr,
                          Ty             => Ada_Type,
                          Params         => Params,
                          All_Global_Inv => All_Global_Inv);
                  begin
                     Dynamic_Prop_Effects :=
                       +New_And_Expr
                          (Left   => +Dynamic_Prop_Effects,
                           Right  => +Dyn_Prop,
                           Domain => EW_Pred);
                  end;
               end if;
            end;
         elsif Item_Is_Mutable (Func_Why_Binders (I))
           and then Entity_In_SPARK (Formal)
         then
            --  On exceptional paths, formals with relaxed initialization
            --  might not be initialized at toplevel.

            if Exceptional then
               if By_Reference (Formal) then
                  declare
                     Ada_Type  : constant Node_Id :=
                       Get_Ada_Type_From_Item (Func_Why_Binders (I));
                     Init_Expr : constant W_Term_Id :=
                       (if Func_Why_Binders (I).Init.Present
                        then
                          New_Deref
                            (Right => Func_Why_Binders (I).Init.Id,
                             Typ   => Get_Typ (Func_Why_Binders (I).Init.Id))
                        else True_Term);

                     Dyn_Prop : constant W_Pred_Id :=
                       Compute_Dynamic_Invariant
                         (Expr           =>
                            +Transform_Identifier
                               (Params => Params,
                                Expr   => Formal,
                                Ent    => Formal,
                                Domain => EW_Term),
                          Ty             => Ada_Type,
                          Params         => Params,
                          Initialized    => Init_Expr,
                          Valid          =>
                            Get_Valid_Id_From_Item
                              (Func_Why_Binders (I), Params.Ref_Allowed),
                          All_Global_Inv => All_Global_Inv);
                  begin
                     Dynamic_Prop_Effects :=
                       +New_And_Expr
                          (Left   => +Dynamic_Prop_Effects,
                           Right  => +Dyn_Prop,
                           Domain => EW_Pred);
                  end;
               end if;

            --  Otherwise, Compute_Dynamic_Inv_And_Initialization can be used
            --  safely.

            else
               declare
                  Ada_Type : constant Node_Id :=
                    Get_Ada_Type_From_Item (Func_Why_Binders (I));
                  Dyn_Prop : constant W_Pred_Id :=
                    Compute_Dynamic_Inv_And_Initialization
                      (Expr           =>
                         +Transform_Identifier
                            (Params => Params,
                             Expr   => Formal,
                             Ent    => Formal,
                             Domain => EW_Term),
                       Ty             => Ada_Type,
                       Params         => Params,
                       Valid          =>
                         Get_Valid_Id_From_Item
                           (Func_Why_Binders (I), Params.Ref_Allowed),
                       All_Global_Inv => All_Global_Inv);
               begin
                  Dynamic_Prop_Effects :=
                    +New_And_Expr
                       (Left   => +Dynamic_Prop_Effects,
                        Right  => +Dyn_Prop,
                        Domain => EW_Pred);
               end;
            end if;
         end if;
      end loop;

      --  Compute the dynamic property of global output

      declare
         Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
         Write_Ids : Flow_Types.Flow_Id_Sets.Set;

      begin
         Flow_Utility.Get_Proof_Globals
           (Subprogram      => E,
            Reads           => Read_Ids,
            Writes          => Write_Ids,
            Erase_Constants => True);

         for Write_Id of Write_Ids loop
            if Write_Id.Kind = Direct_Mapping then
               declare
                  Entity : constant Entity_Id :=
                    Get_Direct_Mapping_Id (Write_Id);

               begin
                  if not Is_Concurrent_Type (Entity) then
                     declare
                        Init_Id  : constant W_Expr_Id :=
                          Get_Init_Id_From_Object (Entity, Params.Ref_Allowed);
                        Dyn_Prop : constant W_Pred_Id :=
                          Compute_Dynamic_Invariant
                            (Expr        =>
                               +Transform_Identifier
                                  (Params => Params,
                                   Expr   => Entity,
                                   Ent    => Entity,
                                   Domain => EW_Term),
                             Ty          => Etype (Entity),
                             Params      => Params,
                             Valid       =>
                               Get_Valid_Id_From_Object
                                 (Entity, Params.Ref_Allowed),
                             Initialized =>
                               (if Init_Id /= Why_Empty
                                then +Init_Id
                                else True_Term));
                     begin
                        Dynamic_Prop_Effects :=
                          +New_And_Expr
                             (Left   => +Dynamic_Prop_Effects,
                              Right  => +Dyn_Prop,
                              Domain => EW_Pred);
                     end;
                  end if;
               end;
            end if;
         end loop;
      end;

      return Dynamic_Prop_Effects;
   end Compute_Dynamic_Property_For_Effects;

   ---------------------
   -- Compute_Effects --
   ---------------------

   function Compute_Effects
     (E             : Entity_Id;
      Global_Params : Boolean := False;
      More_Reads    : Flow_Types.Flow_Id_Sets.Set :=
        Flow_Types.Flow_Id_Sets.Empty_Set) return W_Effects_Id
   is
      Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids : Flow_Types.Flow_Id_Sets.Set;
      Eff       : constant W_Effects_Id := New_Effects;

      procedure Effects_Append_Binder_To_Reads is new
        Effects_Append_Binder (Effects_Append_To_Reads);

      procedure Effects_Append_Binder_To_Writes is new
        Effects_Append_Binder (Effects_Append_To_Writes);

      --  Start of processing for Compute_Effects

   begin
      --  Collect global variables potentially read and written

      Flow_Utility.Get_Proof_Globals
        (Subprogram      => E,
         Reads           => Read_Ids,
         Writes          => Write_Ids,
         Erase_Constants => True);

      Read_Ids.Union (More_Reads);

      for Write_Id of Write_Ids loop
         case Write_Id.Kind is
            when Direct_Mapping =>
               declare
                  Entity : constant Entity_Id :=
                    Get_Direct_Mapping_Id (Write_Id);

               begin
                  --  Effects on concurrent types are handled by other means

                  if not Is_Concurrent_Type (Entity) then
                     Effects_Append_Binder_To_Writes
                       (Eff, Ada_Ent_To_Why.Element (Symbol_Table, Entity));

                     if Is_Local_Borrower (Entity) then
                        Effects_Append_To_Writes
                          (Eff, Get_Brower_At_End (Entity));
                     end if;
                  end if;

               end;

            when Magic_String   =>
               declare
                  Cu : constant Ada_Ent_To_Why.Cursor :=
                    Ada_Ent_To_Why.Find (Symbol_Table, To_Name (Write_Id));

               begin
                  --  If Write_Id is in the symbol table, use this mapping

                  if Ada_Ent_To_Why.Has_Element (Cu) then
                     Effects_Append_Binder_To_Writes
                       (Eff, Ada_Ent_To_Why.Element (Cu));

                  --  Otherwise, use the id name

                  else
                     Effects_Append_To_Writes
                       (Eff,
                        To_Why_Id (Obj => To_Name (Write_Id), Local => False));
                  end if;
               end;

            when others         =>
               raise Program_Error;
         end case;
      end loop;

      --  Add all OUT and IN OUT parameters as potential writes.
      --  If Global_Params is True, use binders from the Symbol_Table;
      --  otherwise, use binders from the function declaration.

      if Global_Params then
         declare
            Formal : Entity_Id := First_Formal (E);
         begin
            while Present (Formal) loop
               declare
                  B : constant Item_Type :=
                    Ada_Ent_To_Why.Element (Symbol_Table, Formal);
               begin
                  Effects_Append_Binder_To_Writes (Eff, B);
               end;
               Next_Formal (Formal);
            end loop;
         end;
      else
         declare
            Binders : constant Item_Array := Compute_Raw_Binders (E);
         begin
            for B of Binders loop
               Effects_Append_Binder_To_Writes (Eff, B);
            end loop;
         end;
      end if;

      for Read_Id of Read_Ids loop
         case Read_Id.Kind is
            when Direct_Mapping =>
               declare
                  Entity : constant Entity_Id :=
                    Get_Direct_Mapping_Id (Read_Id);

               begin
                  --  Effects on concurrent types are handled by other means

                  if not Is_Concurrent_Type (Entity) then
                     Effects_Append_Binder_To_Reads
                       (Eff, Ada_Ent_To_Why.Element (Symbol_Table, Entity));
                  end if;
               end;

            when Magic_String   =>
               declare
                  Cu : constant Ada_Ent_To_Why.Cursor :=
                    Ada_Ent_To_Why.Find (Symbol_Table, To_Name (Read_Id));

               begin
                  --  If Read_Id is in the symbol table, use this mapping

                  if Ada_Ent_To_Why.Has_Element (Cu) then
                     Effects_Append_Binder_To_Reads
                       (Eff, Ada_Ent_To_Why.Element (Cu));

                  --  Otherwise, use the id name

                  else
                     Effects_Append_To_Reads
                       (Eff,
                        To_Why_Id (Obj => To_Name (Read_Id), Local => False));
                  end if;
               end;

            when others         =>
               raise Program_Error;
         end case;
      end loop;

      return +Eff;
   end Compute_Effects;

   --------------------------------
   -- Compute_Guard_For_Dispatch --
   --------------------------------

   function Compute_Guard_For_Dispatch
     (Subp    : Entity_Id;
      Binders : Item_Array;
      W_Tag   : W_Term_Id;
      Params  : Transformation_Params) return W_Pred_Id
   is
      D_Ty : constant Entity_Id := Find_Dispatching_Type (Subp);
      Pred : W_Pred_Id := True_Pred;
   begin
      for B of Binders loop
         if D_Ty = Get_Ada_Type_From_Item (B) then
            case B.Kind is
               when Regular =>
                  Pred :=
                    New_And_Pred
                      (Left  => Pred,
                       Right =>
                         New_Comparison
                           (Symbol => Why_Eq,
                            Left   => W_Tag,
                            Right  =>
                              +New_Tag_Access
                                 (Domain => EW_Term,
                                  Name   =>
                                    (if Params.Ref_Allowed
                                     then
                                       New_Deref
                                         (Right => B.Main.B_Name,
                                          Typ   => EW_Abstract (D_Ty))
                                     else +B.Main.B_Name),
                                  Ty     => D_Ty)));

               when DRecord =>
                  pragma Assert (B.Tag.Present);
                  Pred :=
                    New_And_Pred
                      (Left  => Pred,
                       Right =>
                         New_Comparison
                           (Symbol => Why_Eq,
                            Left   => W_Tag,
                            Right  => +B.Tag.Id));

               when others  =>
                  raise Program_Error;
            end case;
         end if;
      end loop;
      return Pred;
   end Compute_Guard_For_Dispatch;

   ---------------------------
   -- Compute_Guard_Formula --
   ---------------------------

   function Compute_Guard_Formula
     (Binders : Item_Array; Params : Transformation_Params) return W_Pred_Id
   is
      All_Global_Inv : constant Boolean :=
        Include_All_Global_Invariants_For_Subp (Current_Subp);
      Pred           : W_Pred_Id := True_Pred;

   begin
      --  Add to guard the dynamic property of logic parameters.

      for B of Binders loop
         declare
            Ada_Node : constant Node_Id := Get_Ada_Node_From_Item (B);
            Expr     : constant W_Term_Id :=
              Reconstruct_Item (B, Params.Ref_Allowed);
            Ty_Node  : constant Entity_Id :=
              (if Present (Ada_Node)
                 and then not Specialized_Call_Params.Contains (Ada_Node)
               then (if Is_Type (Ada_Node) then Ada_Node else Etype (Ada_Node))
               else Empty);
            --  Do not generate guards for specialized formals
            Dyn_Prop : constant W_Pred_Id :=
              (if Present (Ty_Node)
               then
                 Compute_Dynamic_Inv_And_Initialization
                   (Expr           => +Expr,
                    Ty             => Ty_Node,
                    Params         => Params,
                    Valid          =>
                      Get_Valid_Id_From_Item (B, Params.Ref_Allowed),
                    Only_Var       => False_Term,
                    All_Global_Inv =>
                      All_Global_Inv
                      or else Ekind (Ada_Node) not in Formal_Kind
                      or else Enclosing_Unit (Ada_Node) /= Current_Subp)
               --  For parameters of Current_Subp, type invariants might be
               --  broken.
               else True_Pred);
         begin
            if No (Ada_Node) then
               declare
                  K    : constant Item_Enum := B.Kind;
                  Name : constant W_Identifier_Id := B.Main.B_Name;
                  Ty   : constant W_Type_Id := Get_Typ (Name);
               begin

                  --  If there is no Ada_Node associated to the binder then
                  --  it must be either the unit binder or a binder for
                  --  a variable referenced for effects only.

                  pragma
                    Assert
                      (K = Regular
                         and then Ty
                                  in M_Main.Type_Of_Heap
                                   | EW_Private_Type
                                   | EW_Unit_Type);
               end;
            end if;

            Pred :=
              +New_And_Then_Expr
                 (Domain => EW_Pred, Left => +Pred, Right => +Dyn_Prop);
         end;
      end loop;
      return Pred;
   end Compute_Guard_Formula;

   ---------------------------------------------
   -- Compute_Moved_Property_For_Deep_Outputs --
   ---------------------------------------------

   function Compute_Moved_Property_For_Deep_Outputs
     (E : Entity_Id; Params : Transformation_Params) return W_Prog_Id
   is
      Assume : W_Prog_Id := +Void;
   begin
      if (Ekind (E) = E_Function
          and then not Is_Function_With_Side_Effects (E))
        or else Ekind (E) in E_Package | E_Task_Type
      then
         return +Void;
      end if;

      declare
         Outputs : constant Entity_Sets.Set :=
           Compute_Outputs_With_Allocated_Parts (E);
      begin
         for Obj of Outputs loop
            Append
              (Assume,
               New_Assume_Statement
                 (Pred =>
                    Compute_Is_Moved_Or_Reclaimed
                      (Expr =>
                         +Transform_Identifier
                            (Params => Params,
                             Expr   => Obj,
                             Ent    => Obj,
                             Domain => EW_Term),
                       Tree => +New_Move_Tree_Access_For_Identitier (Obj),
                       Ty   => Expected_Type_For_Move_Tree (Obj))));
         end loop;
      end;

      return Assume;
   end Compute_Moved_Property_For_Deep_Outputs;

   ------------------------------------------
   -- Compute_Outputs_With_Allocated_Parts --
   ------------------------------------------

   function Compute_Outputs_With_Allocated_Parts
     (E : Callable_Kind_Id) return Entity_Sets.Set
   is
      Outputs : Entity_Sets.Set;
   begin
      declare
         Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
         Write_Ids : Flow_Types.Flow_Id_Sets.Set;
      begin
         Flow_Utility.Get_Proof_Globals
           (Subprogram      => E,
            Reads           => Read_Ids,
            Writes          => Write_Ids,
            Erase_Constants => True);

         for Write_Id of Write_Ids loop
            case Write_Id.Kind is
               when Direct_Mapping =>
                  declare
                     Entity : constant Entity_Id :=
                       Get_Direct_Mapping_Id (Write_Id);
                     Typ    : constant Entity_Id := Retysp (Etype (Entity));

                  begin
                     if not Is_Concurrent_Type (Entity)
                       and then not Read_Ids.Contains (Write_Id)
                       and then Contains_Allocated_Parts (Typ)
                       and then not Is_Anonymous_Access_Type (Typ)
                     then
                        Outputs.Insert (Entity);
                     end if;
                  end;

               when Magic_String   =>
                  null;

               when others         =>
                  raise Program_Error;
            end case;
         end loop;
      end;

      declare
         Formal : Entity_Id := First_Formal (E);
      begin
         while Present (Formal) loop
            declare
               Typ : constant Entity_Id := Retysp (Etype (Formal));
            begin
               if Contains_Allocated_Parts (Typ)
                 and then not Is_Anonymous_Access_Type (Typ)
                 and then Ekind (Formal) = E_Out_Parameter
               then
                  Outputs.Insert (Formal);
               end if;

               Next_Formal (Formal);
            end;
         end loop;
      end;

      return Outputs;
   end Compute_Outputs_With_Allocated_Parts;

   ----------------------------------------
   -- Compute_Program_Exit_Postcondition --
   ----------------------------------------

   function Compute_Program_Exit_Postcondition
     (Params : Transformation_Params; E : Callable_Kind_Id) return W_Pred_Id
   is
      Outputs   : constant Flow_Id_Sets.Set :=
        Get_Outputs_From_Program_Exit (E, E);
      Dyn_Props : W_Pred_Array (1 .. Natural (Outputs.Length));
      Top       : Natural := 0;

   begin
      --  First compute the dynamic invariant (and potentially type invariant)
      --  of globals mentioned in the Program_Exit post of E.

      for F of Outputs loop
         pragma Assert (F.Kind in Direct_Mapping | Magic_String);

         --  Magic_String are global state with no attached entities. As
         --  such state is translated as private in Why3, we do not need
         --  to consider any dynamic invariant or type invariant for it.

         if F.Kind = Direct_Mapping then

            --  Concurrent self should not occur here
            pragma Assert (Is_Object (Get_Direct_Mapping_Id (F)));

            declare
               Binder   : constant Item_Type :=
                 Ada_Ent_To_Why.Element
                   (Symbol_Table, Get_Direct_Mapping_Id (F));
               Ada_Type : constant Entity_Id :=
                 Get_Ada_Type_From_Item (Binder);
               Expr     : constant W_Term_Id :=
                 Reconstruct_Item (Binder, Ref_Allowed => Params.Ref_Allowed);
            begin
               Top := Top + 1;
               Dyn_Props (Top) :=
                 New_And_Pred
                   (Left  =>
                      Compute_Dynamic_Inv_And_Initialization
                        (Expr   => Expr,
                         Ty     => Ada_Type,
                         Params => Params,
                         Valid  =>
                           Get_Valid_Id_From_Item
                             (Binder, Params.Ref_Allowed)),
                    Right =>
                      Compute_Type_Invariant
                        (Expr   => Expr,
                         Ty     => Ada_Type,
                         Params => Params,
                         Kind   => For_Check,
                         Scop   => E));
            end;
         end if;
      end loop;

      --  Also include the program exit postcondition itself if any

      return
        New_And_Pred
          (Left  => New_And_Pred (Dyn_Props (1 .. Top)),
           Right =>
             (if Present (Get_Program_Exit (E))
              then Transform_Pred (Get_Program_Exit (E), Params)
              else True_Pred));
   end Compute_Program_Exit_Postcondition;

   ------------------------------------
   -- Compute_Subprogram_Parameters  --
   ------------------------------------

   function Compute_Subprogram_Parameters
     (E          : Callable_Kind_Id;
      Domain     : EW_Domain;
      More_Reads : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return Item_Array
   is
      Raw_Binders : constant Item_Array := Compute_Raw_Binders (E);
   begin
      return
        (if Domain = EW_Prog
         then Raw_Binders
         else Add_Logic_Binders (E, Raw_Binders, More_Reads));
   end Compute_Subprogram_Parameters;

   --------------------------------------------
   -- Compute_Type_Invariants_For_Subprogram --
   --------------------------------------------

   function Compute_Type_Invariants_For_Subprogram
     (E           : Entity_Id;
      Params      : Transformation_Params;
      For_Input   : Boolean;
      Exceptional : Boolean := False) return W_Pred_Id
   is
      Res : W_Pred_Id := True_Pred;

      procedure Add_To_Res (Dummy : Node_Id; Inv : W_Pred_Id);
      --  Conjunct Inv to Res

      ----------------
      -- Add_To_Res --
      ----------------

      procedure Add_To_Res (Dummy : Node_Id; Inv : W_Pred_Id) is
      begin
         Res := New_And_Pred (Left => Res, Right => Inv);
      end Add_To_Res;

      procedure Compute_Type_Invariants is new
        Process_Type_Invariants_For_Subprogram (Add_To_Res);
   begin
      Compute_Type_Invariants (E, Params, For_Input, Exceptional, Scop => E);

      return Res;
   end Compute_Type_Invariants_For_Subprogram;

   -----------------------
   -- Add_Logic_Binders --
   -----------------------

   function Add_Logic_Binders
     (E           : Entity_Id;
      Raw_Binders : Item_Array;
      More_Reads  : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return Item_Array
   is
      Effect_Binders : Item_Array :=
        Compute_Binders_For_Effects (E, More_Reads);
   begin
      Localize_Binders (Effect_Binders);
      return Raw_Binders & Effect_Binders;
   end Add_Logic_Binders;

   ---------------------------------
   -- Compute_Binders_For_Effects --
   ---------------------------------

   function Compute_Binders_For_Effects
     (E          : Callable_Kind_Id;
      More_Reads : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return Item_Array
   is
      Read_Ids  : Flow_Id_Sets.Set;
      Write_Ids : Flow_Id_Sets.Set;

   begin
      --  Collect global variables potentially read and written

      Flow_Utility.Get_Proof_Globals
        (Subprogram      => E,
         Reads           => Read_Ids,
         Writes          => Write_Ids,
         Erase_Constants => True);

      Read_Ids.Union (More_Reads);

      --  Do not include binder for self reference as it is already included
      --  in binders for parameters.

      return
        Get_Binders_From_Variables
          (Read_Ids.Union (Write_Ids), Ignore_Self => True);
   end Compute_Binders_For_Effects;

   -------------------------
   -- Compute_Raw_Binders --
   -------------------------

   function Compute_Raw_Binders (E : Entity_Id) return Item_Array is
      Binder_Len : constant Natural :=
        Number_Formals (E) + (if Need_Self_Binder (E) then 1 else 0);
      Result     : Item_Array (1 .. Binder_Len);
      Formal     : Entity_Id;
      Count      : Positive;

   begin
      Formal := First_Formal (E);
      Count := 1;

      if Need_Self_Binder (E) then
         declare
            Prot : constant Entity_Id := Containing_Protected_Type (E);
         begin
            Result (1) :=
              (Concurrent_Self,
               Local    => True,
               Init     => <>,
               Is_Moved => <>,
               Valid    => <>,
               Main     =>
                 Concurrent_Self_Binder
                   (Prot, Mutable => Ekind (E) /= E_Function));
            Count := 2;
         end;
      end if;

      while Present (Formal) loop

         --  Specialized parameters are hardcoded. No actual value is provided,
         --  we use a parameter of type unit instead. We still provide an
         --  Ada_Node for it so it will be stored in the Symbol_Table. This
         --  works as a sanity checking. If the formal is referenced, which
         --  should never happen, the generated Why3 code will be ill-typed.

         if Specialized_Call_Params.Contains (Formal) then
            Result (Count) :=
              (Regular,
               Local    => True,
               Init     => <>,
               Is_Moved => <>,
               Valid    => <>,
               Main     => Unit_Param (Short_Name (Formal), Formal));
         else
            Result (Count) :=
              Mk_Item_Of_Entity
                (E => Formal, Local => True, In_Fun_Decl => True);
         end if;
         Next_Formal (Formal);
         Count := Count + 1;
      end loop;

      pragma Assert (Count = Binder_Len + 1);

      return Result;
   end Compute_Raw_Binders;

   -----------------------------
   -- Compute_Cases_Guard_Map --
   -----------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  Pragma/aspect Exit_Cases (Guard1 => Exit_Kind1,
   --                            Guard2 => Exit_Kind2,
   --                               ...
   --                            GuardN => Exit_KindN
   --                           [,OTHERS => Exit_KindN+1]);

   --  This helper subprogram stores in Guard_Map a map from guard expressions
   --  to temporary Why names. The temporary Why name for the OTHERS case
   --  is associated with the aggregate itsle. It will be used to generate
   --  bindings such as:

   --    let guard1 = ... in
   --    let guard2 = ... in
   --    ...
   --    let guardN = ... in
   --    let guardOTHERS = not (guard1 or guard2 ... or guardN) in

   procedure Compute_Cases_Guard_Map
     (Aggr : Node_Id; Guard_Map : out Ada_To_Why_Ident.Map)
   is
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

   begin
      --  Process individual contract cases

      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         declare
            --  Temporary Why name for the current guard
            Guard_Ident : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => EW_Bool_Type);

         begin
            Case_Guard := First (Choice_List (Contract_Case));

            --  The OTHERS choice is associated directly with Aggr

            if Nkind (Case_Guard) = N_Others_Choice then
               Guard_Map.Include (Aggr, Guard_Ident);

            --  Regular contract case

            else
               Guard_Map.Include (Case_Guard, Guard_Ident);
            end if;

            Next (Contract_Case);
         end;
      end loop;
   end Compute_Cases_Guard_Map;

   --------------------------------
   -- Compute_Cases_Entry_Checks --
   --------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  Pragma/aspect Exit_Cases (Guard1 => Exit_Kind1,
   --                            Guard2 => Exit_Kind2,
   --                               ...
   --                            GuardN => Exit_KindN
   --                           [,OTHERS => Exit_KindN+1]);

   --  leads to the generation of checks on subprogram entry. In a context
   --  where the precondition is known to hold, it is checked that no
   --  evaluation of a guard can lead to a run-time error, that no more than
   --  one guard evaluates to True (only if there are at least two non-OTHER
   --  guards), and that at least one guard evaluates to True (only in the case
   --  there is no OTHERS and if Check_Complete is True).

   --  Check that cases are disjoint only if there are at least two non-OTHER
   --  guards:

   --    assert ((if guard1 = True then 1 else 0) +
   --            (if guard2 = True then 1 else 0) +
   --            ...
   --            (if guardN = True then 1 else 0) <= 1)

   --  Check that cases are complete only if there is no OTHERS and if
   --  Check_Complete is True:

   --    assert ((if guard1 = True then 1 else 0) +
   --            (if guard2 = True then 1 else 0) +
   --            ...
   --            (if guardN = True then 1 else 0) >= 1)

   function Compute_Cases_Entry_Checks
     (Aggr           : Node_Id;
      Guard_Map      : Ada_To_Why_Ident.Map;
      Check_Complete : Boolean) return W_Prog_Id
   is
      function Is_Pragma (N : Node_Id) return Boolean
      is (Nkind (N) = N_Pragma);

      function Enclosing_Pragma is new First_Parent_With_Property (Is_Pragma);

      Prag          : constant Node_Id := Enclosing_Pragma (Aggr);
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

      Has_Others : Boolean := False;
      --  Set to True if there is an OTHERS guard

      Count : W_Expr_Id := New_Integer_Constant (Value => Uint_0);
      --  Count of the guards enabled

      Result : W_Prog_Id := +Void;
      --  Why program for these checks

      --  Start of processing for Compute_Contract_Cases_Entry_Checks

   begin
      --  Process individual contract cases

      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choice_List (Contract_Case));

         --  The OTHERS choice requires special processing

         if Nkind (Case_Guard) = N_Others_Choice then
            Has_Others := True;

         --  Regular contract case

         else
            declare
               Guard_Ident : constant W_Identifier_Id :=
                 Guard_Map.Element (Case_Guard);
               --  Temporary Why name for the current guard

               --  Whether the current guard is enabled
               Enabled : constant W_Expr_Id :=
                 New_Conditional
                   (Ada_Node  => Case_Guard,
                    Domain    => EW_Term,
                    Condition =>
                      New_Call
                        (Domain => EW_Pred,
                         Name   => Why_Eq,
                         Args   =>
                           (1 => +Guard_Ident,
                            2 =>
                              New_Literal
                                (Domain => EW_Term, Value => EW_True)),
                         Typ    => EW_Bool_Type),
                    Then_Part => New_Integer_Constant (Value => Uint_1),
                    Else_Part => New_Integer_Constant (Value => Uint_0));
            begin
               Count :=
                 New_Call
                   (Ada_Node => Case_Guard,
                    Domain   => EW_Term,
                    Name     => Int_Infix_Add,
                    Args     => (1 => Count, 2 => Enabled),
                    Typ      => EW_Int_Type);
            end;
         end if;

         Next (Contract_Case);
      end loop;

      --  A check that contract cases are disjoint is generated only when there
      --  are at least two guards, and none is an OTHER guard.

      if List_Length (Component_Associations (Aggr)) >= 2
        and then (if List_Length (Component_Associations (Aggr)) = 2
                  then not Has_Others)
      then
         Append
           (Result,
            New_Assert
              (Pred        =>
                 New_VC_Pred
                   (Prag,
                    New_Call
                      (Name => Int_Infix_Le,
                       Typ  => EW_Bool_Type,
                       Args =>
                         (+Count, New_Integer_Constant (Value => Uint_1))),
                    VC_Disjoint_Cases),
               Assert_Kind => EW_Check));
      end if;

      --  A check that contract cases are complete is generated only when there
      --  is no OTHER guard and if Check_Complete is True.

      if Check_Complete and then not Has_Others then
         Append
           (Result,
            New_Assert
              (Pred        =>
                 New_VC_Pred
                   (Prag,
                    New_Call
                      (Typ  => EW_Bool_Type,
                       Name => Int_Infix_Ge,
                       Args =>
                         (+Count, New_Integer_Constant (Value => Uint_1))),
                    VC_Complete_Cases),
               Assert_Kind => EW_Check));
      end if;

      return New_Ignore (Prog => Result);
   end Compute_Cases_Entry_Checks;

   -------------------------------
   -- Compute_Cases_Others_Expr --
   -------------------------------

   function Compute_Cases_Others_Expr
     (Aggr : Node_Id; Guard_Map : Ada_To_Why_Ident.Map) return W_Term_Id
   is
      Result        : W_Term_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

   begin
      Result := False_Term;

      --  Process individual contract cases

      Contract_Case := Last (Component_Associations (Aggr));
      Case_Guard := First (Choice_List (Contract_Case));

      if Nkind (Case_Guard) = N_Others_Choice then
         Prev (Contract_Case);
      else
         return Why_Empty;
      end if;

      while Present (Contract_Case) loop
         Case_Guard := First (Choice_List (Contract_Case));
         declare
            Guard_Ident : constant W_Identifier_Id :=
              Guard_Map.Element (Case_Guard);

         begin
            Result := New_Or_Term (Left => +Guard_Ident, Right => Result);
         end;

         Prev (Contract_Case);
      end loop;

      return
        New_Conditional
          (Condition => Result,
           Then_Part => False_Term,
           Else_Part => True_Term);
   end Compute_Cases_Others_Expr;

   ----------------------------------------
   -- Compute_Contract_Cases_Exit_Checks --
   ----------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  leads to the generation of checks on subprogram exit. It is checked that
   --  the consequence for the guard that was True on entry also evaluates to
   --  True, without run-time errors.

   --    assert (if guard1 then consequence1);
   --    assert (if guard2 then consequence2);
   --    ...
   --    assert (if guardN then consequenceN);
   --    assert (if not (guard1 or guard2 ... or guardN) then consequenceN+1);

   function Compute_Contract_Cases_Exit_Checks
     (Params    : Transformation_Params;
      E         : Entity_Id;
      Guard_Map : Ada_To_Why_Ident.Map) return W_Prog_Id
   is
      CC_List       : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Contract_Cases);
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;
      Warn_Others   : Boolean := Params.Warn_On_Dead;

      function Do_One_Contract_Case
        (Contract_Case : Node_Id; Enabled : W_Expr_Id) return W_Prog_Id;
      --  Returns the Why program checking absence of run-time errors and
      --  function verification of the given Contract_Case. Enabled is a
      --  boolean term. Set Warn_Others to False if the current case is
      --  statically disabled for True.

      function Do_One_Contract_Case
        (Contract_Case : Node_Id; Enabled : W_Expr_Id) return W_Prog_Id
      is
         Consequence : constant Node_Id := Expression (Contract_Case);

         --  Enabled must be converted to a predicate to be used as the
         --  condition in an if-expr inside a predicate.
         Enabled_Pred : constant W_Pred_Id :=
           New_Call
             (Name => Why_Eq,
              Typ  => EW_Bool_Type,
              Args =>
                (+Enabled, New_Literal (Domain => EW_Term, Value => EW_True)));

         WP_Consequence : W_Prog_Id;

      begin
         --  Possibly warn on an unreachable case. No warning is emitted if
         --  the case is statically disabled.

         declare
            Case_Guard : constant Node_Id :=
              First (Choice_List (Contract_Case));
            Do_Warn    : Boolean;

         begin
            if Nkind (Case_Guard) = N_Others_Choice then
               Do_Warn := Warn_Others;
            else
               Do_Warn :=
                 Params.Warn_On_Dead
                 and then not Exp_Util.Is_Statically_Disabled
                                (Case_Guard, False, Include_Valid => True);
               Warn_Others :=
                 Warn_Others
                 and then not Exp_Util.Is_Statically_Disabled
                                (Case_Guard, True, Include_Valid => True);
            end if;

            WP_Consequence :=
              Transform_Prog
                (Consequence, (Params with delta Warn_On_Dead => Do_Warn));
            WP_Consequence :=
              Warn_On_Dead_Branch
                (Consequence, WP_Consequence, Params.Phase, Do_Warn);
         end;

         return
           Sequence
             (New_Ignore
                (Prog =>
                   New_Conditional
                     (Ada_Node  => Contract_Case,
                      Condition => +Enabled,
                      Then_Part => WP_Consequence,
                      Else_Part =>
                        Insert_Simple_Conversion
                          (Expr => True_Prog,
                           To   => Type_Of_Node (Consequence)))),
              New_Assert
                (Pred        =>
                   New_VC_Pred
                     (Contract_Case,
                      New_Conditional
                        (Ada_Node  => Contract_Case,
                         Condition => Enabled_Pred,
                         Then_Part => Transform_Pred (Consequence, Params)),
                      VC_Contract_Case),
                 Assert_Kind => EW_Assert));
      end Do_One_Contract_Case;

      Result : W_Prog_Id := +Void;

      --  Start of processing for Compute_Contract_Cases_Exit_Checks

   begin
      for Aggr of CC_List loop
         --  Process individual contract cases

         Contract_Case := First (Component_Associations (Aggr));
         while Present (Contract_Case) loop
            Case_Guard := First (Choice_List (Contract_Case));

            declare
               --  Temporary Why name for the current guard
               Guard_Ident : constant W_Identifier_Id :=
                 (if Nkind (Case_Guard) = N_Others_Choice
                  then Guard_Map.Element (Aggr)
                  else Guard_Map.Element (Case_Guard));

               --  Whether the current guard is enabled
               Enabled : constant W_Expr_Id := +Guard_Ident;

            begin
               Append (Result, Do_One_Contract_Case (Contract_Case, Enabled));
            end;

            Next (Contract_Case);
         end loop;
      end loop;

      return Result;
   end Compute_Contract_Cases_Exit_Checks;

   ------------------------------------------
   -- Compute_Contract_Cases_Postcondition --
   ------------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  leads to the generation of a postcondition for the corresponding Why
   --  program function.

   --    if guard1 then consequence1
   --    else if guard2 then consequence2
   --    ...
   --    else if guardN then consequenceN
   --    [else consequenceN+1]

   function Compute_Contract_Cases_Postcondition
     (Params : Transformation_Params; E : Callable_Kind_Id) return W_Pred_Id
   is
      CC_List       : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Contract_Cases);
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;
      Consequence   : Node_Id;

      Result : W_Pred_Array (1 .. Natural (CC_List.Length));
      Pos    : Natural := 0;

      --  Start of processing for Compute_Contract_Cases_Postcondition

   begin
      for Aggr of CC_List loop
         Pos := Pos + 1;
         Result (Pos) := True_Pred;

         --  Process individual contract cases in reverse order, to create the
         --  proper if-elsif Why predicate.

         Contract_Case := Last (Component_Associations (Aggr));
         while Present (Contract_Case) loop
            Case_Guard := First (Choice_List (Contract_Case));
            Consequence := Expression (Contract_Case);

            --  The "others" choice requires special processing

            if Nkind (Case_Guard) = N_Others_Choice then
               Result (Pos) := Transform_Pred (Consequence, Params);

            --  Regular contract case

            else
               declare
                  --  Whether the current guard is enabled in the pre-state

                  Enabled : constant W_Expr_Id :=
                    Transform_Attribute_Old (Case_Guard, EW_Pred, Params);
               begin
                  Result (Pos) :=
                    New_Conditional
                      (Condition => +Enabled,
                       Then_Part => Transform_Pred (Consequence, Params),
                       Else_Part => Result (Pos));
               end;
            end if;

            Prev (Contract_Case);
         end loop;
      end loop;

      return New_And_Pred (Result);
   end Compute_Contract_Cases_Postcondition;

   ---------------------------------------------
   -- Compute_Exceptional_Cases_Postcondition --
   ---------------------------------------------

   function Compute_Exceptional_Cases_Postcondition
     (Params : Transformation_Params;
      E      : Callable_Kind_Id;
      Exc_Id : W_Identifier_Id) return W_Pred_Id
   is
      Prag                 : constant Node_Id :=
        Get_Pragma (E, Pragma_Exceptional_Cases);
      Dynamic_Prop_Effects : constant W_Pred_Id :=
        New_And_Pred
          ((1 =>
              Compute_Dynamic_Property_For_Effects
                (E, Params, Exceptional => True),
            2 =>
              Compute_Type_Invariants_For_Subprogram
                (E, Params, False, Exceptional => True),
            3 => Preservation_Of_Access_Parameters (E, Params)));
      --  Dynamic invariant and type invariant for outputs of the
      --  procedure, as well as preservation of discriminants and
      --  bounds of access parameters.

   begin
      --  If there is no exceptional cases, then it should be generated from
      --  the set of expected exceptions. All expected exceptions are allowed
      --  in any context.

      if No (Prag) then
         declare
            Exc_Set : constant Exception_Sets.Set :=
              Get_Exceptions_For_Subp (E);
            All_But : Boolean;
            Excs    : Node_Sets.Set;
            Cond    : W_Pred_Id := False_Pred;

         begin
            Exc_Set.Disclose (All_But, Excs);

            for E of Excs loop
               Cond :=
                 New_Or_Pred
                   (Cond, New_Comparison (Why_Eq, +Exc_Id, +To_Why_Id (E)));
            end loop;

            if All_But then
               Cond := New_Not (Right => Cond);
            end if;

            return New_And_Pred (Left => Dynamic_Prop_Effects, Right => Cond);
         end;
      end if;

      declare
         Aggr             : constant Node_Id :=
           Expression (First (Pragma_Argument_Associations (Prag)));
         Assocs           : constant List_Id := Component_Associations (Aggr);
         Others_Present   : constant Boolean :=
           Nkind (First (Choice_List (Last (Assocs)))) = N_Others_Choice;
         Nb_Cases         : constant Integer := Natural (List_Length (Assocs));
         Elsif_Parts      :
           W_Pred_Array (2 .. Nb_Cases - (if Others_Present then 1 else 0));
         Else_Part        : W_Pred_Id;
         Exceptional_Case : Node_Id := First (Assocs);

      begin
         --  Get the case where there is only the others choice out of the way

         if Nb_Cases = 1 and then Others_Present then
            return
              New_And_Pred
                (Left  => Dynamic_Prop_Effects,
                 Right =>
                   Transform_Pred (Expression (Exceptional_Case), Params));
         end if;

         --  Fill the Elsif_Parts if any

         Next (Exceptional_Case);
         if Elsif_Parts'Length > 0 then
            for Num in Elsif_Parts'Range loop
               Elsif_Parts (Num) :=
                 New_Elsif
                   (Condition =>
                      +Compute_Guard_For_Exceptions
                         (Choice_List (Exceptional_Case), Exc_Id, EW_Pred),
                    Then_Part =>
                      Transform_Pred (Expression (Exceptional_Case), Params));
               Next (Exceptional_Case);
            end loop;
         end if;

         --  Fill the Else_Part if any

         if Others_Present then
            Else_Part :=
              Transform_Pred (Expression (Exceptional_Case), Params);
         else
            Else_Part := False_Pred;
         end if;

         --  Reconstruct the conditional

         Exceptional_Case := First (Assocs);

         return
           New_And_Pred
             (Left  => Dynamic_Prop_Effects,
              Right =>
                New_Conditional
                  (Ada_Node    => Prag,
                   Condition   =>
                     +Compute_Guard_For_Exceptions
                        (Choice_List (Exceptional_Case), Exc_Id, EW_Pred),
                   Then_Part   =>
                     Transform_Pred (Expression (Exceptional_Case), Params),
                   Elsif_Parts => Elsif_Parts,
                   Else_Part   => Else_Part));
      end;
   end Compute_Exceptional_Cases_Postcondition;

   ------------------------------------------------
   -- Compute_Exit_Cases_Exceptional_Exit_Checks --
   ------------------------------------------------

   --  Pragma/aspect Exit_Cases (Guard1 => Exit_Kind1,
   --                            Guard2 => Exit_Kind2,
   --                               ...
   --                            GuardN => Exit_KindN
   --                          [,OTHERS => Exit_KindN+1]);

   --  leads to the generation of checks on exceptional exit. It is checked
   --  that the guards that are not associated to Exception_Raised evaluates to
   --  False and that the exception raised is the expected one if a guard
   --  associated to Exception_Raised evaluates to True.

   --  pragma Assert (not guardi); --  if Exit_Kindi is not Exception_Raised
   --  pragma Assert
   --    (guardi -> exc_id = e_i); --  if Exit_Kindi is Exception_Raised => Ei

   function Compute_Exit_Cases_Exceptional_Exit_Checks
     (E         : Entity_Id;
      Guard_Map : Ada_To_Why_Ident.Map;
      Exc_Id    : W_Identifier_Id) return W_Prog_Id
   is
      Prag   : constant Node_Id := Get_Pragma (E, Pragma_Exit_Cases);
      Result : W_Prog_Id := +Void;

   begin
      --  If no Exit_Cases on this subprogram, return

      if No (Prag) then
         return Result;
      end if;

      --  Process individual exit cases

      declare
         Aggr       : constant Node_Id :=
           Expression (First (Pragma_Argument_Associations (Prag)));
         Exit_Case  : Node_Id := First (Component_Associations (Aggr));
         Check_Info : Check_Info_Type := New_Check_Info;

      begin
         Check_Info.Continuation.Append
           (Continuation_Type'
              (E,
               To_Unbounded_String
                 ("on exceptional exit from " & Source_Name (E))));

         while Present (Exit_Case) loop
            declare
               Case_Guard  : constant Node_Id :=
                 First (Choice_List (Exit_Case));
               Exit_Kind   : constant Node_Id := Expression (Exit_Case);
               --  Temporary Why name for the current guard
               Guard_Ident : constant W_Identifier_Id :=
                 (if Nkind (Case_Guard) = N_Others_Choice
                  then Guard_Map.Element (Aggr)
                  else Guard_Map.Element (Case_Guard));
            begin
               case Nkind (Exit_Kind) is
                  when N_Identifier =>
                     case Chars (Exit_Kind) is
                        when Name_Exception_Raised                  =>
                           null;

                        when Name_Normal_Return | Name_Program_Exit =>
                           Append
                             (Result,
                              New_Ignore
                                (Prog =>
                                   New_Located_Assert
                                     (Ada_Node   => Exit_Kind,
                                      Pred       =>
                                        New_Not (Right => +Guard_Ident),
                                      Reason     => VC_Exit_Case,
                                      Kind       => EW_Assert,
                                      Check_Info => Check_Info)));

                        when others                                 =>
                           raise Program_Error;
                     end case;

                  when N_Aggregate  =>
                     Append
                       (Result,
                        New_Ignore
                          (Prog =>
                             New_Located_Assert
                               (Ada_Node   => Exit_Kind,
                                Pred       =>
                                  New_Conditional
                                    (Condition => +Guard_Ident,
                                     Then_Part =>
                                       New_Comparison
                                         (Symbol => Why_Eq,
                                          Left   => +Exc_Id,
                                          Right  =>
                                            +To_Why_Id
                                               (Entity
                                                  (Expression
                                                     (First
                                                        (Component_Associations
                                                           (Exit_Kind))))))),
                                Reason     => VC_Exit_Case,
                                Kind       => EW_Assert,
                                Check_Info => Check_Info)));

                  when others       =>
                     raise Program_Error;
               end case;
            end;
            Next (Exit_Case);
         end loop;
      end;

      return Result;
   end Compute_Exit_Cases_Exceptional_Exit_Checks;

   -----------------------------------------
   -- Compute_Exit_Cases_Exceptional_Post --
   -----------------------------------------

   --  Pragma/aspect Exit_Cases (Guard1 => Exit_Kind1,
   --                            Guard2 => Exit_Kind2,
   --                               ...
   --                            GuardN => Exit_KindN
   --                          [,OTHERS => Exit_KindN+1]);

   --  leads to the generation of an exceptional postcondition for the
   --  corresponding Why program function.

   --  We generate:
   --
   --  if old guard1 then
   --    false                     --  if Exit_Kindi is not Exception_Raised
   --    exc_id = e_i              --  if Exit_Kindi is Exception_Raised => Ei
   --    true                      --  if Exit_Kindi is Exception_Raised
   --
   --  elsif ...

   function Compute_Exit_Cases_Exceptional_Post
     (Params : Transformation_Params; E : Entity_Id; Exc_Id : W_Identifier_Id)
      return W_Pred_Id
   is
      Prag : constant Node_Id := Get_Pragma (E, Pragma_Exit_Cases);

   begin
      --  If no Exit_Cases on this subprogram, return

      if No (Prag) then
         return True_Pred;
      end if;

      --  Process individual exit cases in reverse order, to create the proper
      --  if-elsif Why predicate.

      declare
         Aggr      : constant Node_Id :=
           Expression (First (Pragma_Argument_Associations (Prag)));
         Assocs    : constant List_Id := Component_Associations (Aggr);
         Exit_Case : Node_Id := Last (Assocs);
         Result    : W_Pred_Id := True_Pred;

      begin
         while Present (Exit_Case) loop
            declare
               Case_Guard : constant Node_Id :=
                 First (Choice_List (Exit_Case));
               W_Conseq   : W_Pred_Id;
               Exit_Kind  : constant Node_Id := Expression (Exit_Case);
            begin

               case Nkind (Exit_Kind) is
                  when N_Identifier =>
                     W_Conseq :=
                       (if Chars (Exit_Kind) = Name_Exception_Raised
                        then True_Pred
                        else False_Pred);

                  when N_Aggregate  =>
                     W_Conseq :=
                       New_Comparison
                         (Symbol => Why_Eq,
                          Left   => +Exc_Id,
                          Right  =>
                            +To_Why_Id
                               (Entity
                                  (Expression
                                     (First
                                        (Component_Associations
                                           (Exit_Kind))))));

                  when others       =>
                     raise Program_Error;
               end case;

               --  The "others" choice requires special processing

               if Nkind (Case_Guard) = N_Others_Choice then
                  Result := W_Conseq;

               --  Regular contract case

               else
                  declare
                     --  Whether the current guard is enabled in the pre-state

                     Enabled : constant W_Expr_Id :=
                       Transform_Attribute_Old (Case_Guard, EW_Pred, Params);
                  begin
                     Result :=
                       New_Conditional
                         (Condition => +Enabled,
                          Then_Part => W_Conseq,
                          Else_Part => Result);
                  end;
               end if;
            end;
            Prev (Exit_Case);
         end loop;

         return Result;
      end;
   end Compute_Exit_Cases_Exceptional_Post;

   --------------------------------------
   -- Compute_Exit_Cases_Simple_Checks --
   --------------------------------------

   --  Pragma/aspect Exit_Cases (Guard1 => Exit_Kind1,
   --                            Guard2 => Exit_Kind2,
   --                               ...
   --                            GuardN => Exit_KindN
   --                          [,OTHERS => Exit_KindN+1]);

   --  leads to the generation of checks on exit kind Name. It is checked that
   --  the guards that are not associated to Name evaluates to False.

   --  pragma Assert (not guardi); --  if Exit_Kindi is not Name

   function Compute_Exit_Cases_Simple_Checks
     (E : Entity_Id; Name : Name_Id; Guard_Map : Ada_To_Why_Ident.Map)
      return W_Prog_Id
   is
      Prag   : constant Node_Id := Get_Pragma (E, Pragma_Exit_Cases);
      Result : W_Prog_Id := +Void;

   begin
      --  If no Exit_Cases on this subprogram, return

      if No (Prag) then
         return Result;
      end if;

      --  Process individual exit cases

      declare
         Aggr       : constant Node_Id :=
           Expression (First (Pragma_Argument_Associations (Prag)));
         Exit_Case  : Node_Id := First (Component_Associations (Aggr));
         Check_Info : Check_Info_Type := New_Check_Info;
         Loc        : constant String :=
           (case Name is
              when Name_Normal_Return => "on normal return",
              when Name_Program_Exit  => "on program exit",
              when others             => raise Program_Error);

      begin
         Check_Info.Continuation.Append
           (Continuation_Type'
              (E, To_Unbounded_String (Loc & " from " & Source_Name (E))));

         while Present (Exit_Case) loop
            declare
               Case_Guard  : constant Node_Id :=
                 First (Choice_List (Exit_Case));
               Exit_Kind   : constant Node_Id := Expression (Exit_Case);
               --  Temporary Why name for the current guard
               Guard_Ident : constant W_Identifier_Id :=
                 (if Nkind (Case_Guard) = N_Others_Choice
                  then Guard_Map.Element (Aggr)
                  else Guard_Map.Element (Case_Guard));
               Exclude     : Boolean;
            begin
               case Nkind (Exit_Kind) is
                  when N_Identifier =>
                     Exclude := Chars (Exit_Kind) /= Name;

                  when N_Aggregate  =>
                     Exclude := True;

                  when others       =>
                     raise Program_Error;
               end case;

               if Exclude then
                  Append
                    (Result,
                     New_Ignore
                       (Prog =>
                          New_Located_Assert
                            (Ada_Node   => Exit_Kind,
                             Pred       => New_Not (Right => +Guard_Ident),
                             Reason     => VC_Exit_Case,
                             Kind       => EW_Assert,
                             Check_Info => Check_Info)));
               end if;
            end;
            Next (Exit_Case);
         end loop;
      end;

      return Result;
   end Compute_Exit_Cases_Simple_Checks;

   ------------------------------------
   -- Compute_Exit_Cases_Simple_Post --
   ------------------------------------

   --  Pragma/aspect Exit_Cases (Guard1 => Exit_Kind1,
   --                            Guard2 => Exit_Kind2,
   --                               ...
   --                            GuardN => Exit_KindN
   --                          [,OTHERS => Exit_KindN+1]);

   --  leads to the generation of a normal postcondition for the corresponding
   --  Why program function.

   --  If the this no OTHERS case or the OTHERS case is Name, generate:
   --
   --  /\ not (old guardi)  --  if Exit_Kindi is not Name
   --
   --  Otherwise, generate:
   --
   --  \/ old guardi        --  if Exit_Kindi is Name

   function Compute_Exit_Cases_Simple_Post
     (Params : Transformation_Params; E : Entity_Id; Name : Name_Id)
      return W_Pred_Id
   is
      Prag : constant Node_Id := Get_Pragma (E, Pragma_Exit_Cases);

   begin
      --  If no Exit_Cases on this subprogram, return

      if No (Prag) then
         return True_Pred;
      end if;

      --  Process individual exit cases in reverse order, to see the others
      --  case before the rest.

      declare
         Aggr           : constant Node_Id :=
           Expression (First (Pragma_Argument_Associations (Prag)));
         Assocs         : constant List_Id := Component_Associations (Aggr);
         Exit_Case      : Node_Id := Last (Assocs);
         Num_Cases      : constant Positive := Positive (List_Length (Assocs));
         Others_Is_Name : Boolean := True;
         --  Set to False if we find an OTHERS choice which is not Name
         Guards         : W_Pred_Array (1 .. Num_Cases);
         Top            : Natural := 0;
         Result         : W_Pred_Id;

      begin
         while Present (Exit_Case) loop
            declare
               Case_Guard : constant Node_Id :=
                 First (Choice_List (Exit_Case));
               Exit_Kind  : constant Node_Id := Expression (Exit_Case);
               Is_Name    : Boolean;
            begin
               case Nkind (Exit_Kind) is
                  when N_Identifier =>
                     Is_Name := Chars (Exit_Kind) = Name;

                  when N_Aggregate  =>
                     Is_Name := False;

                  when others       =>
                     raise Program_Error;
               end case;

               --  If we have an OTHERS choice, set Others_Is_Name

               if Nkind (Case_Guard) = N_Others_Choice then
                  Others_Is_Name := Is_Name;

               --  Otherwise, aggregate guards of cases which are not the same
               --  as the OTHERS choice.

               elsif Is_Name /= Others_Is_Name then
                  Top := Top + 1;
                  Guards (Top) :=
                    +Transform_Attribute_Old (Case_Guard, EW_Pred, Params);
               end if;
            end;
            Prev (Exit_Case);
         end loop;

         Result := New_Or_Pred (Guards (1 .. Top));

         --  If Others_Is_Name is set, then we have aggregated guards for
         --  termination different from Name. We need to add a negation.

         if Others_Is_Name then
            Result := New_Not (Right => Result);
         end if;

         return Result;
      end;
   end Compute_Exit_Cases_Simple_Post;

   --------------------------
   -- Compute_Inlined_Expr --
   --------------------------

   function Compute_Inlined_Expr
     (Function_Entity    : Entity_Id;
      Logic_Func_Binders : Item_Array;
      W_Return_Type      : W_Type_Id;
      Params             : Transformation_Params) return W_Term_Id
   is
      Value : constant Node_Id := Retrieve_Inline_Annotation (Function_Entity);
      W_Def : W_Term_Id;

   begin
      --  We fill the map of parameters, so that in the definition, we use
      --  local names of the parameters, instead of the global names.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Push_Binders_To_Symbol_Table (Logic_Func_Binders);

      --  If the function is annotated Logical_Eq, return a call to Why_Eq

      if Has_Logical_Eq_Annotation (Function_Entity) then
         declare
            Left       : constant Entity_Id := First_Formal (Function_Entity);
            Right      : constant Entity_Id := Next_Formal (Left);
            Left_Expr  : constant W_Expr_Id :=
              Transform_Identifier (Params, Left, Left, EW_Term);
            Right_Expr : constant W_Expr_Id :=
              Transform_Identifier (Params, Right, Right, EW_Term);
         begin
            if Has_Array_Type (Etype (Left)) then
               W_Def := +New_Logic_Eq_Call (+Left_Expr, +Right_Expr, EW_Term);
            else
               W_Def :=
                 New_Comparison
                   (Symbol => Why_Eq,
                    Left   => +Left_Expr,
                    Right  => +Right_Expr);
            end if;
         end;

      elsif No (Value) then
         W_Def := Why_Empty;

      --  If Function_Entity is recursive, it is not inlined as it may
      --  interfere with its verification.

      elsif Is_Recursive (Function_Entity) then
         Error_Msg_N
           ("recursive function cannot be inlined for proof",
            Function_Entity,
            Kind => Info_Kind);

         W_Def := Why_Empty;

      --  If Function_Entity needs a separate axiom module to break cyclicity
      --  in proof, its postcondition cannot be used to inline it.

      elsif Proof_Module_Cyclic (Function_Entity)
        and then not Find_Contracts
                       (Function_Entity, Pragma_Postcondition, False, False)
                       .Is_Empty
      then
         Error_Msg_N
           ("function cannot be inlined for proof",
            Function_Entity,
            Kind          => Info_Kind,
            Continuations =>
              ["inlining might cause circularity in the verification"
               & " process"]);
         W_Def := Why_Empty;

      --  Reconstruct the wrapper for potentially invalid values

      elsif Is_Potentially_Invalid (Function_Entity) then
         declare
            Valid_Flag : W_Expr_Id;
            Context    : Ref_Context;
         begin
            W_Def :=
              +Transform_Potentially_Invalid_Expr
                 (Expr          => Value,
                  Expected_Type => Type_Of_Node (Function_Entity),
                  Domain        => EW_Term,
                  Params        => Params,
                  Context       => Context,
                  Valid_Flag    => Valid_Flag);

            W_Def :=
              +New_Function_Validity_Wrapper_Value
                 (Fun        => Function_Entity,
                  Valid_Flag => Valid_Flag,
                  Value      => +W_Def);

            W_Def :=
              +Bindings_For_Ref_Context
                 (Expr => +W_Def, Context => Context, Domain => EW_Term);
         end;

      --  Translate the Value expression in Why

      else
         W_Def :=
           Transform_Term
             (Expr => Value, Expected_Type => W_Return_Type, Params => Params);

         if Is_Tagged_Type (Retysp (Etype (Function_Entity))) then
            W_Def :=
              New_Tag_And_Ext_Update
                (Ada_Node => Value,
                 Name     => W_Def,
                 Ty       => Etype (Function_Entity));
         end if;
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      return W_Def;
   end Compute_Inlined_Expr;

   ------------------------
   -- Declare_Exceptions --
   ------------------------

   procedure Declare_Exceptions (Th : Theory_UC) is
   begin
      for Exc of Subprogram_Exceptions loop
         Emit (Th, New_Exception_Declaration (Name => +Exc));
      end loop;
   end Declare_Exceptions;

   -----------------------------
   -- Declare_Logic_Functions --
   -----------------------------

   procedure Declare_Logic_Functions
     (Th                    : Theory_UC;
      Dispatch_Th           : Theory_UC := Empty_Theory;
      E                     : Callable_Kind_Id;
      Spec_Binders          : Binder_Array := Binder_Array'(1 .. 0 => <>);
      Specialization_Module : Symbol := No_Symbol;
      More_Reads            : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
   is
      Why_Type           : constant W_Type_Id :=
        (if Is_Potentially_Invalid (E)
         then Validity_Wrapper_Type (E)
         else Type_Of_Node (E));
      Logic_Func_Binders : constant Item_Array :=
        Compute_Binders (E, EW_Term, More_Reads);
      Logic_Why_Binders  : constant Binder_Array :=
        Spec_Binders & To_Binder_Array (Logic_Func_Binders);
      Logic_Id           : constant W_Identifier_Id :=
        To_Local
          (Logic_Function_Name
             (E, Specialization_Module => Specialization_Module));
      Pred_Id            : constant W_Identifier_Id :=
        To_Local
          (Guard_Predicate_Name
             (E, Specialization_Module => Specialization_Module));
      Params             : constant Transformation_Params :=
        (Logic_Params with delta Old_Policy => Ignore);
      Result_Id          : constant W_Identifier_Id :=
        New_Temp_Identifier (Base_Name => "result", Typ => Why_Type);
      Pred_Binders       : constant Binder_Array :=
        Binder_Type'
          (Ada_Node => Empty,
           B_Name   => +Result_Id,
           B_Ent    => Null_Entity_Name,
           Mutable  => False,
           Labels   => <>)
        & Logic_Why_Binders;
      Labels             : constant Symbol_Set :=
        (if Is_Expression_Function_Or_Completion (E)
           and then not Has_Contracts (E, Pragma_Postcondition)
           and then not Has_Contracts (E, Pragma_Contract_Cases)
           and then not Is_Recursive (E)
         then Symbol_Sets.To_Set (NID (GP_Inline_Marker))
         else Symbol_Sets.Empty_Set);

      Def : W_Term_Id;

      --  Start of processing for Declare_Logic_Functions

   begin
      if Is_Unchecked_Conversion_Instance (E) then
         declare
            Precise_UC               : constant True_Or_Explain :=
              Is_UC_With_Precise_Definition (E);
            Source, Target           : Node_Id;
            Source_Type, Target_Type : Entity_Id;
            Arg                      : constant W_Identifier_Id :=
              Logic_Why_Binders (1).B_Name;
         begin
            Get_Unchecked_Conversion_Args (E, Source, Target);
            Source_Type := Retysp (Entity (Source));
            Target_Type := Retysp (Entity (Target));

            if not Precise_UC.Ok then

               --  Output information on reason for imprecise handling of UC.

               Warning_Msg_N
                 (Warn_Imprecise_UC,
                  E,
                  Msg =>
                    Create_N
                      (Warn_Imprecise_UC,
                       Names => [To_String (Precise_UC.Explanation)]));

               Def := Why_Empty;

            elsif Is_Scalar_Type (Source_Type)
              and then Is_Scalar_Type (Target_Type)
            then
               Def :=
                 Precise_Integer_UC
                   (Arg           => +Arg,
                    Size          =>
                      Get_Attribute_Value (Source_Type, Attribute_Size),
                    Source_Type   => EW_Abstract (Source_Type),
                    Target_Type   => Base_Why_Type_No_Bool (Target_Type),
                    Source_Status => Get_Scalar_Status (Source_Type),
                    Target_Status => Get_Scalar_Status (Target_Type),
                    Ada_Function  => E);

            --  At least one of Source or Target is a composite type made up
            --  of integers. Convert Source to a large-enough modular type,
            --  and convert that value to Target. If all types involved are
            --  modular, then this benefits from bitvector support in provers.

            else
               Def :=
                 Precise_Composite_UC
                   (Arg          => +Arg,
                    Source_Type  => Source_Type,
                    Target_Type  => Target_Type,
                    Ada_Function => E);
            end if;
         end;

      else
         Def := Compute_Inlined_Expr (E, Logic_Func_Binders, Why_Type, Params);
      end if;

      --  Generate a logic function

      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => Logic_Id,
            Binders     => Logic_Why_Binders,
            Location    => No_Location,
            Labels      => Labels,
            Def         => +Def,
            Return_Type => Why_Type));

      --  Generate the guard for the postcondition of the function

      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pred,
            Name        => Pred_Id,
            Binders     => Pred_Binders,
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type => EW_Bool_Type));

      --  Generate logic functions and guards for dispatching and
      --  refined versions of the function in a separate module.

      if Is_Dispatching_Operation (E)
        and then not Is_Hidden_Dispatching_Operation (E)
      then
         Emit
           (Dispatch_Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => Logic_Id,
               Binders     => Tag_Binder & Logic_Why_Binders,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Why_Type));
         Emit
           (Dispatch_Th,
            New_Function_Decl
              (Domain      => EW_Pred,
               Name        => Pred_Id,
               Binders     =>
                 Pred_Binders (1)
                 & Tag_Binder
                 & Pred_Binders (2 .. Pred_Binders'Length),
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location,
               Return_Type => EW_Bool_Type));
      end if;

      --  Generate a function return the pledge of a traversal function.
      --  We don't need anything specific for dispatching functions as
      --  tagged types cannot be deep.

      if Is_Borrowing_Traversal_Function (E) then
         Declare_At_End_Function (Th, E, Logic_Why_Binders);
      end if;
   end Declare_Logic_Functions;

   --------------------------------------
   -- Generate_Ref_For_Concurrent_Self --
   --------------------------------------

   procedure Generate_Ref_For_Concurrent_Self
     (Th : Theory_UC; Prot_Ty : Entity_Id; Location : Source_Ptr) is
   begin
      Emit
        (Th,
         New_Global_Ref_Declaration
           (Ada_Node => Prot_Ty,
            Name     => Self_Name,
            Labels   => Symbol_Sets.Empty_Set,
            Location => Location,
            Ref_Type => Type_Of_Node (Prot_Ty)));

      --  Generate a variable for the move tree

      if Contains_Allocated_Parts (Prot_Ty) then
         Emit
           (Th,
            New_Global_Ref_Declaration
              (Name     => Concurrent_Self_Move_Tree_Id (Prot_Ty),
               Location => Location,
               Labels   => Symbol_Sets.Empty_Set,
               Ref_Type => Get_Move_Tree_Type (Prot_Ty)));
      end if;
   end Generate_Ref_For_Concurrent_Self;

   --------------------------
   -- Generate_VCs_For_LSP --
   --------------------------

   procedure Generate_VCs_For_LSP (E : Subprogram_Kind_Id) is
      Name      : constant String := Full_Name (E);
      Overrides : constant Boolean :=
        Present (Visible_Overridden_Operation (E));
      Params    : Transformation_Params;

      Inherited_Pre_List  : Node_Lists.List;
      Classwide_Pre_List  : Node_Lists.List;
      Dispatch_Pre_List   : Node_Lists.List;
      Pre_List            : Node_Lists.List;
      Inherited_Post_List : Node_Lists.List;
      Classwide_Post_List : Node_Lists.List;
      Dispatch_Post_List  : Node_Lists.List;
      Post_List           : Node_Lists.List;
      CC_List             : Node_Lists.List;

      Inherited_Pre_Spec  : W_Pred_Id;
      Dispatch_Pre_Spec   : W_Pred_Id;
      Pre_Spec            : W_Pred_Id;
      Inherited_Post_Spec : W_Pred_Id;
      Dispatch_Post_Spec  : W_Pred_Id;
      Post_Spec           : W_Pred_Id;

      Inherited_Pre_Assume : W_Prog_Id;
      Dispatch_Pre_Check   : W_Prog_Id;
      Classwide_Pre_Assume : W_Prog_Id;
      Pre_Check            : W_Prog_Id;
      Pre_Assume           : W_Prog_Id;
      Call_Effects         : W_Prog_Id;
      Post_Assume          : W_Prog_Id;
      Classwide_Post_Check : W_Prog_Id;
      Dispatch_Post_Assume : W_Prog_Id;
      Inherited_Post_Check : W_Prog_Id;

      Why_Body               : W_Prog_Id := +Void;
      Dispatch_Pre_RTE       : W_Prog_Id := +Void;
      Dispatch_Weaker_Pre    : W_Prog_Id := +Void;
      Weaker_Pre             : W_Prog_Id := +Void;
      Stronger_Post          : W_Prog_Id := +Void;
      Dispatch_Post_RTE      : W_Prog_Id := +Void;
      Stronger_Dispatch_Post : W_Prog_Id := +Void;

      Old_Parts : Node_Sets.Set;

      Th : Theory_UC;
   begin
      Th :=
        Open_Theory
          (WF_Main,
           New_Module (Name => Name & "__subprogram_lsp", File => No_Symbol),
           Comment =>
             "Module for checking LSP for subprogram "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  First create a new identifier for F'Result

      if Ekind (E) = E_Function then
         Result_Is_Mutable := True;
         Result_Name :=
           New_Identifier (Name => Name & "__result", Typ => Type_Of_Node (E));
      end if;

      Params := Contract_VC_Params;

      --  First retrieve contracts specified on the subprogram and the
      --  subprograms it overrides.

      Classwide_Pre_List :=
        Find_Contracts (E, Pragma_Precondition, Classwide => True);
      Pre_List := Find_Contracts (E, Pragma_Precondition);

      Classwide_Post_List :=
        Find_Contracts (E, Pragma_Postcondition, Classwide => True);
      Post_List := Find_Contracts (E, Pragma_Postcondition);

      CC_List := Find_Contracts (E, Pragma_Contract_Cases);

      --  Querry dispatching versions of classwide and inherited pre- or
      --  postcondition to perform checks for all descendants.

      Dispatch_Pre_List := Dispatching_Contract (Classwide_Pre_List);
      Inherited_Pre_List :=
        Dispatching_Contract
          (Find_Contracts (E, Pragma_Precondition, Inherited => True));

      Dispatch_Post_List := Dispatching_Contract (Classwide_Post_List);
      Inherited_Post_List :=
        Dispatching_Contract
          (Find_Contracts (E, Pragma_Postcondition, Inherited => True));

      --  Then, generate suitable predicates based on the specified contracts,
      --  with appropriate True defaults.

      Inherited_Pre_Spec :=
        +Compute_Spec (Params, Inherited_Pre_List, EW_Pred);
      Dispatch_Pre_Spec := +Compute_Spec (Params, Dispatch_Pre_List, EW_Pred);
      Pre_Spec := +Compute_Spec (Params, Pre_List, EW_Pred);

      Inherited_Post_Spec :=
        +Compute_Spec (Params, Inherited_Post_List, EW_Pred);
      Dispatch_Post_Spec :=
        +Compute_Spec (Params, Dispatch_Post_List, EW_Pred);
      Post_Spec :=
        +New_And_Expr
           (Left   => +Compute_Spec (Params, Post_List, EW_Pred),
            Right  => +Compute_CC_And_EC_Postcondition (Params, E),
            Domain => EW_Pred);

      --  Compute the effect of a call of the subprogram

      Call_Effects := Compute_Call_Effects (Params, E);

      --  If E has a class-wide precondition, check that it cannot raise a
      --  run-time error in an empty context.
      --  This check is done using dispatching operations so it is verified
      --  for all possible descendants.

      if not Dispatch_Pre_List.Is_Empty then
         Dispatch_Pre_RTE :=
           +Compute_Spec (Params, Dispatch_Pre_List, EW_Prog);
         Dispatch_Pre_RTE := New_Ignore (Prog => Dispatch_Pre_RTE);
      end if;

      --  If E is overriding another subprogram, check that its specified
      --  classwide precondition is weaker than the inherited one.
      --  This check is done using dispatching operations so it is verified
      --  for all possible descendants.

      if Overrides and then not Dispatch_Pre_List.Is_Empty then
         Inherited_Pre_Assume :=
           New_Assume_Statement (Pred => Inherited_Pre_Spec);

         Dispatch_Pre_Check :=
           New_Located_Assert
             (Ada_Node =>
                Get_Location_For_Aspect
                  (E, Pragma_Precondition, Classwide => True),
              Pred     => Dispatch_Pre_Spec,
              Reason   => VC_Weaker_Classwide_Pre,
              Kind     => EW_Assert);

         Dispatch_Weaker_Pre :=
           Sequence
             ((1 =>
                 New_Comment
                   (Comment =>
                      NID
                        ("Checking that class-wide precondition is"
                         & " implied by inherited precondition")),
               2 => Inherited_Pre_Assume,
               3 => Dispatch_Pre_Check));

         Dispatch_Weaker_Pre := New_Ignore (Prog => Dispatch_Weaker_Pre);
      end if;

      --  If E has a specific precondition, check that it is weaker than the
      --  classwide one.
      --  This check is done using specific operations as it only applies to
      --  the current operation.

      if not Pre_List.Is_Empty then

         --  Normal preconditions are not allowed on dispatching operations
         --  unless the dispatching type is a private type whose partial view
         --  is untagged.

         pragma Assert (Is_Hidden_Dispatching_Operation (E));
         pragma Assert (Classwide_Pre_List.Is_Empty);

         --  Only do the check for overriding subprograms. New primitives of
         --  privately tagged types cannot have classwide contracts.

         if Overrides then
            Classwide_Pre_Assume :=
              New_Assume_Statement
                (Pred => Get_LSP_Contract (Params, E, Pragma_Precondition));

            Pre_Check :=
              New_Located_Assert
                (Ada_Node => Get_Location_For_Aspect (E, Pragma_Precondition),
                 Pred     => Pre_Spec,
                 Reason   =>
                   (if Inherited_Pre_List.Is_Empty
                    then VC_Trivial_Weaker_Pre
                    else VC_Weaker_Pre),
                 Kind     => EW_Assert);

            Weaker_Pre :=
              Sequence
                ((1 =>
                    New_Comment
                      (Comment =>
                         NID
                           ("Checking that precondition is"
                            & " implied by class-wide precondition")),
                  2 => Classwide_Pre_Assume,
                  3 => Pre_Check));

            Weaker_Pre := New_Ignore (Prog => Weaker_Pre);
         end if;
      end if;

      --  If E has a specific postcondition, check that it is stronger than the
      --  classwide one. To that end, perform equivalent effects of call in
      --  context of precondition for static call.
      --  Skip this check if the dispatching postcondition is the default True
      --  postcondition.
      --  This check is done using specific operations as it only applies to
      --  the current operation.

      if not (Post_List.Is_Empty and then CC_List.Is_Empty)
        and then not (Classwide_Post_List.Is_Empty
                      and then Inherited_Post_List.Is_Empty)
      then
         Pre_Assume :=
           New_Assume_Statement
             (Pred =>
                Get_Static_Call_Contract (Params, E, Pragma_Precondition));

         Post_Assume := New_Assume_Statement (Pred => Post_Spec);

         Classwide_Post_Check :=
           New_Located_Assert
             (Ada_Node =>
                (if not Post_List.Is_Empty
                 then Get_Location_For_Aspect (E, Pragma_Postcondition)
                 elsif not CC_List.Is_Empty
                 then Get_Location_For_Aspect (E, Pragma_Contract_Cases)
                 else Empty),
              Pred     => Get_LSP_Contract (Params, E, Pragma_Postcondition),
              Reason   => VC_Stronger_Post,
              Kind     => EW_Assert);

         Stronger_Post :=
           Sequence
             ((1 =>
                 New_Comment
                   (Comment =>
                      NID
                        ("Simulate static call to subprogram "
                         & """"
                         & Get_Name_String (Chars (E))
                         & """")),
               2 => Pre_Assume,
               3 => Call_Effects,
               4 =>
                 New_Comment
                   (Comment =>
                      NID
                        ("Checking that class-wide postcondition is"
                         & " implied by postcondition")),
               5 => Post_Assume,
               6 => Classwide_Post_Check));

         Stronger_Post := New_Ignore (Prog => Stronger_Post);

         --  Collect old attributes referenced by the checks

         Collect_Old_For_Subprogram (E, Old_Parts);
         Collect_Old_Parts (Classwide_Post_List, Old_Parts);
         if Classwide_Post_List.Is_Empty then
            Collect_Old_Parts
              (Find_Contracts (E, Pragma_Postcondition, Inherited => True),
               Old_Parts);
         end if;
      end if;

      --  If E is overriding another subprogram, check that its specified
      --  classwide postcondition is stronger than the inherited one.
      --  Note that we should *not* assume the dispatching precondition for
      --  this check, as this would not be transitive.
      --  This check is done using dispatching operations so it is verified
      --  for all possible descendants.

      if not Dispatch_Post_List.Is_Empty and then Overrides then

         Dispatch_Post_Assume :=
           New_Assume_Statement (Pred => Dispatch_Post_Spec);

         Inherited_Post_Check :=
           New_Located_Assert
             (Ada_Node =>
                Get_Location_For_Aspect
                  (E, Pragma_Postcondition, Classwide => True),
              Pred     => Inherited_Post_Spec,
              Reason   => VC_Stronger_Classwide_Post,
              Kind     => EW_Assert);

         Stronger_Dispatch_Post :=
           Sequence
             ((1 =>
                 New_Comment
                   (Comment =>
                      NID
                        ("Checking that inherited postcondition is"
                         & " implied by class-wide postcondition")),
               2 => Call_Effects,
               3 => Dispatch_Post_Assume,
               4 => Inherited_Post_Check));

         Stronger_Dispatch_Post := New_Ignore (Prog => Stronger_Dispatch_Post);

         --  Collect old attributes referenced by the checks

         Collect_Old_Parts (Inherited_Post_List, Old_Parts);
         Collect_Old_Parts (Dispatch_Post_List, Old_Parts);
      end if;

      Why_Body :=
        Sequence
          ((1 => Dispatch_Pre_RTE,
            2 => Dispatch_Weaker_Pre,
            3 => Weaker_Pre,
            4 => Stronger_Post,
            5 => Stronger_Dispatch_Post));

      --  Add declarations for 'Old variables

      Why_Body :=
        +Bind_From_Mapping_In_Expr
           (Params => Params,
            Map    => Map_For_Old,
            Expr   => +Why_Body,
            Domain => EW_Pterm,
            Subset => Old_Parts);

      --  Check that the class-wide postcondition cannot raise runtime errors.
      --  To that end, perform equivalent effects of call in an empty context.
      --  Also check that the evaluation of 'Old variables are free of RTE in
      --  the empty context. Here again, we should *not* assume the dispatching
      --  precondition for this check, as this postcondition can be inherited
      --  in overridings weakening the precondition.
      --  This check is done using dispatching operations so it is verified
      --  for all possible descendants.

      if not Dispatch_Post_List.Is_Empty then
         Dispatch_Post_RTE :=
           +Compute_Spec (Params, Dispatch_Post_List, EW_Prog);
         Dispatch_Post_RTE := New_Ignore (Prog => Dispatch_Post_RTE);
         Dispatch_Post_RTE :=
           Sequence
             ((1 =>
                 New_Comment
                   (Comment =>
                      NID
                        ("Checking absence of RTE in"
                         & " class-wide postcondition")),
               2 => Call_Effects,
               3 => Dispatch_Post_RTE));

         --  Add declarations for 'Old variables with RTE

         Old_Parts.Clear;
         Collect_Old_Parts (Dispatch_Post_List, Old_Parts);

         Dispatch_Post_RTE :=
           +Bind_From_Mapping_In_Expr
              (Params => Params,
               Map    => Map_For_Old,
               Expr   => +Dispatch_Post_RTE,
               Domain => EW_Prog,
               Subset => Old_Parts);
      end if;

      Append (Why_Body, Dispatch_Post_RTE);

      --  Insert bindings for variants, they may be needed to check recursive
      --  calls in the classwide post. We use EW_Pterm as a domain here as RTE
      --  has already been checked while verifying E.

      Why_Body :=
        Insert_Bindings_For_Variants
          (E => E, Prog => Why_Body, Domain => EW_Pterm, Params => Params);

      --  Assume dynamic property of inputs before the checks

      Prepend
        (Compute_Dynamic_Property_For_Inputs (Params => Params, E => E),
         Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Body, E, Params);

      --  Declare a global variable to hold the result of a function

      if Ekind (E) = E_Function then
         pragma Assert (not Is_Potentially_Invalid (E));

         Emit
           (Th,
            New_Global_Ref_Declaration
              (Ada_Node => E,
               Name     => Result_Name,
               Labels   => Get_Counterexample_Labels (E),
               Location => No_Location,
               Ref_Type => Type_Of_Node (E)));
      end if;

      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain   => EW_Prog,
            Name     => Def_Name,
            Binders  => (1 => Unit_Param),
            Labels   => Symbol_Sets.Empty_Set,
            Location => Safe_First_Sloc (E),
            Def      => +Why_Body));

      --  We should *not* filter our own entity, it is needed for recursive
      --  calls.

      if Ekind (E) = E_Function then
         Result_Name := Why_Empty;
         Result_Is_Mutable := False;
      end if;

      Close_Theory (Th, Kind => VC_Generation_Theory, Defined_Entity => E);
   end Generate_VCs_For_LSP;

   ------------------------------------------
   -- Generate_VCs_For_Package_Elaboration --
   ------------------------------------------

   procedure Generate_VCs_For_Package_Elaboration (E : E_Package_Id) is
      Name       : constant String := Full_Name (E);
      Body_N     : constant Node_Id := Package_Body (E);
      Vis_Decls  : constant List_Id := Visible_Declarations_Of_Package (E);
      Priv_Decls : constant List_Id := Private_Declarations_Of_Package (E);
      Init_Conds : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Initial_Condition);
      Params     : Transformation_Params;

      Why_Body : W_Prog_Id := +Void;
      Why_Spec : W_Prog_Id := +Void;
      Post     : W_Pred_Id;
      Th       : Theory_UC;
   begin
      --  We open a new theory, so that the context is fresh for that package

      Th :=
        Open_Theory
          (WF_Main,
           New_Module (Name => Name & "__package_def", File => No_Symbol),
           Comment =>
             "Module for checking absence of run-time errors and "
             & "package initial condition on package elaboration of "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      Register_VC_Entity (E);

      Params := Body_Params;

      --  Reset the toplevel exceptions for exit paths

      Clear_Exceptions;

      if Within_Protected_Type (E) then
         declare
            CPT : constant Entity_Id := Containing_Protected_Type (E);
         begin
            --  The Ada_Node is important here, because that's how we detect
            --  occurrences of "self" in a term later.

            Self_Name := Concurrent_Self_Ident (CPT);
            Self_Is_Mutable := True;
         end;

         --  Declare global variable to hold the state of a protected object

         Generate_Ref_For_Concurrent_Self
           (Th, Containing_Protected_Type (E), Safe_First_Sloc (E));
      end if;

      --  Translate initial condition of E

      if not Init_Conds.Is_Empty
        and then (No (Body_N) or else Entity_Body_In_SPARK (E))
        and then not Is_Ignored_Internal (Body_N)
      then
         Post := True_Pred;

         for Expr of Init_Conds loop
            declare
               Conj : W_Pred_Id;
            begin
               --  Generate postcondition for generated subprogram, that
               --  corresponds to the initial condition of the package.

               Params.Phase := Generate_Contract_For_Body;
               Conj := Transform_Pred (Expr, EW_Bool_Type, Params);
               Conj := New_VC_Pred (Expr, Conj, VC_Initial_Condition);
               Post := New_And_Pred (Left => Post, Right => Conj);

               --  Generate program to check the absence of run-time errors in
               --  the initial condition.

               Params.Phase := Generate_VCs_For_Contract;
               Why_Body :=
                 Sequence
                   (Why_Body,
                    New_Ignore
                      (Prog => Transform_Prog (Expr, EW_Bool_Type, Params)));
            end;
         end loop;

      --  No initial condition, so no postcondition for the generated
      --  subprogram.

      else
         Post := Why_Empty;
      end if;

      --  Translate declarations and statements in the package body, if there
      --  is one and it is in SPARK.

      if Entity_Body_In_SPARK (E) then
         if Present (Handled_Statement_Sequence (Body_N))
           and then Body_Statements_In_SPARK (E)
         then
            Prepend
              (Transform_Handled_Statements
                 (Handled_Statement_Sequence (Body_N), Body_Params),
               Why_Body);
         end if;

         Why_Body :=
           Transform_Declarations_Block
             (Declarations (Body_N), Why_Body, Body_Params);

         --  Assume initial conditions of withed units from the body

         if Is_Compilation_Unit (E) then
            declare
               Local_Params : constant Transformation_Params :=
                 (Params with delta Phase => Generate_VCs_For_Contract);
            begin
               Prepend
                 (Assume_Initial_Condition_Of_Withed_Units
                    (Package_Body_Entity (Body_N), Local_Params),
                  Why_Body);
            end;
         end if;
      end if;

      --  Introduce a check for the type invariant of all the variables
      --  initialized by the package.

      if No (Body_N) or else Entity_Body_In_SPARK (E) then
         declare
            Params : constant Transformation_Params := Contract_VC_Params;
         begin
            Append (Why_Body, Check_Type_Invariants_For_Package (E, Params));
         end;
      end if;

      --  Translate public and private declarations of the package

      if Present (Priv_Decls) and then Private_Spec_In_SPARK (E) then
         Why_Spec :=
           Transform_Declarations_Block (Priv_Decls, Why_Spec, Body_Params);
      end if;

      if Present (Vis_Decls) then
         Why_Spec :=
           Transform_Declarations_Block (Vis_Decls, Why_Spec, Body_Params);
      end if;

      --  Assume initial conditions of withed units.
      --  ??? Currently, we only assume initial conditions of withed units
      --  on compilation units though it is also valid for library level
      --  packages. This is because it does not seem relevant for nested
      --  packages. It may be interesting to rather inline them.

      if Is_Compilation_Unit (E) then
         declare
            Local_Params : constant Transformation_Params :=
              (Params with delta Phase => Generate_VCs_For_Contract);
         begin
            Prepend
              (Assume_Initial_Condition_Of_Withed_Units (E, Local_Params),
               Why_Spec);
         end;
      end if;

      --  Assume precondition of the enclosing subprogram for nested packages
      --  which are declared directly inside the declarative part of the
      --  subprogram.
      --  ??? We could also assume it for other nested packages, but this would
      --  require havoking variables.

      declare
         Enclosing_Subp : constant Entity_Id :=
           Directly_Enclosing_Subprogram_Or_Entry (E);
      begin
         if Present (Enclosing_Subp) then
            declare
               Pre : W_Pred_Id :=
                 Get_Static_Call_Contract
                   (Params, Enclosing_Subp, Pragma_Precondition);
            begin

               --  For entries, also assume that the guard holds

               if Is_Entry (Enclosing_Subp)
                 and then Entity_Body_In_SPARK (Enclosing_Subp)
               then
                  declare
                     Params  : constant Transformation_Params :=
                       Contract_Body_Params;
                     Barrier : constant Node_Id :=
                       Entry_Body_Barrier (Get_Body (Enclosing_Subp));
                  begin
                     Pre :=
                       +New_And_Then_Expr
                          (Domain => EW_Pred,
                           Left   => +Pre,
                           Right  =>
                             Transform_Expr
                               (Barrier, EW_Bool_Type, EW_Pred, Params));
                  end;
               end if;

               Prepend (New_Assume_Statement (Pred => Pre), Why_Spec);
            end;
         end if;
      end;

      --  Assuming information about input variables and constants should be
      --  done separately for Why_Spec and Why_Body so that objects used in
      --  the body are not visible when analyszing the spec. It is necessary as
      --  bodies might introduce cycles in dependencies between packages.
      --  This might introduce duplicated assumptions in the body.

      --  We assume that objects used in the program are in range, if
      --  they are of a dynamic type.

      Params.Phase := Generate_VCs_For_Contract;

      Prepend
        (Assume_Dynamic_Invariant_For_Variables
           (Vars   => Get_Referenced_Variables (Why_Spec, E),
            Params => Params,
            Scope  => E),
         Why_Spec);
      --  Flow analysis does not compute the set of variables used from a
      --  package specification only. Do it from the generated Why.

      Prepend
        (Compute_Dynamic_Property_For_Inputs (Params => Params, E => E),
         Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Spec, E, Params);
      Assume_Value_Of_Constants (Why_Body, E, Params);

      --  Declare the toplevel exceptions for exit paths

      Declare_Exceptions (Th);

      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain   => EW_Prog,
            Name     => Def_Name,
            Binders  => (1 => Unit_Param),
            Location => Safe_First_Sloc (E),
            Labels   => Symbol_Sets.Empty_Set,
            Post     => Post,
            Def      => +Sequence (Why_Spec, Why_Body)));

      --  Cleanup

      Self_Name := Why_Empty;
      Self_Is_Mutable := False;

      Close_Theory (Th, Kind => VC_Generation_Theory, Defined_Entity => E);
   end Generate_VCs_For_Package_Elaboration;

   -------------------------------------
   -- Generate_VCs_For_Protected_Type --
   -------------------------------------

   procedure Generate_VCs_For_Protected_Type (E : E_Protected_Type_Id) is
      type Discr is record
         Id  : W_Identifier_Id;
         Val : W_Expr_Id;
      end record;
      --  Why3 representation of discriminants

      package Discriminant_Lists is new
        Ada.Containers.Doubly_Linked_Lists (Element_Type => Discr);

      W_Discriminants : Discriminant_Lists.List;
      --  Container for Why3 representations

      procedure Prepare_Discr;
      --  insert the discriminants into the symbol table so that they can be
      --  referred to by the Why generated for the various checks

      procedure Wrap_Discr (Expr : in out W_Prog_Id);

      -------------------
      -- Prepare_Discr --
      -------------------

      procedure Prepare_Discr is
         Discr_N : Node_Id := Empty;
      begin
         Ada_Ent_To_Why.Push_Scope (Symbol_Table);

         if Has_Discriminants (E) then
            Discr_N := First_Discriminant (E);
         end if;

         while Present (Discr_N) loop
            declare
               Discr_W : constant Discr :=
                 (Id  =>
                    New_Temp_Identifier (Typ => EW_Abstract (Etype (Discr_N))),

                  Val =>
                    New_Ada_Record_Access
                      (Ada_Node => Empty,
                       Domain   => EW_Term,
                       Name     => +Self_Name,
                       Field    => Discr_N,
                       Ty       => E));
            begin
               Insert_Tmp_Item_For_Entity (Discr_N, Discr_W.Id);

               W_Discriminants.Append (Discr_W);
            end;

            Next_Discriminant (Discr_N);
         end loop;
      end Prepare_Discr;

      ----------------
      -- Wrap_Discr --
      ----------------

      procedure Wrap_Discr (Expr : in out W_Prog_Id) is
      begin
         for W_D of reverse W_Discriminants loop
            Expr :=
              New_Typed_Binding
                (Name => +W_D.Id, Def => +W_D.Val, Context => Expr);
         end loop;
         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      end Wrap_Discr;

      Why_Body   : W_Prog_Id := +Void;
      Name       : constant String := Full_Name (E);
      Priv_Decls : constant List_Id := Private_Declarations_Of_Prot_Type (E);
      Vis_Decls  : constant List_Id := Visible_Declarations_Of_Prot_Type (E);
      Th         : Theory_UC;

      --  Start of processing for Generate_VCs_For_Protected_Type

   begin
      --  We open a new theory, so that the context is fresh for this task

      Th :=
        Open_Theory
          (WF_Main,
           New_Module (Name => Name & "__protected_type", File => No_Symbol),
           Comment =>
             "Module for various checks related to the protected type "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      Register_VC_Entity (E);

      --  The Ada_Node is important here, because that's how we detect
      --  occurrences of "self" in a term later.

      Self_Name := Concurrent_Self_Ident (E);
      Self_Is_Mutable := False;

      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => Self_Name,
            Binders     => (1 .. 0 => <>),
            Location    => Safe_First_Sloc (E),
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type => Get_Typ (Self_Name)));

      --  ??? Where is the call to Push_Scope?

      Prepare_Discr;

      --  If protected object attaches an interrupt, the priority must be in
      --  range of System.Interrupt_Priority; see RM C.3.1(11/3).

      if Requires_Interrupt_Priority (E) then
         declare
            P : constant Node_Id := Get_Priority_Or_Interrupt_Priority (E);
         begin

            --  If no priority was specified, the default priority is
            --  implementation-defined (RM D.3 (10/3)), but in range
            --  of System.Interrupt_Priority.

            if Present (P) then

               declare
                  P_Expr : constant W_Expr_Id :=
                    Transform_Expr
                      (Expr          => P,
                       Domain        => EW_Term,
                       Params        => Body_Params,
                       Expected_Type => EW_Int_Type);
               begin

                  --  Generate a range check, but with a reason of ceiling
                  --  check, as specified in RM index for "Ceiling_Check".

                  Append
                    (Why_Body,
                     New_Located_Assert
                       (Ada_Node => E,
                        Pred     =>
                          +New_Range_Expr
                             (Domain => EW_Pred,
                              Low    =>
                                New_Attribute_Expr
                                  (Domain => EW_Term,
                                   Ty     => RTE (RE_Interrupt_Priority),
                                   Attr   => Attribute_First,
                                   Params => Body_Params),
                              High   =>
                                New_Attribute_Expr
                                  (Domain => EW_Term,
                                   Ty     => RTE (RE_Interrupt_Priority),
                                   Attr   => Attribute_Last,
                                   Params => Body_Params),
                              Expr   => P_Expr),
                        Reason   => VC_Ceiling_Interrupt,
                        Kind     => EW_Check));
               end;
            end if;
         end;
      end if;

      --  Check that no Attach_Handler expression of the protected object
      --  corresponds to a reserved interrupt; see RM C.3.1(10/3).

      Append
        (Why_Body, Compute_Attach_Handler_Check (Base_Type (E), Body_Params));

      --  Translate public and private declarations of the package

      if Present (Priv_Decls) and then Private_Spec_In_SPARK (E) then
         --  Check for absence of runtime error in protected components initial
         --  values.

         declare
            Checks  : W_Statement_Sequence_Id := Void_Sequence;
            F_Check : W_Prog_Id;
         begin
            for Field of Get_Component_Set (E) loop
               if Ekind (Field) in E_Component | E_Discriminant then

                  if Present (Expression (Enclosing_Declaration (Field))) then

                     --  If Field has a default expression, use it

                     F_Check :=
                       Transform_Prog
                         (Expr          =>
                            Expression (Enclosing_Declaration (Field)),
                          Expected_Type => Type_Of_Node (Etype (Field)),
                          Params        => Body_Params);
                  else

                     --  Otherwise, use its Field's Etype default value

                     F_Check :=
                       Compute_Default_Check
                         (Field, Etype (Field), Body_Params);
                  end if;

                  if F_Check /= +Void then
                     Append
                       (Checks,
                        New_Ignore
                          (Ada_Node => Etype (Field), Prog => F_Check));
                  end if;
               end if;
            end loop;

            Append (Why_Body, +Checks);
         end;

         Why_Body :=
           Transform_Declarations_Block (Priv_Decls, Why_Body, Body_Params);
      end if;

      if Present (Vis_Decls) then
         Why_Body :=
           Transform_Declarations_Block (Vis_Decls, Why_Body, Body_Params);
      end if;

      Wrap_Discr (Why_Body);

      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain   => EW_Prog,
            Name     => Def_Name,
            Binders  => (1 => Unit_Param),
            Location => Safe_First_Sloc (E),
            Labels   => Symbol_Sets.Empty_Set,
            Def      => +Why_Body));

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      Self_Name := Why_Empty;
      Self_Is_Mutable := False;

      Close_Theory (Th, Kind => VC_Generation_Theory, Defined_Entity => E);
   end Generate_VCs_For_Protected_Type;

   ---------------------------------
   -- Generate_VCs_For_Subprogram --
   ---------------------------------

   procedure Generate_VCs_For_Subprogram (E : Callable_Kind_Id) is
      Name : constant String := Full_Name (E);
      Th   : Theory_UC;

      --  Start of processing for Generate_VCs_For_Subprogram

   begin
      Th :=
        Open_Theory
          (WF_Main,
           New_Module (Name => Name & "__subprogram_def", File => No_Symbol),
           Comment =>
             "Module for checking contracts and absence of "
             & "run-time errors in subprogram "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      Register_VC_Entity (E);

      Generate_VCs_For_Subprogram (E, Th, Def_Name);

      Close_Theory (Th, Kind => VC_Generation_Theory, Defined_Entity => E);
   end Generate_VCs_For_Subprogram;

   procedure Generate_VCs_For_Subprogram
     (E : Callable_Kind_Id; Th : Theory_UC; Prog_Name : W_Identifier_Id)
   is

      function Assume_For_Input return W_Prog_Id;
      --  Generate assumptions for dynamic types used in the program. An
      --  exception is made for predicate functions generated by the frontend,
      --  for which we should not assume that the predicate holds for checking
      --  the absence of RTE in the predicate itself.
      --  Also assume the type invariants of global inputs of E and of global
      --  parameters if E is a boundary subprogram.

      function Assume_For_Output return W_Prog_Id;
      --  Generate assumptions for deep outputs, that all pointers are moved at
      --  subprogram entry.

      function RTE_Of_Pre return W_Prog_Id;
      --  Compute an expression which contains the RTE checks of the
      --  precondition.

      function Assume_Or_Assert_Of_Pre return W_Prog_Id;
      --  Usually assumes the precondition, except for main programs where
      --  the precondition needs to be proved in fact. In this latter case
      --  an assertion is returned instead of an assumption.

      function Check_Feasibility return W_Prog_Id;
      --  Generate an assertion checking that there exists a possible return
      --  value for E consistent with its implicit or explicit postcondition.

      function Check_Inline_Annotation return W_Prog_Id;
      --  Checks that the expression used for inlining is equal to the result.
      --  This is done for functions annotated with Inline_For_Proof and
      --  Logical_Equal.

      function Check_Init_Of_Out_Params return W_Prog_Id;
      --  Checks initialization of out parameters at the end of the subprogram.

      function Check_Invariants_Of_Outputs
        (Exceptional : Boolean := False) return W_Prog_Id;
      --  Checks the type invariants of global output and of out parameters if
      --  E is a boundary subprogram.
      --  If Exceptional is True, only check "by reference" parameters.

      function Checking_Of_Refined_Post (Arg : W_Prog_Id) return W_Prog_Id
      with Pre => Entity_Body_In_SPARK (E);
      --  Encapsulate the translated body inside an abstract program with
      --  the Refined_Post as a postcondition.
      --  Assume the dynamic property of modified variables after the call.

      function Post_As_Pred return W_Pred_Id;
      --  Compute the postcondition predicate based on the Ada postcondition

      function Try_Block (Prog : W_Prog_Id) return W_Prog_Id;
      --  adding try/catch block for the return exception on top of the program

      Pre_Prags  : Node_Lists.List;
      Post_Prags : Node_Lists.List;

      procedure Get_Pre_Post_Pragmas (Decls : List_Id);
      --  Retrieve pragmas Precondition and Postcondition from the list
      --  of body declarations, and add them to Pre_Prags and Post_Prags
      --  when they do not come from aspects.

      function Transform_All_Pragmas
        (Prags : Node_Lists.List; Comment : String) return W_Prog_Id;
      --  Translate the pragma list in Prags into Why3.

      --  Mapping from guards to temporary names, and Why program to check
      --  contract cases and exit cases on exit.
      CC_Guard_Map : Ada_To_Why_Ident.Map;
      EC_Guard_Map : Ada_To_Why_Ident.Map;

      function CC_EC_And_RTE_Post return W_Prog_Id;
      --  Return verification of the contract cases, exit cases on normal
      --  return, plus runtime checks for the Post

      function Check_Exceptional_Cases
        (Exc_Id : W_Identifier_Id) return W_Prog_Id;
      --  Return verification of the exceptional cases

      function Declare_Old_Variables (P : W_Prog_Id) return W_Prog_Id;

      function Declare_Termination_Condition (P : W_Prog_Id) return W_Prog_Id;
      --  If E has a dynamic termination condition, introduce a declaration
      --  for its value at the beginning of the subprogram.

      function Warn_On_Inconsistent_Pre return W_Prog_Id;
      --  Generate a VC to warn on inconsistent preconditions

      function Warn_On_Inconsistent_Post return W_Prog_Id;
      --  Generate a VC to warn on inconsistent postconditions

      function Wrap_Decls_For_Guards
        (P : W_Prog_Id; Guard_Map : Ada_To_Why_Ident.Map) return W_Prog_Id;
      --  Helper subprogram, introduce bindings for guards of contract or exit
      --  cases over P.

      function Wrap_Decls_For_CC_Guards (P : W_Prog_Id) return W_Prog_Id;

      function Wrap_Decls_For_EC_Guards (P : W_Prog_Id) return W_Prog_Id;

      ----------------------
      -- Assume_For_Input --
      ----------------------

      function Assume_For_Input return W_Prog_Id is
         Pred_Fun_Param : constant Entity_Id :=
           (if Ekind (E) = E_Function and then Is_Predicate_Function (E)
            then First_Formal (E)
            else Empty);
         Params         : constant Transformation_Params := Contract_VC_Params;
      begin
         if Ekind (E) = E_Procedure and then Null_Present (E) then
            return +Void;
         end if;
         return
           Sequence
             ((1 =>
                 New_Comment
                   (Comment =>
                      NID
                        ("Assume dynamic invariants of inputs of the"
                         & " subprogram"
                         & (if Sloc (E) > 0
                            then " " & Build_Location_String (Sloc (E))
                            else ""))),
               2 =>
                 Compute_Dynamic_Property_For_Inputs
                   (Params         => Params,
                    E              => E,
                    Pred_Fun_Param => Pred_Fun_Param),
               3 =>
                 New_Assume_Statement
                   (Pred =>
                      Compute_Type_Invariants_For_Subprogram
                        (E => E, For_Input => True, Params => Params))));
      end Assume_For_Input;

      -----------------------
      -- Assume_For_Output --
      -----------------------

      function Assume_For_Output return W_Prog_Id is
         Params : constant Transformation_Params := Contract_VC_Params;
      begin
         if Ekind (E) = E_Procedure and then Null_Present (E) then
            return +Void;
         end if;
         return
           Sequence
             ((1 =>
                 New_Comment
                   (Comment =>
                      NID
                        ("Assume moved pointers in outputs of the"
                         & " subprogram"
                         & (if Sloc (E) > 0
                            then " " & Build_Location_String (Sloc (E))
                            else ""))),
               2 => Compute_Moved_Property_For_Deep_Outputs (E, Params)));
      end Assume_For_Output;

      -----------------------------
      -- Assume_Or_Assert_Of_Pre --
      -----------------------------

      function Assume_Or_Assert_Of_Pre return W_Prog_Id is
         Params   : constant Transformation_Params := Contract_VC_Params;
         Pre_Node : constant Node_Id :=
           Get_Location_For_Aspect (E, Pragma_Precondition);
         Pre      : W_Pred_Id :=
           Get_Static_Call_Contract (Params, E, Pragma_Precondition);
         Stmt     : W_Prog_Id;

      begin
         --  Need to prove precondition of Main before use. The test for
         --  entries is just to protect the call to Might_Be_Main.

         if Is_Subprogram (E) and then Might_Be_Main (E) then

            --  Initial conditions of withed units should only be available to
            --  prove the precondition of potential Main subprograms. It cannot
            --  be assumed for potential other calls which might occur during
            --  the elaboration.

            if No (Pre_Node) then
               pragma Assert (Is_True_Boolean (+Pre));
               Stmt := +Void;
            else
               Stmt :=
                 New_Located_Abstract
                   (Ada_Node => Pre_Node,
                    Expr     =>
                      Assume_Initial_Condition_Of_Withed_Units (E, Params),
                    Reason   => VC_Precondition_Main,
                    Post     => Pre);
            end if;
         else
            if Is_Entry (E) and then Entity_Body_In_SPARK (E) then
               declare
                  Params  : constant Transformation_Params :=
                    Contract_Body_Params;
                  Body_N  : constant Node_Id := Entry_Body (E);
                  Barrier : constant Node_Id := Entry_Body_Barrier (Body_N);
               begin
                  Pre :=
                    +New_And_Then_Expr
                       (Domain => EW_Pred,
                        Left   => +Pre,
                        Right  =>
                          Transform_Expr
                            (Barrier, EW_Bool_Type, EW_Pred, Params));
               end;
            end if;
            Stmt := New_Assume_Statement (Pred => Pre);
         end if;

         return
           Sequence
             (New_Comment
                (Comment =>
                   NID
                     ("Assume Pre of the subprogram"
                      & (if Sloc (E) > 0
                         then " " & Build_Location_String (Sloc (E))
                         else ""))),
              Stmt);
      end Assume_Or_Assert_Of_Pre;

      ------------------------
      -- CC_EC_And_RTE_Post --
      ------------------------

      function CC_EC_And_RTE_Post return W_Prog_Id is
         Params : constant Transformation_Params := Contract_VC_Params;
      begin
         return
           Sequence
             ((1 =>
                 New_Ignore
                   (Prog =>
                      +Compute_Spec
                         (Params, E, Pragma_Postcondition, EW_Prog)),
               2 =>
                 Compute_Contract_Cases_Exit_Checks
                   (Params => Params, E => E, Guard_Map => CC_Guard_Map),
               3 =>
                 Compute_Exit_Cases_Simple_Checks
                   (E         => E,
                    Name      => Name_Normal_Return,
                    Guard_Map => EC_Guard_Map)));
      end CC_EC_And_RTE_Post;

      -----------------------------
      -- Check_Exceptional_Cases --
      -----------------------------

      function Check_Exceptional_Cases
        (Exc_Id : W_Identifier_Id) return W_Prog_Id
      is

         function Check_Post_For_Case
           (Exceptional_Case : Node_Id; Params : Transformation_Params)
            return W_Prog_Id;
         --  RTE and post check for Exceptional_Case

         -------------------------
         -- Check_Post_For_Case --
         -------------------------

         function Check_Post_For_Case
           (Exceptional_Case : Node_Id; Params : Transformation_Params)
            return W_Prog_Id
         is
            Post     : constant Node_Id := Expression (Exceptional_Case);
            RTE_Post : constant W_Prog_Id := Transform_Prog (Post, Params);
         begin
            return
              Sequence
                (New_Ignore
                   (Post,
                    Warn_On_Dead_Branch
                      (Post, RTE_Post, Params.Phase, Params.Warn_On_Dead)),
                 New_Assert
                   (Ada_Node    => Post,
                    Pred        =>
                      New_VC_Pred
                        (Post,
                         Transform_Pred (Post, Params),
                         VC_Exceptional_Case),
                    Assert_Kind => EW_Assert));
         end Check_Post_For_Case;

         Params : constant Transformation_Params := Contract_VC_Params;
         Prag   : constant Node_Id := Get_Pragma (E, Pragma_Exceptional_Cases);

      begin
         --  If there is no exceptional cases, then it should be generated from
         --  the set of expected exceptions. All expected exceptions are
         --  allowed in any context, so there is nothing to check.

         if No (Prag) then
            return +Void;
         end if;

         declare
            Aggr             : constant Node_Id :=
              Expression (First (Pragma_Argument_Associations (Prag)));
            Assocs           : constant List_Id :=
              Component_Associations (Aggr);
            Others_Present   : constant Boolean :=
              Nkind (First (Choice_List (Last (Assocs)))) = N_Others_Choice;
            Nb_Cases         : constant Integer :=
              Natural (List_Length (Assocs));
            Elsif_Parts      :
              W_Prog_Array (2 .. Nb_Cases - (if Others_Present then 1 else 0));
            Else_Part        : W_Prog_Id;
            Exceptional_Case : Node_Id := First (Assocs);

            --  Start of processing for Check_Exceptional_Cases

         begin
            --  Get the case where there is only one choice out of the way

            if Nb_Cases = 1 then
               return Check_Post_For_Case (Exceptional_Case, Params);
            end if;

            --  Fill the Elsif_Parts if any

            Next (Exceptional_Case);
            if Elsif_Parts'Length > 0 then
               for Num in Elsif_Parts'Range loop
                  Elsif_Parts (Num) :=
                    New_Elsif
                      (Condition =>
                         +Compute_Guard_For_Exceptions
                            (Choice_List (Exceptional_Case), Exc_Id, EW_Prog),
                       Then_Part =>
                         Check_Post_For_Case (Exceptional_Case, Params));
                  Next (Exceptional_Case);
               end loop;
            end if;

            --  Fill the Else_Part if any

            if Others_Present then
               Else_Part := Check_Post_For_Case (Exceptional_Case, Params);

            --  Checks that no unexpected exceptions are raised are done on
            --  raises.

            else
               Else_Part := Why_Empty;
            end if;

            --  Reconstruct the conditional

            Exceptional_Case := First (Assocs);

            return
              New_Conditional
                (Ada_Node    => Prag,
                 Condition   =>
                   +Compute_Guard_For_Exceptions
                      (Choice_List (Exceptional_Case), Exc_Id, EW_Prog),
                 Then_Part   => Check_Post_For_Case (Exceptional_Case, Params),
                 Elsif_Parts => Elsif_Parts,
                 Else_Part   => Else_Part);
         end;
      end Check_Exceptional_Cases;

      -----------------------
      -- Check_Feasibility --
      -----------------------

      function Check_Feasibility return W_Prog_Id is
         Save_Result_Is_Mutable : constant Boolean := Result_Is_Mutable;
         Save_Result_Name       : constant W_Identifier_Id := Result_Name;

         Local_Params : constant Transformation_Params :=
           (Body_Params with delta Old_Policy => Ignore);
         --  Old can safely be ignored in postconditions of functions
         Why_Type     : constant W_Type_Id := Type_Of_Node (E);
         Result_Id    : W_Identifier_Id :=
           New_Temp_Identifier (Typ => Why_Type, Base_Name => "result");

      begin
         pragma Assert (not Is_Potentially_Invalid (E));

         --  Store an immutable local name for the result that can be
         --  existentially quantified.

         Result_Is_Mutable := False;
         Result_Name := Result_Id;

         declare
            pragma Assert (Include_All_Global_Invariants_For_Subp (E));
            Dynamic_Prop_Result : constant W_Pred_Id :=
              +New_And_Then_Expr
                 (Left   =>
                    +Compute_Dynamic_Inv_And_Initialization
                       (Expr     => +Result_Name,
                        Ty       => Etype (E),
                        Only_Var => False_Term,
                        Params   => Local_Params),
                  Right  =>
                    +Compute_Type_Invariants_For_Subprogram
                       (E, Local_Params, For_Input => False),
                  Domain => EW_Pred);
            Post                : W_Pred_Id :=
              New_And_Pred
                (Left  => Dynamic_Prop_Result,
                 Right =>
                   New_And_Pred
                     (Left  =>
                        Get_Static_Call_Contract
                          (Local_Params, E, Pragma_Postcondition),
                      Right =>
                        Compute_CC_And_EC_Postcondition (Local_Params, E)));

         begin
            --  For arrays, the has_bounds predicate is impossible to prove as
            --  it is abstract. Introduce a call to slice.
            --    let result = slice new_result in post result

            if Has_Array_Type (Etype (E)) then
               declare
                  New_Res_Id : constant W_Identifier_Id :=
                    New_Temp_Identifier
                      (Typ => Why_Type, Base_Name => "result");
               begin
                  Post :=
                    New_Binding
                      (Name    => Result_Id,
                       Def     =>
                         +New_Slice_Call (EW_Term, +New_Res_Id, Why_Type),
                       Context => Post);

                  Result_Id := New_Res_Id;
               end;
            end if;

            --  Restore the previous state

            Result_Is_Mutable := Save_Result_Is_Mutable;
            Result_Name := Save_Result_Name;

            --  Generate:
            --    exists result : why_type. post result

            return
              New_Located_Assert
                (Ada_Node => E,
                 Pred     =>
                   New_Existential_Quantif
                     (Binders =>
                        (1 =>
                           New_Binder
                             (Domain   => EW_Pred,
                              Name     => Result_Id,
                              Arg_Type => Why_Type)),
                      Labels  => Symbol_Sets.Empty_Set,
                      Pred    => Post),
                 Reason   => VC_Feasible_Post,
                 Kind     => EW_Assert);
         end;
      end Check_Feasibility;

      ------------------------------
      -- Check_Init_Of_Out_Params --
      ------------------------------

      function Check_Init_Of_Out_Params return W_Prog_Id is
         Param  : Entity_Id := First_Formal (E);
         Checks : W_Prog_Id := +Void;

      begin
         while Present (Param) loop
            declare
               B : constant Item_Type :=
                 Ada_Ent_To_Why.Element (Symbol_Table, Param);
            begin
               if Ekind (Param) = E_Out_Parameter
                 and then Obj_Has_Relaxed_Init (Param)
               then
                  Continuation_Stack.Append
                    (Continuation_Type'
                       (E,
                        To_Unbounded_String
                          ("for parameter "
                           & Source_Name (Param)
                           & " at the end of the subprogram")));

                  if B.Init.Present then
                     Append
                       (Checks,
                        New_Located_Assert
                          (Ada_Node => Param,
                           Pred     =>
                             Pred_Of_Boolean_Term
                               (New_Deref
                                  (Right => B.Init.Id,
                                   Typ   => Get_Typ (B.Init.Id))),
                           Reason   => VC_Initialization_Check,
                           Kind     => EW_Assert));

                  elsif Has_Scalar_Full_View (Etype (Param)) then
                     Append
                       (Checks,
                        New_Located_Assert
                          (Ada_Node => Param,
                           Pred     =>
                             +Compute_Is_Initialized
                                (E                  => Etype (Param),
                                 Name               =>
                                   +Reconstruct_Item
                                      (B, Body_Params.Ref_Allowed),
                                 Params             => Body_Params,
                                 Domain             => EW_Pred,
                                 Exclude_Components => Relaxed),
                           Reason   => VC_Initialization_Check,
                           Kind     => EW_Assert));

                  elsif Has_Predicates (Etype (Param)) then
                     Append
                       (Checks,
                        New_Predicate_Check
                          (Ada_Node => Param,
                           W_Expr   =>
                             +Reconstruct_Item (B, Body_Params.Ref_Allowed),
                           Ty       => Etype (Param)));
                  end if;

                  Continuation_Stack.Delete_Last;
               end if;
            end;
            Next_Formal (Param);
         end loop;

         return Checks;
      end Check_Init_Of_Out_Params;

      -----------------------------
      -- Check_Inline_Annotation --
      -----------------------------

      function Check_Inline_Annotation return W_Prog_Id is
         Need_Check : constant Boolean :=
           (Present (Retrieve_Inline_Annotation (E))
            and then (not Is_Expression_Function_Or_Completion (E)
                      or else not Entity_Body_Compatible_With_SPARK (E)))
           or else Has_Logical_Eq_Annotation (E);
         Params     : constant Transformation_Params := Contract_VC_Params;
      begin
         if Need_Check then
            pragma Assert (not Is_Potentially_Invalid (E));

            declare
               Def : constant W_Term_Id :=
                 Compute_Inlined_Expr
                   (Function_Entity    => E,
                    Logic_Func_Binders => (1 .. 0 => <>),
                    W_Return_Type      => Get_Typ (Result_Name),
                    Params             => Params);
            begin
               if Def /= Why_Empty then
                  return
                    New_Assert
                      (Pred        =>
                         New_VC_Pred
                           (Ada_Node => Find_Inline_Pragma (E),
                            Expr     =>
                              New_Comparison
                                (Symbol => Why_Eq,
                                 Left   =>
                                   New_Deref
                                     (Right => Result_Name,
                                      Typ   => Get_Typ (Result_Name)),
                                 Right  => Def),
                            Reason   => VC_Inline_Check),
                       Assert_Kind => EW_Assert);
               else
                  return +Void;
               end if;
            end;
         else
            return +Void;
         end if;
      end Check_Inline_Annotation;

      ---------------------------------
      -- Check_Invariants_Of_Outputs --
      ---------------------------------

      function Check_Invariants_Of_Outputs
        (Exceptional : Boolean := False) return W_Prog_Id
      is
         Params : constant Transformation_Params := Contract_VC_Params;
      begin
         return
           Check_Type_Invariants_For_Subprogram
             (E, E, Params, For_Input => False, Exceptional => Exceptional);
      end Check_Invariants_Of_Outputs;

      ------------------------------
      -- Checking_Of_Refined_Post --
      ------------------------------

      function Checking_Of_Refined_Post (Arg : W_Prog_Id) return W_Prog_Id is
         Params : constant Transformation_Params := Contract_VC_Params;
         Prog   : W_Prog_Id := Arg;
      begin
         if Has_Contracts (E, Pragma_Refined_Post) then
            Append
              (Prog,
               New_Ignore
                 (Prog =>
                    +Compute_Spec (Params, E, Pragma_Refined_Post, EW_Prog)));
            Prog :=
              New_Located_Abstract
                (Ada_Node => Get_Location_For_Aspect (E, Pragma_Refined_Post),
                 Expr     => Prog,
                 Reason   => VC_Refined_Post,
                 Post     =>
                   +Compute_Spec (Params, E, Pragma_Refined_Post, EW_Pred));
            Append
              (Prog,
               New_Assume_Statement
                 (Pred => Compute_Dynamic_Property_For_Effects (E, Params)));

            --  For functions we also need to assume the dynamic invariant of
            --  the result.

            if Ekind (E) = E_Function then
               declare
                  pragma Assert (Include_All_Global_Invariants_For_Subp (E));
                  Dyn_Prop : W_Pred_Id :=
                    Compute_Dynamic_Inv_And_Initialization
                      (Expr   =>
                         New_Deref
                           (Right => Result_Name,
                            Typ   => Get_Typ (Result_Name)),
                       Ty     => Etype (E),
                       Params => Params,
                       Valid  => Get_Valid_Id_For_Result (E));

               begin
                  --  For borrowing traversal functions, add the dynamic
                  --  invariant of the result at end and of the borrowed
                  --  parameter at end.

                  if Is_Borrowing_Traversal_Function (E) then
                     declare
                        Brower_At_End   : constant W_Identifier_Id :=
                          Get_Brower_At_End (E);
                        Borrowed_At_End : constant W_Identifier_Id :=
                          To_Local (Get_Borrowed_At_End (E));
                     begin
                        Dyn_Prop :=
                          New_And_Pred
                            (Conjuncts =>
                               (1 => Dyn_Prop,
                                2 =>
                                  Compute_Dynamic_Inv_And_Initialization
                                    (Expr   =>
                                       New_Deref
                                         (Right => Brower_At_End,
                                          Typ   => Get_Typ (Brower_At_End)),
                                     Ty     => Etype (E),
                                     Params => Params),
                                3 =>
                                  Compute_Dynamic_Inv_And_Initialization
                                    (Expr   => +Borrowed_At_End,
                                     Ty     => Etype (First_Formal (E)),
                                     Params => Params)));
                     end;
                  end if;

                  Append (Prog, New_Assume_Statement (Pred => Dyn_Prop));
               end;
            end if;
         end if;
         return Prog;
      end Checking_Of_Refined_Post;

      ---------------------------
      -- Declare_Old_Variables --
      ---------------------------

      function Declare_Old_Variables (P : W_Prog_Id) return W_Prog_Id is
         CC_List  : constant Node_Lists.List :=
           Find_Contracts (E, Pragma_Contract_Cases);
         Post_Old : Node_Sets.Set;
         CC_Old   : Node_Sets.Set;
         R        : W_Prog_Id;
      begin
         --  Add mapping for Old variables coming from the postcondition. Use
         --  the EW_Prog domain to generate checks for them.

         Collect_Old_For_Subprogram (E, Post_Old, Exclude_CC => True);

         if Entity_Body_In_SPARK (E) then
            Collect_Old_Parts
              (Find_Contracts (E, Pragma_Refined_Post), Post_Old);
            Collect_Old_Parts (Post_Prags, Post_Old);
         end if;

         R :=
           +Bind_From_Mapping_In_Expr
              (Params => Body_Params,
               Map    => Map_For_Old,
               Expr   => +P,
               Domain => EW_Prog,
               Subset => Post_Old);

         --  Add mapping for Old variables coming from the contract case if
         --  any. Checks are generated separately as they should only be done
         --  when in the correct contract case.

         for Aggr of CC_List loop
            Collect_Old_Parts (Aggr, CC_Old);
            R :=
              +Bind_From_Mapping_In_Expr
                 (Params => Body_Params,
                  Map    => Map_For_Old,
                  Expr   => +R,
                  Domain => EW_Pterm,
                  Subset => CC_Old);

            --  Generate checks for Old variables inside ignore blocks when the
            --  corresponding guard is enabled.

            declare
               Contract_Case : Node_Id :=
                 First (Component_Associations (Aggr));
               Case_Guard    : Node_Id;
            begin
               while Present (Contract_Case) loop
                  CC_Old.Clear;
                  Collect_Old_Parts (Expression (Contract_Case), CC_Old);
                  Case_Guard := First (Choice_List (Contract_Case));
                  Prepend
                    (New_Conditional
                       (Condition =>
                          +(if Nkind (Case_Guard) = N_Others_Choice
                            then CC_Guard_Map.Element (Aggr)
                            else CC_Guard_Map.Element (Case_Guard)),
                        Then_Part =>
                          +New_Ignore
                             (Prog =>
                                +Bind_From_Mapping_In_Expr
                                   (Params => Body_Params,
                                    Map    => Map_For_Old,
                                    Expr   => +Void,
                                    Domain => EW_Prog,
                                    Subset => CC_Old))),
                     R);

                  Next (Contract_Case);
               end loop;
            end;
         end loop;
         return R;
      end Declare_Old_Variables;

      -----------------------------------
      -- Declare_Termination_Condition --
      -----------------------------------

      function Declare_Termination_Condition (P : W_Prog_Id) return W_Prog_Id
      is
         Cond : constant Termination_Condition :=
           Get_Termination_Condition (E);
      begin
         if Cond.Kind = Dynamic then
            return
              New_Binding
                (Name    => Termination_Condition_Name,
                 Def     => Transform_Prog (Cond.Condition, Body_Params),
                 Context => P);
         else
            return P;
         end if;
      end Declare_Termination_Condition;

      --------------------------
      -- Get_Pre_Post_Pragmas --
      --------------------------

      procedure Get_Pre_Post_Pragmas (Decls : List_Id) is
         Decl : Node_Id := First (Decls);
      begin
         while Present (Decl) loop
            if Is_Pragma (Decl, Pragma_Precondition)
              and then not From_Aspect_Specification (Decl)
            then
               Pre_Prags.Append (Decl);

            elsif Is_Pragma (Decl, Pragma_Postcondition)
              and then not From_Aspect_Specification (Decl)
            then
               Post_Prags.Append (Decl);

            --  Stop the search if a new declaration is found

            elsif Decl_Starts_Pragma_Annotate_Range (Decl) then
               exit;
            end if;
            Next (Decl);
         end loop;
      end Get_Pre_Post_Pragmas;

      ------------------
      -- Post_As_Pred --
      ------------------

      function Post_As_Pred return W_Pred_Id is
         Params      : constant Transformation_Params :=
           (Contract_Body_Params with delta Old_Policy => As_Old);
         Mark_Params : Transformation_Params := Params;
         Post_N      : Node_Id;
      begin
         Mark_Params.Gen_Marker := GM_Toplevel;

         --  There might be no specific postcondition for E. In that case, the
         --  classwide or inherited postcondition is checked if present. Locate
         --  it on E for the inherited case.

         if Has_Contracts (E, Pragma_Postcondition) then
            Post_N := Get_Location_For_Aspect (E, Pragma_Postcondition);
         elsif Has_Contracts (E, Pragma_Postcondition, Classwide => True) then
            Post_N :=
              Get_Location_For_Aspect
                (E, Pragma_Postcondition, Classwide => True);
         elsif Has_Contracts (E, Pragma_Postcondition, Inherited => True) then
            Post_N :=
              Get_Location_For_Aspect
                (E, Pragma_Postcondition, Inherited => True);
         else
            Post_N := Empty;
         end if;
         if Entity_Body_In_SPARK (E) then

            --  Translate contract of E. A No_Return subprogram, from the
            --  inside, has postcondition true as non-termination verification
            --  is done by the frontend, but the precondition is unchanged.

            if (Is_Subprogram (E) and then No_Return (E)) or else No (Post_N)
            then
               pragma
                 Assert
                   (if No (Post_N)
                      then
                        Is_True_Boolean
                          (+Get_Static_Call_Contract
                              (Mark_Params, E, Pragma_Postcondition)));
               return Why_Empty;
            else
               return
                 New_VC_Pred
                   (Post_N,
                    Get_Static_Call_Contract
                      (Mark_Params, E, Pragma_Postcondition),
                    VC_Postcondition);
            end if;
         else
            return Why_Empty;
         end if;
      end Post_As_Pred;

      ----------------
      -- RTE_Of_Pre --
      ----------------

      function RTE_Of_Pre return W_Prog_Id is
         Params : constant Transformation_Params := Contract_VC_Params;
         Pre    : constant W_Prog_Id :=
           +Compute_Spec (Params, E, Pragma_Precondition, EW_Prog);
      begin
         return
           Sequence
             (New_Comment
                (Comment =>
                   NID
                     ("Check for RTE in the Pre of the subprogram"
                      & (if Sloc (E) > 0
                         then " " & Build_Location_String (Sloc (E))
                         else ""))),
              New_Ignore (Prog => Pre));
      end RTE_Of_Pre;

      ---------------------------
      -- Transform_All_Pragmas --
      ---------------------------

      function Transform_All_Pragmas
        (Prags : Node_Lists.List; Comment : String) return W_Prog_Id
      is
         Result : W_Prog_Id;
      begin
         if Prags.Is_Empty then
            Result := +Void;
         else
            Result :=
              New_Comment
                (Comment =>
                   NID
                     (Comment
                      & (if Sloc (E) > 0
                         then " " & Build_Location_String (Sloc (E))
                         else "")));

            for Prag of Prags loop
               Append
                 (Result, Transform_Pragma (Prag, Body_Params, Force => True));
            end loop;
         end if;

         return Result;
      end Transform_All_Pragmas;

      ---------------
      -- Try_Block --
      ---------------

      function Try_Block (Prog : W_Prog_Id) return W_Prog_Id is
      begin
         return
           New_Try_Block
             (Prog    => Prog,
              Handler =>
                (1 => New_Handler (Name => M_Main.Return_Exc, Def => +Void)));
      end Try_Block;

      -------------------------------
      -- Warn_On_Inconsistent_Post --
      -------------------------------

      function Warn_On_Inconsistent_Post return W_Prog_Id is
         Params    : constant Transformation_Params := Contract_VC_Params;
         Post      : W_Pred_Id :=
           Get_Static_Call_Contract (Params, E, Pragma_Postcondition);
         Stmt      : W_Prog_Id;
         Post_Node : constant Node_Id :=
           Get_Location_For_Aspect (E, Pragma_Postcondition);
      begin
         if No (Post_Node) then
            return +Void;
         end if;

         --  Negate the condition to check for an inconsistency
         Post := New_Not (Right => +Post);

         Stmt :=
           Sequence
             (Compute_Call_Effects (Params, E),
              New_Located_Assert
                (Ada_Node => Post_Node,
                 Pred     => Post,
                 Reason   => VC_Inconsistent_Post,
                 Kind     => EW_Assert));

         return
           Sequence
             (New_Comment
                (Comment =>
                   NID
                     ("Check inconsistency of Post of subprogram"
                      & (if Sloc (E) > 0
                         then " " & Build_Location_String (Sloc (E))
                         else ""))),
              New_Ignore (Prog => Stmt));
      end Warn_On_Inconsistent_Post;

      ------------------------------
      -- Warn_On_Inconsistent_Pre --
      ------------------------------

      function Warn_On_Inconsistent_Pre return W_Prog_Id is
         Params   : constant Transformation_Params := Contract_VC_Params;
         Pre      : W_Pred_Id :=
           Get_Static_Call_Contract (Params, E, Pragma_Precondition);
         Stmt     : W_Prog_Id;
         Pre_Node : constant Node_Id :=
           Get_Location_For_Aspect (E, Pragma_Precondition);
      begin
         if No (Pre_Node) then
            return +Void;
         end if;

         if Is_Entry (E) then
            declare
               Params  : constant Transformation_Params :=
                 Contract_Body_Params;
               Body_N  : constant Node_Id := Get_Body (E);
               Barrier : constant Node_Id := Entry_Body_Barrier (Body_N);
            begin
               Pre :=
                 +New_And_Then_Expr
                    (Domain => EW_Pred,
                     Left   => +Pre,
                     Right  =>
                       Transform_Expr
                         (Barrier, EW_Bool_Type, EW_Pred, Params));
            end;
         end if;

         --  Negate the condition to check for an inconsistency
         Pre := New_Not (Right => +Pre);

         Stmt :=
           New_Located_Assert
             (Ada_Node => Pre_Node,
              Pred     => Pre,
              Reason   => VC_Inconsistent_Pre,
              Kind     => EW_Assert);

         return
           Sequence
             (New_Comment
                (Comment =>
                   NID
                     ("Check inconsistency of Pre of subprogram"
                      & (if Sloc (E) > 0
                         then " " & Build_Location_String (Sloc (E))
                         else ""))),
              New_Ignore (Prog => Stmt));
      end Warn_On_Inconsistent_Pre;

      ------------------------------
      -- Wrap_Decls_For_CC_Guards --
      ------------------------------

      function Wrap_Decls_For_CC_Guards (P : W_Prog_Id) return W_Prog_Id
      is (Wrap_Decls_For_Guards (P, CC_Guard_Map));

      ------------------------------
      -- Wrap_Decls_For_EC_Guards --
      ------------------------------

      function Wrap_Decls_For_EC_Guards (P : W_Prog_Id) return W_Prog_Id
      is (Wrap_Decls_For_Guards (P, EC_Guard_Map));

      ---------------------------
      -- Wrap_Decls_For_Guards --
      ---------------------------

      function Wrap_Decls_For_Guards
        (P : W_Prog_Id; Guard_Map : Ada_To_Why_Ident.Map) return W_Prog_Id
      is
         Prog : W_Prog_Id := P;

      begin
         --  First traverse aggregates that stand for others cases

         for C in Guard_Map.Iterate loop
            declare
               Id : constant W_Identifier_Id := Ada_To_Why_Ident.Element (C);
               N  : constant Node_Id := Ada_To_Why_Ident.Key (C);

            begin
               if Nkind (N) = N_Aggregate then
                  Prog :=
                    New_Typed_Binding
                      (Name    => Id,
                       Def     => +Compute_Cases_Others_Expr (N, Guard_Map),
                       Context => Prog);
               end if;
            end;
         end loop;

         --  Add regular cases afterwards as others cases might reference them

         for C in Guard_Map.Iterate loop
            declare
               Id : constant W_Identifier_Id := Ada_To_Why_Ident.Element (C);
               N  : constant Node_Id := Ada_To_Why_Ident.Key (C);

            begin
               if Nkind (N) /= N_Aggregate then
                  Prog :=
                    +Bind_From_Mapping_In_Expr
                       (Params => Contract_VC_Params,
                        Expr   => +Prog,
                        N      => N,
                        Name   => Id,
                        Domain => EW_Prog);
               end if;
            end;
         end loop;
         return Prog;
      end Wrap_Decls_For_Guards;

      Name : constant String := Full_Name (E);

      Effects  : constant W_Effects_Id := New_Effects;
      CC_Check : W_Prog_Id := +Void; --  Checks for contract cases on entry
      EC_Check : W_Prog_Id := +Void; --  Checks for exit cases on entry
      Prog     : W_Prog_Id;
      Why_Body : W_Prog_Id;

      Result_Var : W_Prog_Id;

      Precondition_Is_Statically_False  : Boolean := False;
      Postcondition_Is_Statically_False : Boolean := False;

      --  Start of processing for Generate_VCs_For_Subprogram

   begin
      --  Reset the toplevel exceptions for exit paths

      Clear_Exceptions;

      if Is_Function_Or_Function_Type (E) then
         Result_Name :=
           New_Identifier (Name => Name & "__result", Typ => Type_Of_Node (E));
         Result_Is_Mutable := True;

         Result_Var :=
           New_Deref
             (Ada_Node => E, Right => Result_Name, Typ => Type_Of_Node (E));
      else
         Result_Var := +Void;
      end if;

      if Within_Protected_Type (E) and then Ekind (E) /= E_Subprogram_Type then
         declare
            CPT : constant Entity_Id := Containing_Protected_Type (E);
         begin
            --  The Ada_Node is important here, because that's how we detect
            --  occurrences of "self" in a term later.

            Self_Name := Concurrent_Self_Ident (CPT);
            Self_Is_Mutable := True;
         end;
      end if;

      if Get_Termination_Condition (E).Kind = Dynamic then
         Termination_Condition_Name :=
           New_Temp_Identifier
             (Base_Name => "termination_condition", Typ => EW_Bool_Type);
      end if;

      --  If E is a wrapper introduced for an implicit overriding of an
      --  inherited primitive with a dispatching result on a null extension,
      --  add a continuation to better locate the check messages.

      if Is_Wrapper_For_Dispatching_Result (E) then

         --  Go over the ancestors of E to find the first one which is not
         --  an implicit wrapper. There must be one.

         declare
            Parent_E : Entity_Id := E;
         begin
            loop
               Parent_E := Overridden_Operation (Parent_E);
               pragma Assert (Present (Parent_E));
               exit when not Is_Wrapper_For_Dispatching_Result (Parent_E);
            end loop;

            Continuation_Stack.Append
              (Continuation_Type'
                 (Ada_Node => Parent_E,
                  Message  =>
                    To_Unbounded_String
                      ("in implicit overriding of primitive function with"
                       & " dispatching result """
                       & Source_Name (E)
                       & '"')));
         end;
      end if;

      for Expr of Find_Contracts (E, Pragma_Precondition) loop
         if Nkind (Expr) in N_Expanded_Name | N_Identifier
           and then Entity (Expr) = Standard_False
         then
            Precondition_Is_Statically_False := True;

            --  Do not warn about statically False preconditions if they are
            --  disabled.

            if Original_Node (Expr) /= Expr
              and then not Exp_Util.Is_Statically_Disabled
                             (Expr, False, Include_Valid => True)
            then
               Warning_Msg_N (Warn_Precondition_Statically_False, Expr);
            end if;
         end if;
      end loop;

      for Expr of Find_Contracts (E, Pragma_Postcondition) loop
         if Nkind (Expr) in N_Expanded_Name | N_Identifier
           and then Entity (Expr) = Standard_False
         then
            Postcondition_Is_Statically_False := True;
         end if;
      end loop;

      --  If contract cases are present, generate checks for absence of
      --  run-time errors in guards, and check that contract cases are disjoint
      --  and complete. The completeness is checked in a context where the
      --  precondition is assumed. Init_Prog is set to the program up to the
      --  precondition assumption, and Prog is set to the program starting
      --  with the contract case entry checks.

      for Aggr of Find_Contracts (E, Pragma_Contract_Cases) loop
         Compute_Cases_Guard_Map (Aggr => Aggr, Guard_Map => CC_Guard_Map);

         CC_Check :=
           Compute_Cases_Entry_Checks
             (Aggr, CC_Guard_Map, Check_Complete => True);
      end loop;

      --  If exit cases are present, generate checks for absence of run-time
      --  errors in guards, and check that exit cases are disjoint.
      --  Init_Prog is set to the program up to the precondition assumption,
      --  and Prog is set to the program starting with the exit case entry
      --  checks.

      declare
         Prag : constant Node_Id := Get_Pragma (E, Pragma_Exit_Cases);
         Aggr : Node_Id;
      begin
         if Present (Prag) then
            Aggr := Expression (First (Pragma_Argument_Associations (Prag)));

            Compute_Cases_Guard_Map (Aggr => Aggr, Guard_Map => EC_Guard_Map);

            EC_Check :=
              Compute_Cases_Entry_Checks
                (Aggr, EC_Guard_Map, Check_Complete => False);
         end if;
      end;

      --  Declare global variable to hold the state of a protected object

      if Within_Protected_Type (E) and then Ekind (E) /= E_Subprogram_Type then
         Generate_Ref_For_Concurrent_Self
           (Th, Containing_Protected_Type (E), Safe_First_Sloc (E));
      end if;

      --  Declare a global variable to hold the result of a function. This is
      --  useful both for verifying the body of E when it is in SPARK, and for
      --  the warning on inconsistent postcondition when it is issued.

      if Is_Function_Or_Function_Type (E) then
         Emit
           (Th,
            New_Global_Ref_Declaration
              (Ada_Node => E,
               Name     => Result_Name,
               Labels   => Get_Counterexample_Labels (E),
               Location => No_Location,
               Ref_Type => Type_Of_Node (E)));

         --  Add a validity flag for the result if it is potentially invalid

         if Is_Potentially_Invalid (E) then
            declare
               Result_Valid : constant W_Identifier_Id :=
                 Get_Valid_Flag_For_Id (Result_Name, Etype (E));
            begin
               Emit
                 (Th,
                  New_Global_Ref_Declaration
                    (Ada_Node => E,
                     Name     => Result_Valid,
                     Labels   =>
                       Get_Counterexample_Labels (E, "'" & Initialized_Label),
                     Location => No_Location,
                     Ref_Type => Get_Typ (Result_Valid)));
            end;
         end if;

         --  If E is a traversal function returning a borrower, declare a
         --  reference borrower at end and a constant for the borrowed at end.

         if Is_Borrowing_Traversal_Function (E) then
            declare
               Brower_At_End   : constant W_Identifier_Id :=
                 Get_Brower_At_End (E);
               Borrowed_At_End : constant W_Identifier_Id :=
                 To_Local (Get_Borrowed_At_End (E));
            begin
               Emit
                 (Th,
                  New_Global_Ref_Declaration
                    (Name     => Brower_At_End,
                     Ref_Type => Get_Typ (Brower_At_End),
                     Labels   => Symbol_Sets.Empty_Set,
                     Location => No_Location));
               Emit
                 (Th,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => Borrowed_At_End,
                     Binders     => (1 .. 0 => <>),
                     Labels      => Symbol_Sets.Empty_Set,
                     Location    => No_Location,
                     Return_Type => Get_Typ (Borrowed_At_End)));
            end;
         end if;
      end if;

      --  If the subprogram is annotated with a variant but flow analysis
      --  does not see that it is recursive, raise a warning.

      if Entity_Body_In_SPARK (E)
        and then Present (Get_Pragma (E, Pragma_Subprogram_Variant))
        and then not Is_Recursive (E)
      then
         Warning_Msg_N
           (Warn_Variant_Not_Recursive,
            Get_Pragma (E, Pragma_Subprogram_Variant),
            First => True);
      end if;

      --  For expression functions, the body is not marked. Retrieve the
      --  expression directly.

      if Is_Expression_Function_Or_Completion (E)
        and then Entity_Body_In_SPARK (E)
      then
         declare
            Expr : constant Node_Id :=
              Expression (Get_Expression_Function (E));

         begin
            Why_Body :=
              Sequence
                ((1 => Check_Ceiling_Protocol (Body_Params, E),
                  2 =>
                    Transform_Simple_Return_Expression
                      (Expr, E, Type_Of_Node (E), Body_Params)));

            Why_Body := Checking_Of_Refined_Post (Why_Body);

            --  Check type invariants on subprogram's ouput, absence of runtime
            --  errors in Post and RTE + validity of contract and exit cases,
            --  and Inline_For_Proof/Logical_Equal annotation.

            Why_Body :=
              Sequence
                ((1 => Why_Body,
                  2 => Check_Invariants_Of_Outputs,
                  3 => CC_EC_And_RTE_Post,
                  4 => Check_Inline_Annotation));
         end;

      --  Regular subprogram with body in SPARK

      elsif Entity_Body_In_SPARK (E) then
         declare
            Body_N       : constant Node_Id := Get_Body (E);
            Exceptions   : constant Boolean := Has_Exceptional_Contract (E);
            Program_Exit : constant Boolean := Has_Program_Exit (E);
            Num_Handlers : constant Natural :=
              (if Exceptions then 1 else 0) + (if Program_Exit then 1 else 0);
            Handlers     : W_Handler_Array (1 .. Num_Handlers);
            Curr_Handler : Natural := 0;

         begin
            Get_Pre_Post_Pragmas (Declarations (Body_N));

            Why_Body :=
              Sequence
                ((1 =>
                    Transform_All_Pragmas
                      (Pre_Prags, "checking of pragma precondition"),
                  2 => Check_Ceiling_Protocol (Body_Params, E),
                  3 =>
                    Transform_Declarations
                      (Declarations (Body_N), Body_Params),
                  4 =>
                    Transform_Handled_Statements
                      (Handled_Statement_Sequence (Body_N), Body_Params),
                  5 =>
                    New_Raise
                      (Ada_Node => Body_N, Name => M_Main.Return_Exc)));

            --  Enclose the subprogram body in a try-block, so that return
            --  statements can be translated as raising exceptions.

            Why_Body := Try_Block (Why_Body);

            --  Check pragmas Precondition and Postcondition in the body of the
            --  subprogram as plain assertions.

            Why_Body :=
              Sequence
                ((1 => Why_Body,
                  2 =>
                    +Finalization_Actions
                       (E,
                        Local_CFG.Vertex'
                          (Kind => Local_CFG.Body_Exit, Node => E),
                        Body_Params),
                  3 =>
                    Transform_All_Pragmas
                      (Post_Prags, "checking of pragma postcondition")));

            Why_Body := Checking_Of_Refined_Post (Why_Body);

            --  Check type invariants on subprogram's output, absence of
            --  runtime errors in Post and RTE + validity of contract and exit
            --  cases, and Inline_For_Proof/Logical_Equal annotation.

            Why_Body :=
              Sequence
                ((1 => Why_Body,
                  2 => Check_Init_Of_Out_Params,
                  3 => Check_Invariants_Of_Outputs,
                  4 => CC_EC_And_RTE_Post,
                  5 => Check_Inline_Annotation));

            --  Create a handler for Ada exceptions

            if Exceptions then
               declare
                  Exc_Id  : constant W_Identifier_Id :=
                    New_Temp_Identifier
                      (Base_Name => "exc", Typ => EW_Int_Type);
                  Handler : W_Prog_Id;

               begin
                  Effects_Append_To_Raises
                    (Effects,
                     New_Raise_Effect
                       (Domain => EW_Prog, Name => M_Main.Ada_Exc));

                  --  Handle the scope exit like on normal return. Do not check
                  --  initialization for parameters with Relaxed_Initialization
                  --  as it is not mandated by Ada.
                  --  We do not need to check for absence of memory leaks in
                  --  formal parameters which are not passed by reference and
                  --  therefore discarded, a such parameters are rejected in
                  --  marking.

                  Continuation_Stack.Append
                    (Continuation_Type'
                       (Ada_Node => Body_N,
                        Message  =>
                          To_Unbounded_String ("on exceptional exit")));

                  Handler :=
                    Sequence
                      ((1 =>
                          +Finalization_Actions
                             (E,
                              Local_CFG.Vertex'
                                (Kind => Local_CFG.Body_Exit, Node => E),
                              Body_Params),
                        2 =>
                          Check_Invariants_Of_Outputs (Exceptional => True)));

                  Continuation_Stack.Delete_Last;

                  --  Check RTE + validity of exceptional cases and exit cases
                  --  on exceptional exit.

                  Handler :=
                    Sequence
                      ((1 => Handler,
                        2 =>
                          Compute_Exit_Cases_Exceptional_Exit_Checks
                            (E, EC_Guard_Map, Exc_Id),
                        3 => Check_Exceptional_Cases (Exc_Id)));

                  --  Reraise the exception

                  Handler :=
                    Sequence
                      (Handler,
                       New_Raise
                         (Ada_Node => Body_N,
                          Name     => M_Main.Ada_Exc,
                          Arg      => +Exc_Id));

                  Curr_Handler := Curr_Handler + 1;
                  Handlers (Curr_Handler) :=
                    New_Handler
                      (Name   => M_Main.Ada_Exc,
                       Arg_Id => Exc_Id,
                       Def    => Handler);

                  --  Add an artificial raise Ada_Exc to Why_Body so the
                  --  handler is not ignored when no Ada exception is raised
                  --  and the warning on dead branches will be emitted.

                  Why_Body :=
                    Sequence
                      (Left  => Why_Body,
                       Right =>
                         New_Conditional
                           (Condition => False_Prog,
                            Then_Part =>
                              New_Raise
                                (Name => M_Main.Ada_Exc,
                                 Arg  =>
                                   New_Integer_Constant (Value => Uint_0))));
               end;
            end if;

            --  Create a handler of Program_Exit

            if Program_Exit then
               declare
                  Params     : constant Transformation_Params :=
                    Contract_VC_Params;
                  Loc        : constant String := " on program exit";
                  Raise_Stmt : constant W_Prog_Id :=
                    New_Raise
                      (Ada_Node => Body_N, Name => M_Main.Program_Exit_Exc);
                  Handler    : W_Prog_Id := +Void;

               begin
                  Effects_Append_To_Raises
                    (Effects,
                     New_Raise_Effect
                       (Domain => EW_Prog, Name => M_Main.Program_Exit_Exc));

                  --  Do not havoc borrowers not check for memory leaks. It
                  --  still necessary to check potential invariants of outputs
                  --  mentioned in the program exit post of E.

                  for F of Get_Outputs_From_Program_Exit (E, E) loop
                     pragma Assert (F.Kind in Direct_Mapping | Magic_String);

                     --  Magic_String are global state with no attached
                     --  entities. As such state is translated as private in
                     --  Why3, we do not need to consider any type invariant
                     --  for it.

                     if F.Kind = Direct_Mapping then

                        --  Concurrent self should not occur here
                        pragma Assert (Is_Object (Get_Direct_Mapping_Id (F)));

                        declare
                           Obj        : constant Entity_Id :=
                             Get_Direct_Mapping_Id (F);
                           Binder     : constant Item_Type :=
                             Ada_Ent_To_Why.Element (Symbol_Table, Obj);
                           Ada_Type   : constant Entity_Id :=
                             Get_Ada_Type_From_Item (Binder);
                           Expr       : constant W_Term_Id :=
                             Reconstruct_Item
                               (Binder, Ref_Allowed => Params.Ref_Allowed);
                           Check_Info : Check_Info_Type := New_Check_Info;
                           Inv        : constant W_Pred_Id :=
                             Compute_Type_Invariant
                               (Expr   => Expr,
                                Ty     => Ada_Type,
                                Params => Params,
                                Kind   => For_Check,
                                Scop   => E);

                        begin
                           if not Is_True_Boolean (+Inv) then
                              Check_Info.Continuation.Append
                                (Continuation_Type'
                                   (Ada_Node => Obj,
                                    Message  =>
                                      To_Unbounded_String
                                        ("for " & Source_Name (Obj) & Loc)));

                              Handler :=
                                Sequence
                                  (Handler,
                                   New_Assert
                                     (Pred        =>
                                        New_VC_Pred
                                          (Ada_Node   => E,
                                           Expr       => Inv,
                                           Reason     => VC_Invariant_Check,
                                           Check_Info => Check_Info),
                                      Assert_Kind => EW_Assert));
                           end if;
                        end;
                     end if;
                  end loop;

                  --  Check RTE + validity of program exit post and exit cases
                  --  on exceptional exit.

                  declare
                     Program_Exit : constant Node_Id := Get_Program_Exit (E);
                  begin
                     if Present (Program_Exit) then
                        Handler :=
                          Sequence
                            ((1 => Handler,
                              2 =>
                                New_Ignore
                                  (Program_Exit,
                                   Warn_On_Dead_Branch
                                     (Program_Exit,
                                      Transform_Prog (Program_Exit, Params),
                                      Params.Phase,
                                      Params.Warn_On_Dead)),

                              3 =>
                                New_Assert
                                  (Ada_Node    => Program_Exit,
                                   Pred        =>
                                     New_VC_Pred
                                       (Program_Exit,
                                        Transform_Pred (Program_Exit, Params),
                                        VC_Program_Exit_Post),
                                   Assert_Kind => EW_Assert)));
                     end if;
                  end;

                  Handler :=
                    Sequence
                      (Left  => Handler,
                       Right =>
                         Compute_Exit_Cases_Simple_Checks
                           (E         => E,
                            Name      => Name_Program_Exit,
                            Guard_Map => EC_Guard_Map));

                  --  Reraise the exception

                  Handler := Sequence (Handler, Raise_Stmt);

                  Curr_Handler := Curr_Handler + 1;
                  Handlers (Curr_Handler) :=
                    New_Handler
                      (Name => M_Main.Program_Exit_Exc, Def => Handler);

                  --  Add an artificial raise Program_Exit_Exc to Why_Body so
                  --  the handler is not ignored when no calls in E exits the
                  --  program.

                  Why_Body :=
                    Sequence
                      (Left  => Why_Body,
                       Right =>
                         New_Conditional
                           (Condition => False_Prog,
                            Then_Part =>
                              New_Raise (Name => M_Main.Program_Exit_Exc)));
               end;
            end if;

            pragma Assert (Curr_Handler = Num_Handlers);

            --  Append the result of the subprogram to the body

            Why_Body := Sequence ((1 => Why_Body, 2 => Result_Var));

            --  If there are handlers, wrap the body in a try block

            if Num_Handlers > 0 then
               Why_Body :=
                 New_Try_Block (Prog => Why_Body, Handler => Handlers);
            end if;
         end;

      --  Body is not in SPARK

      else
         --  Fill the mapping for uses of 'Old to later check absence of
         --  run-time errors in these expressions.

         declare
            use type Atree.Traverse_Result;

            function Search_Old (N : Node_Id) return Atree.Traverse_Result;
            --  Search for attribute Old and enter its prefix in the map

            ----------------
            -- Search_Old --
            ----------------

            function Search_Old (N : Node_Id) return Atree.Traverse_Result is
               Dummy : W_Identifier_Id;
            begin
               if Nkind (N) = N_Attribute_Reference
                 and then Attribute_Name (N) = Name_Old
               then
                  Dummy := Name_For_Old (Prefix (N));
               end if;

               return Atree.OK;
            end Search_Old;

            procedure Search_Olds is new Traverse_More_Proc (Search_Old);

         begin
            --  Traverse all postconditions and RHS of contract cases

            for Post of Get_Postcondition_Expressions (E, Refined => False)
            loop
               Search_Olds (Post);
            end loop;

            --  For abstract functions and access-to-functions, generate a
            --  feasibility check.

            if Is_Function_Type (E)
              or else (Ekind (E) = E_Function
                       and then Is_Abstract_Subprogram (E))
            then
               Why_Body := Check_Feasibility;
            else
               Why_Body := +Void;
            end if;
         end;
      end if;

      declare
         Warn_Pre : constant W_Prog_Id :=
         --  Do not issue a check for inconsistent precondition if switch
         --  --proof-warnings is not set
           (if not Gnat2Why_Args.Proof_Warnings
              --  or if a conjunct in the precondition is statically False
              or else Precondition_Is_Statically_False
              --  or if warnings are suppressed.
              or else Opt.Warning_Mode = Opt.Suppress
            then +Void
            else Warn_On_Inconsistent_Pre);

         Warn_Post : constant W_Prog_Id :=
         --  Do not issue a check for inconsistent postcondition if switch
         --  --proof-warnings is not set
           (if not Gnat2Why_Args.Proof_Warnings
              --  or if a conjunct in the postcondition is statically False
              or else Postcondition_Is_Statically_False
              --  or if the body is in SPARK
              or else Entity_Body_In_SPARK (E)
              --  or if warnings are suppressed.
              or else Opt.Warning_Mode = Opt.Suppress
            then +Void
            else Warn_On_Inconsistent_Post);

      begin
         --  Add declarations for 'Old variables

         Prog := Sequence ((CC_Check, EC_Check, Warn_Post, Why_Body));
         Prog := Declare_Old_Variables (Prog);
         Prog := Wrap_Decls_For_CC_Guards (Prog);
         Prog := Wrap_Decls_For_EC_Guards (Prog);
         Prog := Insert_Bindings_For_Variants (E, Prog, EW_Prog, Body_Params);
         Prog := Declare_Termination_Condition (Prog);

         Prog :=
           Sequence
             ((Assume_For_Input,
               Assume_For_Output,
               RTE_Of_Pre,
               Warn_Pre,
               Assume_Or_Assert_Of_Pre,
               Prog));
      end;

      --  Assume values of constants

      Assume_Value_Of_Constants (Prog, E, Contract_VC_Params);

      --  Declare the toplevel exceptions for exit paths

      Declare_Exceptions (Th);

      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain   => EW_Prog,
            Name     => Prog_Name,
            Binders  => (1 => Unit_Param),
            Labels   => Symbol_Sets.Empty_Set,
            Location => Safe_First_Sloc (E),
            Post     => Post_As_Pred,
            Effects  => Effects,
            Def      => +Prog));

      --  cleanup

      Self_Name := Why_Empty;
      Self_Is_Mutable := False;

      if Ekind (E) = E_Function then
         Result_Name := Why_Empty;
         Result_Is_Mutable := False;
      end if;

      if Get_Termination_Condition (E).Kind = Dynamic then
         Termination_Condition_Name := Why_Empty;
      end if;

      if Is_Wrapper_For_Dispatching_Result (E) then
         Continuation_Stack.Delete_Last;
      end if;

      --  This code emits static VCs (determined by static computations inside
      --  gnat2why), so we can put this code anywhere.

      if Is_Unchecked_Conversion_Instance (E) then
         declare
            Source, Target : Node_Id;
            Src_Ty, Tar_Ty : Entity_Id;
         begin
            Get_Unchecked_Conversion_Args (E, Source, Target);
            Src_Ty := Retysp (Entity (Source));
            Tar_Ty := Retysp (Entity (Target));
            declare
               Valid       : Boolean;
               Explanation : Unbounded_String;
            begin
               Suitable_For_UC_Source (Src_Ty, Valid, Explanation);
               Emit_Static_Proof_Result
                 (Source,
                  VC_UC_Source,
                  Valid,
                  E,
                  Explanation => To_String (Explanation));

               --  If E is annotated with Potentially_Invalid, do not check
               --  that its target type has only valid values.

               Suitable_For_UC_Target_UC_Wrap
                 (Tar_Ty,
                  Valid,
                  Explanation,
                  Check_Validity => not Is_Potentially_Invalid (E));

               Emit_Static_Proof_Result
                 (Target,
                  VC_UC_Target,
                  Valid,
                  E,
                  Explanation => To_String (Explanation));

               Have_Same_Known_RM_Size (Src_Ty, Tar_Ty, Valid, Explanation);
               Emit_Static_Proof_Result
                 (E,
                  VC_UC_Same_Size,
                  Valid,
                  E,
                  Explanation => To_String (Explanation));

               Types_Compatible_Alignment (Src_Ty, Tar_Ty, Valid, Explanation);
               Emit_Static_Proof_Result
                 (E,
                  VC_UC_Align_UC,
                  Valid,
                  E,
                  Explanation => To_String (Explanation));
            end;
         end;
      end if;
   end Generate_VCs_For_Subprogram;

   --------------------------------
   -- Generate_VCs_For_Task_Type --
   --------------------------------

   procedure Generate_VCs_For_Task_Type (E : E_Task_Type_Id) is
      Name   : constant String := Full_Name (E);
      Body_N : constant Node_Id := Task_Body (E);
      Params : constant Transformation_Params := Body_Params;

      Why_Body   : W_Prog_Id;
      Priv_Decls : constant List_Id := Private_Declarations_Of_Task_Type (E);
      Vis_Decls  : constant List_Id := Visible_Declarations_Of_Task_Type (E);
      Th         : Theory_UC;
   begin
      --  We open a new theory, so that the context is fresh for this task

      Th :=
        Open_Theory
          (WF_Main,
           New_Module (Name => Name & "__task_body", File => No_Symbol),
           Comment =>
             "Module for checking absence of run-time errors and "
             & "non-termination of task body of the task type "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      Register_VC_Entity (E);

      --  Reset the toplevel exceptions for exit paths

      Clear_Exceptions;

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      --  Translate declarations and statements in the task body, if there
      --  is one.

      if Entity_Body_In_SPARK (E) then
         Why_Body :=
           Transform_Handled_Statements
             (Handled_Statement_Sequence (Body_N), Body_Params);

         Why_Body :=
           Transform_Declarations_Block
             (Declarations (Body_N), Why_Body, Body_Params);

         --  We check that the call graph starting from this task respects the
         --  ceiling priority protocol.

         Prepend (Check_Ceiling_Protocol (Params, E), Why_Body);
      else
         Why_Body := +Void;
      end if;

      --  We check any assertions and pragma (Interrupt)_Priority in the
      --  declarations of the task.

      --  Translate public and private declarations of the package

      if Present (Priv_Decls) and then Private_Spec_In_SPARK (E) then
         Why_Body :=
           Transform_Declarations_Block (Priv_Decls, Why_Body, Body_Params);
      end if;

      if Present (Vis_Decls) then
         Why_Body :=
           Transform_Declarations_Block (Vis_Decls, Why_Body, Body_Params);
      end if;

      --  We assume that objects used in the program are in range, if
      --  they are of a dynamic type.

      Prepend
        (Compute_Dynamic_Property_For_Inputs (Params => Params, E => E),
         Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Body, E, Params);

      --  Declare the toplevel exceptions for exit paths

      Declare_Exceptions (Th);

      declare
         Post : W_Pred_Id;
      begin
         if Entity_Body_In_SPARK (E) then
            Post :=
              New_VC_Pred
                (Ada_Node => E,
                 Expr     => False_Pred,
                 Reason   => VC_Task_Termination);
         else
            Post := Why_Empty;
         end if;
         Emit
           (Th,
            Why.Gen.Binders.New_Function_Decl
              (Domain   => EW_Prog,
               Name     => Def_Name,
               Binders  => (1 => Unit_Param),
               Location => Safe_First_Sloc (E),
               Labels   => Symbol_Sets.Empty_Set,
               Post     => Post,
               Def      => +Why_Body));
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      Close_Theory (Th, Kind => VC_Generation_Theory, Defined_Entity => E);

   end Generate_VCs_For_Task_Type;

   -----------------------------
   -- Get_Location_For_Aspect --
   -----------------------------

   function Get_Location_For_Aspect
     (E         : Entity_Id;
      Kind      : Pragma_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Node_Id is
   begin
      --  In the case of a No_Return Subprogram, there is no real location for
      --  the postcondition; simply return the subprogram entity node.

      if Kind = Pragma_Postcondition
        and then Is_Subprogram (E)
        and then No_Return (E)
      then
         return E;
      end if;

      --  Pre- and postconditions are stored in reverse order in
      --  Pre_Post_Conditions, hence retrieve the last assertion in this
      --  list to get the first one in source code.

      declare
         L : constant Node_Lists.List :=
           Find_Contracts
             (E, Kind, Classwide => Classwide, Inherited => Inherited);
      begin
         if L.Is_Empty then
            return Empty;
         else
            return L.Last_Element;
         end if;
      end;
   end Get_Location_For_Aspect;

   ------------------------------
   -- Generate_Axiom_For_Lemma --
   ------------------------------

   procedure Generate_Axiom_For_Lemma
     (E                     : E_Procedure_Id;
      Specialization_Module : Symbol := No_Symbol;
      More_Reads            : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
   is
      Fun     : constant Entity_Id :=
        Retrieve_Automatic_Instantiation_Annotation (E);
      Binders : Item_Array := Compute_Binders (E, EW_Term, More_Reads);
      Params  : Transformation_Params;
      Pre     : W_Pred_Id;
      Post    : W_Pred_Id;
      Th      : Theory_UC;

      function Is_Disabled return Boolean;
      --  Return True if there is a conjunct in the precondition of E which is
      --  known to be False at compile time.

      -----------------
      -- Is_Disabled --
      -----------------

      function Is_Disabled return Boolean is

         function Is_Statically_False (N : N_Subexpr_Id) return Boolean;
         --  Return True if there is a conjunct in N which is known to be False
         --  at compile time.

         -------------------------
         -- Is_Statically_False --
         -------------------------

         function Is_Statically_False (N : N_Subexpr_Id) return Boolean is
         begin
            case Nkind (N) is
               when N_And_Then | N_Op_And =>
                  return
                    Is_Statically_False (Left_Opnd (N))
                    or else Is_Statically_False (Right_Opnd (N));

               when others                =>
                  return
                    Compile_Time_Known_Value (N)
                    and then not Is_True (Expr_Value (N));
            end case;
         end Is_Statically_False;

      begin
         --  Loop over the list of preconditions of E to see if one is
         --  statically false.

         return
           (for some Pre_N of Find_Contracts (E, Pragma_Precondition) =>
              Is_Statically_False (Pre_N));
      end Is_Disabled;

   begin
      --  Do not emit an axiom if E has a precondition which evaluates
      --  statically to False. This optimization is useful for functional
      --  containers which have specific axioms for the handling of
      --  equivalence which can be removed at instantiation using a boolean
      --  formal parameter.

      if Is_Disabled then
         return;
      end if;

      Params := (Logic_Params with delta Old_Policy => Ignore);

      Th :=
        Open_Theory
          (WF_Context,
           (if Specialization_Module = No_Symbol
            then E_Module (E, Lemma_Axiom)
            else M_Lemma_HO_Specializations (E) (Specialization_Module)),
           Comment =>
             "Module for declaring an axiom for the post condition"
             & " of the lemma procedure "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Localize_Binders (Binders);
      Push_Binders_To_Symbol_Table (Binders);

      Pre := +Compute_Spec (Params, E, Pragma_Precondition, EW_Pred);
      Post :=
        +New_And_Expr
           (Left   => +Compute_Spec (Params, E, Pragma_Postcondition, EW_Pred),
            Right  => +Compute_CC_And_EC_Postcondition (Params, E),
            Domain => EW_Pred);

      declare
         Guard : constant W_Pred_Id :=
           +New_And_Then_Expr
              (Left   => +Compute_Guard_Formula (Binders, Params),
               Right  =>
                 +Compute_Type_Invariants_For_Subprogram (E, Params, True),
               Domain => EW_Pred);
         --  Dynamic invariant / type invariants of the inputs

      begin
         --  We generate:
         --  forall binders. Guard /\ Pre -> Post

         Emit
           (Th,
            New_Guarded_Axiom
              (Name    => NID (Short_Name (E) & "__" & Post_Axiom),
               Binders => To_Binder_Array (Binders),
               Pre     => New_And_Pred (Left => Guard, Right => Pre),
               Def     => Post,
               Dep     =>
                 New_Axiom_Dep
                   (Name =>
                      Logic_Function_Name
                        (Fun, Specialization_Module => Specialization_Module),
                    Kind => EW_Axdep_Func)));
      end;

      Close_Theory (Th, Kind => Definition_Theory);
      Record_Extra_Dependency
        (Defining_Module =>
           (if Specialization_Module = No_Symbol
            then E_Module (Fun, Logic_Function_Decl)
            else M_HO_Specializations (Fun) (Specialization_Module).Module),
         Axiom_Module    => Th.Module);

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      Register_Automatically_Instanciated_Lemma (E);
   end Generate_Axiom_For_Lemma;

   -----------------------------
   -- Generate_Axiom_For_Post --
   -----------------------------

   procedure Generate_Axiom_For_Post
     (Th                    : Theory_UC;
      Dispatch_Th           : Theory_UC := Empty_Theory;
      Refined_Th            : Theory_UC := Empty_Theory;
      E                     : Callable_Kind_Id;
      Spec_Binders          : Binder_Array := (1 .. 0 => <>);
      Spec_Guard            : W_Pred_Id := True_Pred;
      Specialization_Module : Symbol := No_Symbol;
      More_Reads            : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
   is
      Needs_Validity_Wrapper : constant Boolean := Is_Potentially_Invalid (E);
      Logic_Func_Binders     : constant Item_Array :=
        Compute_Binders (E, EW_Term, More_Reads);
      Params                 : Transformation_Params;
      Pre                    : W_Pred_Id;
      Post                   : W_Pred_Id;
      Dispatch_Pre           : W_Pred_Id := Why_Empty;
      Dispatch_Post          : W_Pred_Id := Why_Empty;
      Refined_Post           : W_Pred_Id := Why_Empty;
      Why_Type               : W_Type_Id := Why_Empty;

   begin
      Params := (Logic_Params with delta Old_Policy => Ignore);

      if Is_Function_Or_Function_Type (E) then
         if Needs_Validity_Wrapper then
            Why_Type := Validity_Wrapper_Type (E);
         else
            Why_Type := Type_Of_Node (E);
         end if;
      end if;

      --  Do not generate an axiom for the postcondition of volatile functions,
      --  protected subprograms and functions with side effects.

      if not Is_Function_Or_Function_Type (E)
        or else Is_Function_With_Side_Effects (E)
        or else Has_Pragma_Volatile_Function (E)
      then
         return;
      end if;

      pragma Assert (Is_Function_Type (E) or else Has_Post_Axiom (E));

      --  For recursive functions, we store the axiom in a different module,
      --  so that we can make sure that it cannot be used to prove the function
      --  itself.

      if Ekind (E) = E_Function and then Proof_Module_Cyclic (E) then

         --  Raise a warning about missing (implicit) contract on recursive
         --  calls.

         declare
            Has_Explicit_Contracts : constant Boolean :=
              Has_Contracts (E, Pragma_Postcondition)
              or else Has_Contracts (E, Pragma_Contract_Cases);
            Has_Implicit_Contracts : constant Boolean :=
              Type_Needs_Dynamic_Invariant (Etype (E));
         begin

            if Has_Implicit_Contracts or else Has_Explicit_Contracts then
               declare
                  String_For_Implicit : constant String :=
                    (if Has_Explicit_Contracts then "" else "implicit ");
                  String_For_Rec      : constant String :=
                    (if Is_Recursive (E)
                     then "recursive calls"
                     else "implicit recursive calls");
               begin
                  Warning_Msg_N
                    (Warn_Contracts_Recursive,
                     E,
                     Create_N
                       (Warn_Contracts_Recursive,
                        Names => [String_For_Implicit, String_For_Rec]));
               end;
            end if;
         end;

         Register_Proof_Cyclic_Function (E);
      end if;

      --  If the function has a postcondition and is not mutually recursive
      --  then generate an axiom:
      --  axiom def_axiom:
      --     forall args [f (args)]. pre (args) ->
      --           let result = f (args) in post (args)

      --  We fill the map of parameters, so that in the Pre and Post, we use
      --  local names of the parameters, instead of the global names.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Push_Binders_To_Symbol_Table (Logic_Func_Binders);

      Pre := +Compute_Spec (Params, E, Pragma_Precondition, EW_Pred);
      Post :=
        +New_And_Expr
           (Left   => +Compute_Spec (Params, E, Pragma_Postcondition, EW_Pred),
            Right  => +Compute_CC_And_EC_Postcondition (Params, E),
            Domain => EW_Pred);

      if Is_Dispatching_Operation (E)
        and then not Is_Hidden_Dispatching_Operation (E)
      then
         Dispatch_Pre :=
           Get_Dispatching_Call_Contract (Params, E, Pragma_Precondition);
         Dispatch_Post :=
           Get_Dispatching_Call_Contract (Params, E, Pragma_Postcondition);

         --  Classwide post serves as post if no specific postcondition is
         --  given.

         if not Has_Contracts (E, Pragma_Postcondition)
           and then not Has_Contracts (E, Pragma_Contract_Cases)
         then
            Post := Get_LSP_Contract (Params, E, Pragma_Postcondition);
         end if;

         --  Classwide pre serves as pre if no specific postcondition is given

         if not Has_Contracts (E, Pragma_Precondition) then
            Pre := Get_LSP_Contract (Params, E, Pragma_Precondition);
         end if;
      end if;

      --  For higher order specializations, we do not take into account
      --  refined postcondition if any.

      if Entity_Body_In_SPARK (E)
        and then Has_Contracts (E, Pragma_Refined_Post)
        and then Specialization_Module = No_Symbol
      then
         Refined_Post :=
           +Compute_Spec (Params, E, Pragma_Refined_Post, EW_Pred);
      end if;

      declare
         Result_Id         : constant W_Identifier_Id :=
           +New_Result_Ident (Why_Type);
         Result_Value      : constant W_Term_Id :=
           (if Needs_Validity_Wrapper
            then
              +New_Function_Valid_Value_Access (Fun => E, Name => +Result_Id)
            else +Result_Id);
         Result_Valid_Flag : constant W_Term_Id :=
           (if Needs_Validity_Wrapper
            then +New_Function_Valid_Flag_Access (Fun => E, Name => +Result_Id)
            else Why_Empty);
         Logic_Why_Binders : constant Binder_Array :=
           To_Binder_Array (Logic_Func_Binders);
         Guard             : constant W_Pred_Id :=
           +New_And_Then_Expr
              (Left   => +Compute_Guard_Formula (Logic_Func_Binders, Params),
               Right  =>
                 +Compute_Type_Invariants_For_Subprogram (E, Params, True),
               Domain => EW_Pred);
         --  Dynamic invariant / type invariants of the inputs

         Dynamic_Prop_Result : constant W_Pred_Id :=
           +New_And_Then_Expr
              (Left   =>
                 +Compute_Dynamic_Inv_And_Initialization
                    (Expr           => Result_Value,
                     Ty             => Etype (E),
                     Only_Var       => False_Term,
                     All_Global_Inv =>
                       Include_All_Global_Invariants_For_Subp (E),
                     Valid          => Result_Valid_Flag,
                     Params         => Params),
               Right  =>
                 +Compute_Type_Invariants_For_Subprogram (E, Params, False),
               Domain => EW_Pred);
         --  Dynamic invariant / type invariants of the result

         procedure Emit_Post_Axiom
           (Th        : Theory_UC;
            Suffix    : String;
            Selector  : Selection_Kind;
            Pre, Post : W_Pred_Id);
         --  Emit the post_axiom with the given axiom_suffix, pre and
         --  post for the Why identifier associated to E with Selector.

         ---------------------
         -- Emit_Post_Axiom --
         ---------------------

         procedure Emit_Post_Axiom
           (Th        : Theory_UC;
            Suffix    : String;
            Selector  : Selection_Kind;
            Pre, Post : W_Pred_Id)
         is
            Id           : constant W_Identifier_Id :=
              Logic_Function_Name
                (E,
                 Selector_Name         => Selector,
                 Specialization_Module => Specialization_Module);
            Tag_B        : constant Binder_Array :=
              (if Selector = Dispatch
               then (1 => Tag_Binder)
               else (1 .. 0 => <>));
            Binders      : constant Binder_Array :=
              Tag_B & Spec_Binders & Logic_Why_Binders;
            Pred_Binders : constant Binder_Array :=
              Binder_Type'
                (Ada_Node => Empty,
                 B_Name   => +Result_Id,
                 B_Ent    => Null_Entity_Name,
                 Mutable  => False,
                 Labels   => <>)
              & Binders;
            Tag_Comp     : constant W_Pred_Id :=
              (if Is_Tagged_Type (Retysp (Etype (E)))
                 and then not Is_Class_Wide_Type (Etype (E))
               then
                 +New_Comparison
                    (Symbol => Why_Eq,
                     Left   =>
                       New_Tag_Access
                         (Domain => EW_Term,
                          Name   => +Result_Value,
                          Ty     => Retysp (Etype (E))),
                     Right  =>
                       (if Ekind (E) = E_Function
                          and then Selector = Dispatch
                          and then Has_Controlling_Result (E)
                        then +Tag_Binder.B_Name
                        else +E_Symb (Etype (E), WNE_Tag)),
                     Domain => EW_Pred)
               else True_Pred);
            --  For functions with tagged results, assume the value of the tag
            --  of the result.

            Complete_Post : constant W_Pred_Id :=
              New_And_Pred
                (Conjuncts =>
                   (1 =>
                      (if Is_Borrowing_Traversal_Function (E)
                       then
                         Wrap_Post_Of_Traversal
                           (E      => E,
                            Post   => Post,
                            Args   =>
                              Get_Args_From_Binders
                                (Logic_Why_Binders, Ref_Allowed => False),
                            Params => Params)

                       --  If the function returns a validity wrapper,
                       --  introduce bindings for the value part and the
                       --  validity flag of the result.

                       elsif Needs_Validity_Wrapper
                       then Wrap_Post_Of_Potentially_Invalid (E, Post)
                       else Post),
                    2 => Dynamic_Prop_Result,
                    3 => Tag_Comp));
            Guarded_Post  : constant W_Pred_Id :=
              (if not Use_Guard_For_Function (E)
               then Complete_Post
               else
                 New_Conditional
                   (Condition =>
                      +New_Call
                         (Domain  => EW_Pred,
                          Name    =>
                            Guard_Predicate_Name
                              (E,
                               Selector_Name         => Selector,
                               Specialization_Module => Specialization_Module),
                          Binders => Pred_Binders),
                    Then_Part => Complete_Post));
            Call          : constant W_Expr_Id :=
              New_Call (Domain => EW_Term, Name => Id, Binders => Binders);
            Def           : constant W_Pred_Id :=
              +New_Typed_Binding
                 (Ada_Node => Empty,
                  Domain   => EW_Pred,
                  Name     => +Result_Id,
                  Def      => Call,
                  Context  => +Guarded_Post);
            Dep           : constant W_Axiom_Dep_Id :=
              New_Axiom_Dep (Name => Id, Kind => EW_Axdep_Func);
         begin
            --  If we have a specific guard, generate:
            --  forall spec_binders [spec_guard].
            --    spec_guard <->
            --      (forall binders [call]. Guard /\ Pre -> Def)

            if not Is_True_Boolean (+Spec_Guard) then
               Emit
                 (Th,
                  New_Guarded_Axiom
                    (Name     => NID (Short_Name (E) & "__" & Suffix),
                     Binders  => Spec_Binders,
                     Triggers =>
                       New_Triggers
                         (Triggers =>
                            (1 => New_Trigger (Terms => (1 => +Spec_Guard)))),
                     Def      =>
                       New_Connection
                         (Left  => +Spec_Guard,
                          Op    => EW_Equivalent,
                          Right =>
                            +New_Universal_Quantif
                               (Binders  => Tag_B & Logic_Why_Binders,
                                Triggers =>
                                  New_Triggers
                                    (Triggers =>
                                       (1 =>
                                          New_Trigger (Terms => (1 => Call)))),
                                Pred     =>
                                  New_Conditional
                                    (Condition =>
                                       +New_And_Expr
                                          (Left   => +Guard,
                                           Right  => +Pre,
                                           Domain => EW_Pred),
                                     Then_Part => +Def))),
                     Dep      => Dep));

            --  Otherwise, generate:
            --  forall binders [call]. Guard /\ Pre -> Def

            else
               Emit
                 (Th,
                  New_Guarded_Axiom
                    (Name     => NID (Short_Name (E) & "__" & Suffix),
                     Binders  => Binders,
                     Triggers =>
                       New_Triggers
                         (Triggers =>
                            (1 => New_Trigger (Terms => (1 => Call)))),
                     Pre      =>
                       +New_And_Expr
                          (Left => +Guard, Right => +Pre, Domain => EW_Pred),
                     Def      => +Def,
                     Dep      => Dep));
            end if;
         end Emit_Post_Axiom;

      begin
         --  Do not emit an axiom for E if it is inlined for proof

         if No (Retrieve_Inline_Annotation (E)) then
            Emit_Post_Axiom (Th, Post_Axiom, Why.Inter.Standard, Pre, Post);
            Register_Dependency_For_Soundness (Th.Module, E);
         end if;

         if Is_Dispatching_Operation (E)
           and then not Is_Hidden_Dispatching_Operation (E)
         then
            pragma
              Assert (Present (Dispatch_Pre) and then Present (Dispatch_Post));
            Emit_Post_Axiom
              (Dispatch_Th,
               Post_Dispatch_Axiom,
               Dispatch,
               New_And_Pred
                 (Left  =>
                    Compute_Guard_For_Dispatch
                      (Subp    => E,
                       Binders => Logic_Func_Binders,
                       W_Tag   => +Tag_Binder.B_Name,
                       Params  => Params),
                  Right => Dispatch_Pre),
               Dispatch_Post);
            Register_Dependency_For_Soundness (Dispatch_Th.Module, E);
         end if;

         --  For higher order specializations, we do not take into account
         --  refined postcondition if any.

         if Entity_Body_In_SPARK (E)
           and then Has_Contracts (E, Pragma_Refined_Post)
           and then Specialization_Module = No_Symbol
         then
            pragma Assert (Present (Refined_Post));
            Emit_Post_Axiom
              (Refined_Th, Post_Refine_Axiom, Refine, Pre, Refined_Post);
            Register_Dependency_For_Soundness (Refined_Th.Module, E);

            --  E needs special handling for visibility

            Register_Function_With_Refinement (E);
         end if;
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
   end Generate_Axiom_For_Post;

   --------------------------------------------
   -- Generate_Dispatch_Compatibility_Axioms --
   --------------------------------------------

   procedure Generate_Dispatch_Compatibility_Axioms
     (Th : Theory_UC; E : Entity_Id)
   is
      Ty            : constant Entity_Id :=
        Base_Retysp (SPARK_Util.Subprograms.Find_Dispatching_Type (E));
      Descendants   : Node_Sets.Set := Get_Descendant_Set (Ty);
      Anc_Binders   : constant Binder_Array :=
        (if Ekind (E) = E_Function
         then To_Binder_Array (Compute_Binders (E, EW_Term))
         else Procedure_Logic_Binders (E));
      Dispatch_Args : W_Expr_Array (1 .. Anc_Binders'Length + 1);
      Anc_Id        : constant W_Identifier_Id :=
        (if Ekind (E) = E_Function
         then To_Why_Id (E, Domain => EW_Term, Selector => Dispatch)
         else To_Local (E_Symb (E, WNE_Specific_Post)));
      Anc_Ty        : constant W_Type_Id :=
        (if Ekind (E) = E_Function then Type_Of_Node (E) else EW_Bool_Type);
      Descendant_E  : Entity_Id;

   begin
      --  The arguments of the dispatching call are the binders from
      --  Anc_Binders with a hole at the beginning to store the (specific)
      --  value of the tag.

      for I in Anc_Binders'Range loop
         Dispatch_Args (I + 1) := +Anc_Binders (I).B_Name;
      end loop;

      Descendants.Include (Ty);

      for Descendant of Descendants loop
         Descendant_E := Corresponding_Primitive (E, Descendant);

         if Entity_In_SPARK (Descendant_E) then
            Dispatch_Args (1) := +E_Symb (Descendant, WNE_Tag);

            declare
               Desc_Id  : constant W_Identifier_Id :=
                 To_Why_Id (Descendant_E, Domain => EW_Term);
               Anc_Call : constant W_Expr_Id :=
                 New_Call
                   (Domain => EW_Term,
                    Name   => Anc_Id,
                    Args   => Dispatch_Args,
                    Typ    => Anc_Ty);
            begin
               --  If Descendant_E has not the same globals as E, there should
               --  be an error in flow analysis. Do not attempt to generate a
               --  compatibility axiom.

               if not Same_Globals (E, Descendant_E) then
                  return;
               end if;

               --  If E is a function, emit:
               --    for all x1 ... [<E>__dispatch Descendant.tag x1 ...].
               --       <E>__dispatch Descendant.tag x1 ... =
               --            <Descendant.E> X1 ..

               if Ekind (E) = E_Function then

                  --  Do not generate compatibility axioms for volatile
                  --  functions and functions with side effects as they do
                  --  not have any associated logic function.
                  --  ??? They could maybe be handled like procedures, using a
                  --  specific_post predicate.

                  if Is_Function_With_Side_Effects (E)
                    or else Has_Pragma_Volatile_Function (E)
                  then
                     return;
                  end if;

                  declare
                     Desc_Ty      : constant W_Type_Id :=
                       Type_Of_Node (Descendant_E);
                     Desc_Binders : constant Binder_Array :=
                       To_Binder_Array
                         (Compute_Binders (Descendant_E, EW_Term));
                     Desc_Args    : W_Expr_Array (1 .. Desc_Binders'Length);
                     Guard        : constant W_Pred_Id :=
                       (if not Use_Guard_For_Function (E)
                        then True_Pred
                        else
                          New_Call
                            (Name => E_Symb (E, WNE_Dispatch_Func_Guard),
                             Args => Anc_Call & Dispatch_Args,
                             Typ  => EW_Bool_Type));
                     Call         : W_Term_Id;
                     --  The axiom is protected by the dispatching post
                     --  predicate of E.

                  begin
                     pragma
                       Assert
                         (Anc_Binders'First = Desc_Binders'First
                            and Anc_Binders'Last = Desc_Binders'Last);

                     --  Conversions are needed for controlling parameters

                     for I in Desc_Binders'Range loop
                        Desc_Args (I) :=
                          Insert_Simple_Conversion
                            (Domain => EW_Term,
                             Expr   => +Anc_Binders (I).B_Name,
                             To     => Get_Typ (Desc_Binders (I).B_Name));
                     end loop;

                     Call :=
                       +New_Function_Call
                          (Domain => EW_Term,
                           Subp   => Descendant_E,
                           Name   => Desc_Id,
                           Args   => Desc_Args,
                           Check  => False,
                           Typ    => Desc_Ty);

                     --  If Descendant is a derived type with a null extension,
                     --  Descendant_E can be inherited even if it has a
                     --  controlling result. An overriding is generated in the
                     --  frontend so this case should never occur.

                     pragma
                       Assert
                         (if Has_Controlling_Result (Descendant_E)
                            then
                              Base_Retysp (Descendant)
                              = Base_Retysp (Etype (Descendant_E)));

                     Emit
                       (Th,
                        New_Guarded_Axiom
                          (Ada_Node => Empty,
                           Name     =>
                             NID
                               (Full_Name (Descendant) & "__" & Compat_Axiom),
                           Binders  => Anc_Binders,
                           Triggers =>
                             New_Triggers
                               (Triggers =>
                                  (1 =>
                                     New_Trigger (Terms => (1 => Anc_Call)))),
                           Pre      => Guard,
                           Def      =>
                             +New_Comparison
                                (Symbol => Why_Eq,

                                 --  Conversion is needed for controlling
                                 --  result

                                 Left   =>
                                   Insert_Simple_Conversion
                                     (Domain => EW_Term,
                                      Expr   => +Call,
                                      To     => Anc_Ty),
                                 Right  => Anc_Call,
                                 Domain => EW_Term),
                           Dep      =>
                             New_Axiom_Dep
                               (Name => Anc_Id, Kind => EW_Axdep_Func)));
                  end;

               --  If E is a procedure, emit:
               --    for all x1 ... [<E>__spec_post Descendant.tag x1 ...].
               --       <E>__spec_post Descendant.tag x1 ... ->
               --           <specific post of Descendant>

               else
                  pragma Assert (Ekind (E) = E_Procedure);

                  declare
                     New_Binders : Item_Array :=
                       Compute_Raw_Binders (E)
                       & Compute_Binders_For_Effects (E);
                     Old_Binders : Item_Array := New_Binders;
                     Desc_Params : Item_Array :=
                       Compute_Raw_Binders (Descendant_E);
                     Desc_Post   : W_Pred_Id;
                     Old_Parts   : Node_Sets.Set;
                     Params      : Transformation_Params;

                  begin
                     Localize_Binders (New_Binders);
                     Localize_Binders (Old_Binders, "old");

                     Ada_Ent_To_Why.Push_Scope (Symbol_Table);

                     --  Controlling parameters may need a conversion. We need
                     --  a binder in non-split form for them. For others, we
                     --  can use the ancestor names directly.

                     for I in Desc_Params'Range loop
                        declare
                           Ada_Node : constant Node_Id :=
                             Get_Ada_Node_From_Item (Desc_Params (I));
                           Typ      : constant W_Type_Id :=
                             Get_Why_Type_From_Item (Desc_Params (I));

                        begin
                           pragma Assert (Present (Ada_Node));

                           if Get_Ada_Node (+Typ) = Descendant then
                              Desc_Params (I) :=
                                (Regular,
                                 Local    => True,
                                 Init     => <>,
                                 Is_Moved => <>,
                                 Valid    => <>,
                                 Main     =>
                                   (B_Name   =>
                                      New_Temp_Identifier
                                        (Base_Name => Short_Name (Ada_Node),
                                         Typ       => Typ),
                                    B_Ent    => Null_Entity_Name,
                                    Mutable  => False,
                                    Ada_Node => Ada_Node,
                                    Labels   => <>));

                              Ada_Ent_To_Why.Insert
                                (Symbol_Table, Ada_Node, Desc_Params (I));
                           else
                              Ada_Ent_To_Why.Insert
                                (Symbol_Table, Ada_Node, New_Binders (I));
                           end if;
                        end;
                     end loop;

                     --  Store new binders in the Symbol_Table, so that in the
                     --  Post of Descendant, we use local names of parameters
                     --  and effects, instead of the global names.

                     Push_Binders_To_Symbol_Table (New_Binders);

                     Params := (Logic_Params with delta Old_Policy => Use_Map);

                     --  Translate the specific postcondition of Descendant_E

                     if No_Return (Descendant_E) then
                        Desc_Post := False_Pred;
                     else
                        Desc_Post :=
                          +New_And_Expr
                             (Left   =>
                                +Compute_Spec
                                   (Params,
                                    Descendant_E,
                                    Pragma_Postcondition,
                                    EW_Pred),
                              Right  =>
                                +Compute_CC_And_EC_Postcondition
                                   (Params, Descendant_E),
                              Domain => EW_Pred);

                        if not Has_Contracts
                                 (Descendant_E, Pragma_Postcondition)
                          and then not Has_Contracts
                                         (Descendant_E, Pragma_Contract_Cases)
                        then
                           Desc_Post :=
                             Get_LSP_Contract
                               (Params, Descendant_E, Pragma_Postcondition);
                        end if;

                        --  Collect references to Old in Old_Parts

                        Collect_Old_For_Subprogram
                          (Descendant_E,
                           Old_Parts,
                           Exclude_Classwide => False);
                     end if;

                     Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

                     Ada_Ent_To_Why.Push_Scope (Symbol_Table);

                     --  Insert bindings for contolling parameters of
                     --  Descendant_E and update entities which should be used
                     --  for other parameters.

                     for I in Desc_Params'Range loop
                        declare
                           Ada_Node : constant Node_Id :=
                             Get_Ada_Node_From_Item (Desc_Params (I));
                           Typ      : constant W_Type_Id :=
                             Get_Why_Type_From_Item (Desc_Params (I));

                        begin
                           if Get_Ada_Node (+Typ) = Descendant then
                              Desc_Post :=
                                New_Typed_Binding
                                  (Name    => Desc_Params (I).Main.B_Name,
                                   Def     =>
                                     Insert_Simple_Conversion
                                       (Expr =>
                                          Reconstruct_Item
                                            (New_Binders (I),
                                             Ref_Allowed => False),
                                        To   =>
                                          Get_Typ
                                            (Desc_Params (I).Main.B_Name)),
                                   Context => Desc_Post);
                              Ada_Ent_To_Why.Insert
                                (Symbol_Table, Ada_Node, Desc_Params (I));
                           else
                              Ada_Ent_To_Why.Insert
                                (Symbol_Table, Ada_Node, Old_Binders (I));
                           end if;
                        end;
                     end loop;

                     --  To translate expressions used in old attributes, we
                     --  need to store values in the pre state in the symbol
                     --  table.

                     Push_Binders_To_Symbol_Table (Old_Binders);

                     --  Inner references to Old should be ignored

                     Params.Old_Policy := Ignore;

                     --  Insert let bindings for old expressions

                     Desc_Post :=
                       +Bind_From_Mapping_In_Expr
                          (Params => Params,
                           Map    => Map_For_Old,
                           Expr   => +Desc_Post,
                           Domain => EW_Term,
                           Subset => Old_Parts);

                     --  Insert bindings for contolling parameters of
                     --  Descendant_E

                     for I in Desc_Params'Range loop
                        declare
                           Typ : constant W_Type_Id :=
                             Get_Why_Type_From_Item (Desc_Params (I));

                        begin
                           if Get_Ada_Node (+Typ) = Descendant then
                              Desc_Post :=
                                New_Typed_Binding
                                  (Name    => Desc_Params (I).Main.B_Name,
                                   Def     =>
                                     Insert_Simple_Conversion
                                       (Expr =>
                                          Reconstruct_Item
                                            (Old_Binders (I),
                                             Ref_Allowed => False),
                                        To   =>
                                          Get_Typ
                                            (Desc_Params (I).Main.B_Name)),
                                   Context => +Desc_Post);
                           end if;
                        end;
                     end loop;

                     Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

                     Emit
                       (Th,
                        New_Guarded_Axiom
                          (Ada_Node => Empty,
                           Name     =>
                             NID
                               (Full_Name (Descendant) & "__" & Compat_Axiom),
                           Binders  => Anc_Binders,
                           Triggers =>
                             New_Triggers
                               (Triggers =>
                                  (1 =>
                                     New_Trigger (Terms => (1 => Anc_Call)))),
                           Pre      => +Anc_Call,
                           Def      => Desc_Post));
                  end;
               end if;
            end;
         end if;
      end loop;
   end Generate_Dispatch_Compatibility_Axioms;

   ------------------------------------
   -- Generate_Subprogram_Completion --
   ------------------------------------

   procedure Generate_Subprogram_Completion (E : Callable_Kind_Id) is
      Dispatch_Th      : Theory_UC := Empty_Theory;
      Dispatch_Post_Th : Theory_UC := Empty_Theory;
      Post_Axiom_Th    : Theory_UC;
      Refined_Post_Th  : Theory_UC := Empty_Theory;
      Program_Th       : Theory_UC;
   begin
      Program_Th :=
        Open_Theory
          (WF_Context,
           E_Module (E, Program_Function_Decl),
           Comment =>
             "Module for declaring a program function for "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);
      Post_Axiom_Th :=
        Open_Theory
          (WF_Context,
           E_Module (E, Fun_Post_Axiom),
           Comment =>
             "Module for defining a post axiom for "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  If E is a dispatching operation, create a theory for the axioms of
      --  its dispatching version.

      if Is_Dispatching_Operation (E)
        and then not Is_Hidden_Dispatching_Operation (E)
        and then not Is_Predicate_Function (E)
      then
         Dispatch_Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Dispatch_Axiom),
              Comment =>
                "Module for declaring a program function (and compatibility "
                & "axioms) for the dispatching variant of "
                & """"
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
         Dispatch_Post_Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Dispatch_Post_Axiom),
              Comment =>
                "Module for declaring a post axiom for the dispatching variant"
                & " of """
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
      end if;

      if Entity_Body_In_SPARK (E)
        and then Has_Contracts (E, Pragma_Refined_Post)
      then
         Refined_Post_Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Refined_Post_Axiom),
              Comment =>
                "Module for declaring an axiom for the refined postcondition"
                & " of """
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
      end if;

      declare
         Use_Result_Name : constant Boolean := Ekind (E) = E_Function;
         --  Store the result identifier in Result_Name. If the result of
         --  the function is potentially invalid, use a temporary as the
         --  function returns a validity wrapper.

      begin
         if Use_Result_Name then
            Result_Name :=
              (if Is_Potentially_Invalid (E)
               then
                 New_Temp_Identifier
                   (Base_Name => "result", Typ => Type_Of_Node (E))
               else New_Result_Ident (Type_Of_Node (E)));
            Result_Is_Mutable := False;
         end if;

         if Within_Protected_Type (E) then
            Self_Name := Concurrent_Self_Ident (Containing_Protected_Type (E));
            Self_Is_Mutable := Ekind (E) /= E_Function;
         end if;

         Generate_Subprogram_Program_Fun
           (Program_Th,
            Dispatch_Th,
            E,
            To_Why_Id (E, Domain => EW_Prog, Local => True));

         Generate_Axiom_For_Post
           (Post_Axiom_Th, Dispatch_Post_Th, Refined_Post_Th, E);

         if Is_Dispatching_Operation (E)
           and then not Is_Hidden_Dispatching_Operation (E)
           and then not Is_Predicate_Function (E)
         then
            Generate_Dispatch_Compatibility_Axioms (Dispatch_Th, E);
         end if;

         if Within_Protected_Type (E) then
            Self_Name := Why_Empty;
            Self_Is_Mutable := False;
         end if;

         if Use_Result_Name then
            Result_Name := Why_Empty;
            Result_Is_Mutable := False;
         end if;
      end;

      Close_Theory (Post_Axiom_Th, Kind => Axiom_Theory, Defined_Entity => E);

      Close_Theory (Program_Th, Kind => Definition_Theory);

      --  Close the dispatching axiom module if it is not empty and add an
      --  extra dependency to the dispatching definition module.

      if Dispatch_Th /= Empty_Theory then

         --  Compatibility axioms are always sound, so we do not need a
         --  dependency for soundness here.

         Close_Theory (Dispatch_Th, Kind => Definition_Theory);
         Record_Extra_Dependency
           (Defining_Module => E_Module (E, Dispatch),
            Axiom_Module    => Dispatch_Th.Module);

         Close_Theory (Dispatch_Post_Th, Kind => Definition_Theory);
         Record_Extra_Dependency
           (Defining_Module => E_Module (E, Dispatch),
            Axiom_Module    => Dispatch_Post_Th.Module);
      end if;

      --  Close the refined post axiom module if it is not empty

      if Refined_Post_Th /= Empty_Theory then
         Close_Theory (Refined_Post_Th, Kind => Definition_Theory);
      end if;

      --  If E is a lemma procedure with an Automatic_Instantiation annotation,
      --  generate a lemma for the postcondition of E.

      if Has_Automatic_Instantiation_Annotation (E) then
         Generate_Axiom_For_Lemma (E);
      end if;
   end Generate_Subprogram_Completion;

   -------------------------------------
   -- Generate_Subprogram_Program_Fun --
   -------------------------------------

   procedure Generate_Subprogram_Program_Fun
     (Th                    : Theory_UC;
      Dispatch_Th           : Theory_UC := Empty_Theory;
      E                     : Callable_Kind_Id;
      Prog_Id               : W_Identifier_Id;
      Spec_Binders          : Binder_Array := Binder_Array'(1 .. 0 => <>);
      Specialization_Module : Symbol := No_Symbol;
      More_Reads            : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
   is
      Needs_Validity_Wrapper : constant Boolean := Is_Potentially_Invalid (E);
      Func_Binders           : constant Item_Array :=
        Compute_Binders (E, EW_Prog, More_Reads);
      Func_Why_Binders       : constant Binder_Array :=
        To_Binder_Array (Func_Binders);
      Params                 : Transformation_Params;
      Effects                : W_Effects_Id;
      Pre                    : W_Pred_Id;
      Post                   : W_Pred_Id;
      Dispatch_Pre           : W_Pred_Id := Why_Empty;
      Dispatch_Post          : W_Pred_Id := Why_Empty;
      Refined_Post           : W_Pred_Id := Why_Empty;
      Why_Type               : W_Type_Id := Why_Empty;

   begin
      Params := (Logic_Params with delta Ref_Allowed => True);

      --  We fill the map of parameters, so that in the Pre and Post, we use
      --  local names of the parameters, instead of the global names.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      for Binder of Func_Binders loop
         declare
            A : constant Node_Id := Get_Ada_Node_From_Item (Binder);
         begin

            --  If the Ada_Node is Empty, it's not an interesting binder (e.g.
            --  void_param).

            if Present (A) then
               Ada_Ent_To_Why.Insert (Symbol_Table, A, Binder);
            end if;
         end;
      end loop;

      Effects := Compute_Effects (E, More_Reads => More_Reads);

      --  Potentially add raised exceptions to the effects

      if Has_Exceptional_Contract (E) then
         declare
            Exc_Id : constant W_Identifier_Id :=
              New_Temp_Identifier (Base_Name => "exc", Typ => EW_Int_Type);
         begin
            Effects_Append_To_Raises
              (Effects,
               New_Raise_Effect
                 (Domain => EW_Prog,
                  Name   => M_Main.Ada_Exc,
                  Arg_Id => Exc_Id,
                  Post   =>
                    New_And_Pred
                      (Compute_Exceptional_Cases_Postcondition
                         (Params, E, Exc_Id),
                       Compute_Exit_Cases_Exceptional_Post
                         (Params, E, Exc_Id))));
         end;
      end if;

      --  Potentially add program exit to the effects

      if Has_Program_Exit (E) then
         Effects_Append_To_Raises
           (Effects,
            New_Raise_Effect
              (Domain => EW_Prog,
               Name   => M_Main.Program_Exit_Exc,
               Post   =>
                 New_And_Pred
                   (Compute_Program_Exit_Postcondition (Params, E),
                    Compute_Exit_Cases_Simple_Post
                      (Params, E, Name_Program_Exit))));
      end if;

      Pre := Get_Static_Call_Contract (Params, E, Pragma_Precondition);

      if Is_Dispatching_Operation (E)
        and then not Is_Hidden_Dispatching_Operation (E)
      then
         Dispatch_Pre :=
           Get_Dispatching_Call_Contract (Params, E, Pragma_Precondition);
      end if;

      --  For a procedure annotated with No_Return, the postcondition at call
      --  site should be "False", so that it is known in the caller that the
      --  call does not return.

      if Is_Subprogram (E) and then No_Return (E) then
         Post := False_Pred;

         if Is_Dispatching_Operation (E)
           and then not Is_Hidden_Dispatching_Operation (E)
         then
            Dispatch_Post := False_Pred;
         end if;

         if Entity_Body_In_SPARK (E)
           and then Has_Contracts (E, Pragma_Refined_Post)
         then
            Refined_Post := False_Pred;
         end if;

      --  In other cases, the postcondition is extracted from the subprogram
      --  contract.

      else
         Post :=
           +New_And_Expr
              (Left   =>
                 +Compute_Spec (Params, E, Pragma_Postcondition, EW_Pred),
               Right  => +Compute_CC_And_EC_Postcondition (Params, E),
               Domain => EW_Pred);

         if Is_Dispatching_Operation (E)
           and then not Is_Hidden_Dispatching_Operation (E)
         then
            Dispatch_Post :=
              Get_Dispatching_Call_Contract (Params, E, Pragma_Postcondition);

            if not Has_Contracts (E, Pragma_Postcondition)
              and then not Has_Contracts (E, Pragma_Contract_Cases)
            then
               Post := Get_LSP_Contract (Params, E, Pragma_Postcondition);
            end if;
         end if;

         --  For higher order specializations, we do not take into account
         --  refined postcondition if any.

         if Ekind (E) /= E_Subprogram_Type
           and then Entity_Body_In_SPARK (E)
           and then Has_Contracts (E, Pragma_Refined_Post)
           and then Specialization_Module = No_Symbol
         then
            Refined_Post :=
              Get_Static_Call_Contract (Params, E, Pragma_Refined_Post);

         --  If E is an expression function, it might have a refinement even if
         --  it does not have a refine postcondition. In this case, use the
         --  normal post for the refine version.

         elsif Has_Refinement (E) then
            Refined_Post := Post;
         end if;
      end if;

      if Is_Function_Or_Function_Type (E) then

         Why_Type :=
           (if Needs_Validity_Wrapper
            then Validity_Wrapper_Type (E)
            else Type_Of_Node (E));

         declare
            Logic_Func_Args     : constant W_Expr_Array :=
              Get_Args_From_Binders (Spec_Binders, Ref_Allowed => True)
              & Compute_Args (E, Func_Why_Binders, More_Reads);
            Result_Id           : constant W_Identifier_Id :=
              New_Result_Ident (Why_Type);
            Result_Value        : constant W_Term_Id :=
              (if Needs_Validity_Wrapper
               then
                 +New_Function_Valid_Value_Access
                    (Fun => E, Name => +Result_Id)
               else +Result_Id);
            Result_Valid_Flag   : constant W_Term_Id :=
              (if Needs_Validity_Wrapper
               then
                 +New_Function_Valid_Flag_Access (Fun => E, Name => +Result_Id)
               else Why_Empty);
            Dynamic_Prop_Result : constant W_Pred_Id :=
              +New_And_Then_Expr
                 (Left   =>
                    +Compute_Dynamic_Inv_And_Initialization
                       (Expr           => Result_Value,
                        Ty             => Etype (E),
                        Only_Var       => False_Term,
                        All_Global_Inv =>
                          Include_All_Global_Invariants_For_Subp (E),
                        Valid          => Result_Valid_Flag,
                        Params         => Params),
                  Right  =>
                    +Compute_Type_Invariants_For_Subprogram (E, Params, False),
                  Domain => EW_Pred);
            --  Dynamic invariant and type invariant of the result

            Volatile_State : constant W_Identifier_Id :=
              New_Identifier (Domain => EW_Term, Name => "volatile__effect");

            function Create_Function_Decl
              (Prog_Id  : W_Identifier_Id;
               Selector : Selection_Kind;
               Pre      : W_Pred_Id;
               Post     : W_Pred_Id;
               Effects  : W_Effects_Id) return W_Declaration_Id;
            --  create the function declaration with the given Logic_Id,
            --  Prog_Id, Pre and Post.

            --------------------------
            -- Create_Function_Decl --
            --------------------------

            function Create_Function_Decl
              (Prog_Id  : W_Identifier_Id;
               Selector : Selection_Kind;
               Pre      : W_Pred_Id;
               Post     : W_Pred_Id;
               Effects  : W_Effects_Id) return W_Declaration_Id
            is
               --  A tag is needed for dispatching calls, to account for the
               --  fact that the call might be dispatching on its result, which
               --  is not passed as regular argument to the call.
               Need_Tag : constant Boolean := Selector = Dispatch;

               --  Each function has in its postcondition that its result is
               --  equal to the application of the corresponding logic function
               --  to the same arguments.

               Param_Post : W_Pred_Id :=
                 +New_And_Expr
                    (Left   => +Dynamic_Prop_Result,
                     Right  =>

                     --  If the function is a borrowing traversal function,
                     --  bind the identifier for the pledge of the result. Also
                     --  assume that the pledge holds right after the call.

                        (if Is_Borrowing_Traversal_Function (E)
                         then
                           +Wrap_Post_Of_Traversal
                              (E, Post, Logic_Func_Args, Params)

                         --  If the function returns a validity wrapper,
                         --  introduce bindings for the value part and the
                         --  validity flag of the result.

                         elsif Needs_Validity_Wrapper
                         then +Wrap_Post_Of_Potentially_Invalid (E, Post)
                         else +Post),
                     Domain => EW_Pred);
               Tag_Arg    : constant W_Expr_Array :=
                 (if Need_Tag
                  then (1 => +Tag_Binder.B_Name)
                  else (1 .. 0 => <>));
               Tag_B      : constant Binder_Array :=
                 (if Need_Tag then (1 => Tag_Binder) else (1 .. 0 => <>));
               Pred_Args  : constant W_Expr_Array :=
                 +Result_Id & Tag_Arg & Logic_Func_Args;

            begin
               --  A volatile function has an effect, as well as a function
               --  with side effects, and should not have the special
               --  postcondition which says its result is equal to the
               --  logic function.

               if not Is_Function_With_Side_Effects (E)
                 and then not Has_Pragma_Volatile_Function (E)
               then
                  declare
                     --  Add attribute RAC_Assume to the predicate N. This is
                     --  used to assume equality with function results and
                     --  function guards during RAC, because their validity
                     --  cannot be derived.
                     function RAC_Assume (N : W_Pred_Id) return W_Pred_Id
                     is (New_Label
                           (Labels =>
                              Symbol_Sets.To_Set (NID (RAC_Assume_Label)),
                            Def    => N));

                     Logic_Id   : constant W_Identifier_Id :=
                       Logic_Function_Name
                         (E, Selector, Specialization_Module);
                     Pred_Id    : constant W_Identifier_Id :=
                       Guard_Predicate_Name
                         (E, Selector, Specialization_Module);
                     Args       : constant W_Expr_Array :=
                       Tag_Arg & Logic_Func_Args;
                     Logic_Call : constant W_Pred_Id :=
                       RAC_Assume
                         (New_Call
                            (Name => Why_Eq,
                             Args =>
                               (+Result_Id,
                                New_Call
                                  (Domain => EW_Term,
                                   Name   => Logic_Id,
                                   Args   => Args))));
                     Pred_Call  : constant W_Pred_Id :=
                       (if Use_Guard_For_Function (E)
                        then
                          RAC_Assume
                            (New_Call (Name => Pred_Id, Args => Pred_Args))
                        else True_Pred);

                  begin
                     Param_Post :=
                       New_And_Pred
                         ((1 => Logic_Call, 2 => Pred_Call, 3 => Param_Post));
                  end;
               end if;

               --  For functions returning specific tagged type, the result has
               --  the expected tag.

               if Is_Tagged_Type (Retysp (Etype (E)))
                 and then not Is_Class_Wide_Type (Etype (E))
               then
                  Param_Post :=
                    New_And_Pred
                      ((1 => Param_Post,
                        2 =>
                          +New_Comparison
                             (Symbol => Why_Eq,
                              Left   =>
                                New_Tag_Access
                                  (Domain => EW_Term,
                                   Name   => +Result_Value,
                                   Ty     => Retysp (Etype (E))),
                              Right  =>
                                (if Ekind (E) = E_Function
                                   and then Selector = Dispatch
                                   and then Has_Controlling_Result (E)
                                 then +Tag_Binder.B_Name
                                 else +E_Symb (Etype (E), WNE_Tag)),
                              Domain => EW_Pred)));
               end if;

               return
                 New_Function_Decl
                   (Domain      => EW_Prog,
                    Name        => Prog_Id,
                    Binders     => Tag_B & Spec_Binders & Func_Why_Binders,
                    Return_Type => Why_Type,
                    Labels      => Symbol_Sets.Empty_Set,
                    Location    => No_Location,
                    Effects     => Effects,
                    Pre         => Pre,
                    Post        => Param_Post);
            end Create_Function_Decl;

         begin
            --  For a volatile function that is not protected, we need to
            --  generate a dummy effect. Protected functions are OK, they
            --  already have their own state (the protected object).

            if Has_Pragma_Volatile_Function (E) then
               Effects_Append_To_Writes (Effects, Volatile_State);

               Emit
                 (Th,
                  New_Global_Ref_Declaration
                    (Ada_Node => E,
                     Labels   => Symbol_Sets.Empty_Set,
                     Location => No_Location,
                     Name     => Volatile_State,
                     Ref_Type => EW_Private_Type));
            end if;

            --  If the expression function definition might be hidden, generate
            --  a program function without the body as a post.

            if Expr_Fun_Might_Be_Hidden (E) then
               Emit
                 (Th,
                  New_Namespace_Declaration
                    (Name         => NID (To_String (WNE_Hidden_Module)),
                     Declarations =>
                       (1 =>
                          Create_Function_Decl
                            (Prog_Id  => Prog_Id,
                             Selector => Why.Inter.Standard,
                             Pre      => Pre,
                             Post     => Post,
                             Effects  => Effects))));
            end if;

            --  If E is an expression function, add its body to its
            --  postcondition. For higher order specializations, the expression
            --  function body is not taken into account.

            if Is_Expression_Function_Or_Completion (E)
              and then Entity_Body_Compatible_With_SPARK (E)
              and then not Has_Pragma_Volatile_Function (E)
              and then Specialization_Module = No_Symbol
            then
               declare
                  Domain     : constant EW_Domain :=
                    (if Is_Standard_Boolean_Type (Etype (E))
                     then EW_Pred
                     else EW_Term);
                  Expr_Fun_N : constant Node_Id := Get_Expression_Function (E);
                  Expr_Body  : W_Expr_Id;
                  Eq_Expr    : W_Pred_Id;

                  --  Handling of potentially invalid values
                  Valid_Flag : W_Expr_Id;
                  Context    : Ref_Context;

               begin
                  if Needs_Validity_Wrapper then
                     Expr_Body :=
                       Transform_Potentially_Invalid_Expr
                         (Expr          => Expression (Expr_Fun_N),
                          Expected_Type => Type_Of_Node (E),
                          Domain        => Domain,
                          Params        => Params,
                          Context       => Context,
                          Valid_Flag    => Valid_Flag);

                     Expr_Body :=
                       New_Function_Validity_Wrapper_Value
                         (Fun        => E,
                          Valid_Flag => Valid_Flag,
                          Value      => Expr_Body);

                     Eq_Expr :=
                       New_Comparison
                         (Symbol => Why_Eq,
                          Left   => +Result_Id,
                          Right  => +Expr_Body);

                     Eq_Expr :=
                       +Bindings_For_Ref_Context
                          (Expr    => +Eq_Expr,
                           Context => Context,
                           Domain  => EW_Pred);
                  else
                     Expr_Body :=
                       Transform_Expr
                         (Expression (Expr_Fun_N),
                          Expected_Type => Why_Type,
                          Domain        => Domain,
                          Params        => Params);

                     Eq_Expr :=
                       New_Call
                         (Name => Why_Eq, Args => (+Result_Id, +Expr_Body));
                  end if;

                  if Entity_Body_In_SPARK (E) and then Has_Refinement (E) then
                     Refined_Post :=
                       +New_And_Expr (+Eq_Expr, +Refined_Post, EW_Pred);
                  else
                     Post := +New_And_Expr (+Eq_Expr, +Post, EW_Pred);
                  end if;
               end;
            end if;

            Emit
              (Th,
               Create_Function_Decl
                 (Prog_Id  => Prog_Id,
                  Selector => Why.Inter.Standard,
                  Pre      => Pre,
                  Post     => Post,
                  Effects  => Effects));

            if Is_Dispatching_Operation (E)
              and then not Is_Hidden_Dispatching_Operation (E)
            then
               Emit
                 (Dispatch_Th,
                  Create_Function_Decl
                    (Prog_Id  => Prog_Id,
                     Selector => Dispatch,
                     Pre      => Dispatch_Pre,
                     Post     => Dispatch_Post,
                     Effects  => Effects));
            end if;

            --  For higher order specializations, we do not take into account
            --  refined postcondition if any.

            if Entity_Body_In_SPARK (E)
              and then Has_Refinement (E)
              and then Specialization_Module = No_Symbol
            then
               Emit
                 (Th,
                  New_Namespace_Declaration
                    (Name         => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 =>
                          Create_Function_Decl
                            (Prog_Id  => Prog_Id,
                             Selector => Refine,
                             Pre      => Pre,
                             Post     => Refined_Post,
                             Effects  => Effects))));
            end if;
         end;

      else
         pragma
           Assert (Ekind (E) in E_Entry | E_Procedure | E_Subprogram_Type);

         declare
            Dynamic_Prop_Effects : constant W_Pred_Id :=
              New_And_Pred
                ((1 => Compute_Dynamic_Property_For_Effects (E, Params),
                  2 =>
                    Compute_Type_Invariants_For_Subprogram (E, Params, False),
                  3 => Preservation_Of_Access_Parameters (E, Params)));
            --  Dynamic invariant and type invariant for outputs of the
            --  procedure, as well as preservation of discriminants and
            --  bounds of access parameters.

         begin
            Post :=
              +New_And_Expr
                 (Left   => +Post,
                  Right  => +Dynamic_Prop_Effects,
                  Domain => EW_Pred);

            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Id,
                  Binders     => Spec_Binders & Func_Why_Binders,
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Unit_Type,
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => Post));

            if Is_Dispatching_Operation (E)
              and then not Is_Hidden_Dispatching_Operation (E)
            then

               --  For dispatching procedure, declare a new predicate symbol
               --  standing for the specific postcondition which applies to the
               --  dispatching tag and add it to the dispatching postcondition
               --  of E.

               declare
                  Spec_Post_Id : constant W_Identifier_Id :=
                    New_Identifier
                      (Domain => EW_Pred,
                       Symb   => NID (Short_Name (E) & "__" & Specific_Post),
                       Typ    => EW_Bool_Type);
                  --  Name of the predicate function for E's specific post

                  Spec_Post_Call : W_Pred_Id := True_Pred;

               begin
                  --  Construct the Pred_Id corresponding to the call to
                  --  Spec_Post_Id in the postcondition of E.

                  declare
                     Logic_Binders : constant Item_Array :=
                       Compute_Raw_Binders (E)
                       & Compute_Binders_For_Effects (E);
                     --  Binders for parameters and effects of E

                     Dispatch_Param  : constant Entity_Id :=
                       Find_Dispatching_Parameter (E);
                     Dispatch_Binder : constant Item_Type :=
                       Ada_Ent_To_Why.Element (Symbol_Table, Dispatch_Param);
                     Dispatch_Typ    : constant W_Type_Id :=
                       Get_Why_Type_From_Item (Dispatch_Binder);
                     Tag_Arg         : constant W_Expr_Id :=
                       (case Dispatch_Binder.Kind is
                          when Regular =>
                            New_Tag_Access
                              (Domain => EW_Term,
                               Name   =>
                                 (if Dispatch_Binder.Main.Mutable
                                  then
                                    New_Deref
                                      (Right => Dispatch_Binder.Main.B_Name,
                                       Typ   => Dispatch_Typ)
                                  else +Dispatch_Binder.Main.B_Name),
                               Ty     => Get_Ada_Node (+Dispatch_Typ)),
                          when DRecord => +Dispatch_Binder.Tag.Id,
                          when others  => raise Program_Error);
                     --  Tag used for dispatching in calls to E

                     Logic_Args : W_Expr_Array :=
                       Tag_Arg
                       & Get_Args_From_Binders
                           (To_Binder_Array
                              (Logic_Binders, Keep_Const => Local_Only)
                            & To_Binder_Array
                                (Logic_Binders, Keep_Const => Erase),
                            Ref_Allowed => True);
                     --  Arguments of the predicate function for E's
                     --  specific post:
                     --    - the specific tag
                     --    - values of parameters and binders after the call
                     --    - old values of mutable parts of binders

                     First_Old : constant Natural :=
                       2
                       + Item_Array_Length
                           (Logic_Binders, Keep_Const => Local_Only);

                  begin
                     --  Insert calls to old on expressions for the old
                     --  values of parameters and global variables.

                     for I in First_Old .. Logic_Args'Last loop
                        Logic_Args (I) := New_Old (Logic_Args (I), EW_Term);
                     end loop;

                     Spec_Post_Call :=
                       New_Call
                         (Name => Spec_Post_Id,
                          Args => Logic_Args,
                          Typ  => EW_Bool_Type);
                  end;

                  Emit
                    (Dispatch_Th,
                     New_Function_Decl
                       (Domain      => EW_Pred,
                        Name        => Spec_Post_Id,
                        Binders     =>
                          Tag_Binder & Procedure_Logic_Binders (E),
                        Location    => No_Location,
                        Labels      => Symbol_Sets.Empty_Set,
                        Return_Type => EW_Bool_Type));
                  Emit
                    (Dispatch_Th,
                     New_Function_Decl
                       (Domain      => EW_Prog,
                        Name        => Prog_Id,
                        Binders     => Spec_Binders & Func_Why_Binders,
                        Location    => No_Location,
                        Labels      => Symbol_Sets.Empty_Set,
                        Return_Type => EW_Unit_Type,
                        Effects     => Effects,
                        Pre         => Dispatch_Pre,
                        Post        =>
                          New_And_Pred
                            (Conjuncts =>
                               (1 => Dispatch_Post,
                                2 => Dynamic_Prop_Effects,
                                3 => Spec_Post_Call))));
               end;
            end if;

            --  For higher order specializations, we do not take into account
            --  refined postcondition if any.

            if Entity_Body_In_SPARK (E)
              and then Has_Contracts (E, Pragma_Refined_Post)
              and then Specialization_Module = No_Symbol
            then
               Emit
                 (Th,
                  New_Namespace_Declaration
                    (Name         => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 =>
                          New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Spec_Binders & Func_Why_Binders,
                             Location    => No_Location,
                             Labels      => Symbol_Sets.Empty_Set,
                             Return_Type => EW_Unit_Type,
                             Effects     => Effects,
                             Pre         => Pre,
                             Post        =>
                               +New_And_Expr
                                  (Left   => +Refined_Post,
                                   Right  => +Dynamic_Prop_Effects,
                                   Domain => EW_Pred)))));
            end if;
         end;
      end if;

      --  Generate a check_subprogram_variants function. It has the same
      --  parameters as E as well as previous variant values. Its
      --  precondition checks that E's variants progress.
      --
      --  For a subprogram:
      --
      --    Y : Unsigned_8;
      --    procedure Proc (X : in out Integer) with
      --      Variant => (Decreases => X + 1, Increases => Y - 1);
      --
      --  we generate:
      --
      --    val proc__check_subprogram_variants
      --        (x : int ref) (variant_1 : int) (variant_2 : bv_8) : unit
      --      requires { x + 1 < variant_1 \/
      --                 x + 1 = variant_1 /\ y - 1 > variant_2 }

      if Present (Get_Pragma (E, Pragma_Subprogram_Variant)) then
         declare
            Variant_Check  : constant W_Identifier_Id :=
              (if Specialization_Module = No_Symbol
               then E_Symb (E, WNE_Check_Subprogram_Variants)
               else
                 M_HO_Specializations (E) (Specialization_Module).Variant_Id);
            Variants_Ids   : constant W_Expr_Array := Get_Variants_Ids (E);
            Variants_Exprs : constant W_Expr_Array (Variants_Ids'Range) :=
              Get_Variants_Exprs (E, Domain => EW_Term, Params => Params);
            Binders        : Binder_Array :=
              Binder_Array'(Variants_Ids'Range => <>)
              & Spec_Binders
              & Func_Why_Binders;
            Variants       : constant Node_Id :=
              Get_Pragma (E, Pragma_Subprogram_Variant);
            Aggr           : constant Node_Id :=
              Expression (First (Pragma_Argument_Associations (Variants)));
            Variant        : Node_Id := Last (Component_Associations (Aggr));
            Checks         : W_Pred_Id := False_Pred;

         begin
            --  Iterate through the list of variants to complete Binders and
            --  generate Checks.

            for Count in reverse Variants_Ids'Range loop
               declare
                  WTyp : constant W_Type_Id :=
                    Get_Typ (W_Identifier_Id'(+Variants_Ids (Count)));
                  Cmp  : constant W_Identifier_Id :=
                    (if Chars (First (Choice_List (Variant))) = Name_Decreases
                     then
                       (if Why_Type_Is_BitVector (WTyp)
                        then MF_BVs (WTyp).Ult
                        else Int_Infix_Lt)
                     else
                       (if Why_Type_Is_BitVector (WTyp)
                        then MF_BVs (WTyp).Ugt
                        else Int_Infix_Gt));
               begin
                  Binders (Count) :=
                    Binder_Type'
                      (B_Ent  => Why_Empty,
                       B_Name => +Variants_Ids (Count),
                       others => <>);

                  --  <expression> (</>) variant__i or else
                  --    <expression> = variant__i and then Checks

                  Checks :=
                    +New_Or_Else_Expr
                       (Left   =>
                          New_Comparison
                            (Symbol => Cmp,
                             Left   => Variants_Exprs (Count),
                             Right  => Variants_Ids (Count),
                             Domain => EW_Pred),
                        Right  =>
                          New_And_Then_Expr
                            (Left   =>
                               New_Comparison
                                 (Symbol => Why_Eq,
                                  Left   => Variants_Exprs (Count),
                                  Right  => Variants_Ids (Count),
                                  Domain => EW_Pred),
                             Right  => +Checks,
                             Domain => EW_Pred),
                        Domain => EW_Pred);
               end;
               Prev (Variant);
            end loop;

            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => To_Local (Variant_Check),
                  Binders     => Binders,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => EW_Unit_Type,
                  Pre         => Checks));
         end;
      end if;

      --  Generate a check_termination_condition function. It has the same
      --  parameters as E. Its precondition checks that E's termination
      --  condition evaluates to True.
      --
      --  For a subprogram:
      --
      --    Y : Unsigned_8;
      --    procedure Proc (X : in out Integer) with
      --      Always_Terminates => X = Y;
      --
      --  we generate:
      --
      --    val proc__check_termination_condition (x : int ref) : unit
      --      requires { x = y }

      declare
         Cond : constant Termination_Condition :=
           Get_Termination_Condition (E);
      begin
         if Cond.Kind = Dynamic then

            --  Procedures with a dynamic termination condition cannot be
            --  specialized.

            pragma Assert (Specialization_Module = No_Symbol);

            declare
               P_Name : constant W_Identifier_Id :=
                 E_Symb (E, WNE_Check_Termination_Condition);

            begin
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Prog,
                     Name        => To_Local (P_Name),
                     Binders     => Spec_Binders & Func_Why_Binders,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => EW_Unit_Type,
                     Pre         => Transform_Pred (Cond.Condition, Params)));
            end;
         end if;
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
   end Generate_Subprogram_Program_Fun;

   --------------------
   -- Get_Logic_Args --
   --------------------

   function Get_Logic_Args
     (E           : Entity_Id;
      Ref_Allowed : Boolean;
      More_Reads  : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return W_Expr_Array
   is
      Effect_Binders : constant Item_Array :=
        Compute_Binders_For_Effects (E, More_Reads => More_Reads);
      Logic_Binders  : constant Binder_Array :=
        To_Binder_Array (Effect_Binders);

   begin
      return Get_Args_From_Binders (Logic_Binders, Ref_Allowed);
   end Get_Logic_Args;

   ----------------------------------
   -- Insert_Bindings_For_Variants --
   ----------------------------------

   function Insert_Bindings_For_Variants
     (E      : Entity_Id;
      Prog   : W_Prog_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Prog_Id
   is
      Variants_Ids   : constant W_Expr_Array := Get_Variants_Ids (E);
      Variants_Exprs : constant W_Expr_Array (Variants_Ids'Range) :=
        Get_Variants_Exprs (E, Domain, Params);
      W_Ty           : constant W_Type_Id := Get_Type (+Prog);
      T              : W_Prog_Id := Prog;
   begin
      for Count in Variants_Ids'Range loop
         T :=
           New_Binding
             (Name    => +Variants_Ids (Count),
              Def     => +Variants_Exprs (Count),
              Context => T,
              Typ     => W_Ty);
      end loop;
      return T;
   end Insert_Bindings_For_Variants;

   ----------------------
   -- Insert_Exception --
   ----------------------

   procedure Insert_Exception (Exc : W_Name_Id) is
   begin
      Subprogram_Exceptions.Insert (+Exc);
   end Insert_Exception;

   ----------------------
   -- Need_Self_Binder --
   ----------------------

   function Need_Self_Binder (E : Callable_Kind_Id) return Boolean
   is (Is_Subprogram_Or_Entry (E) and then Within_Protected_Type (E));

   ---------------------------------------
   -- Preservation_Of_Access_Parameters --
   ---------------------------------------

   function Preservation_Of_Access_Parameters
     (E : Entity_Id; Params : Transformation_Params) return W_Pred_Id
   is
      Func_Why_Binders : constant Item_Array := Compute_Binders (E, EW_Prog);
      Result           : W_Pred_Id := True_Pred;

   begin
      pragma Assert (Params.Old_Policy = As_Old);

      for I in Func_Why_Binders'Range loop
         if Item_Is_Mutable (Func_Why_Binders (I)) then
            declare
               E : constant Entity_Id :=
                 Get_Ada_Node_From_Item (Func_Why_Binders (I));

            begin

               if Ekind (E) = E_In_Parameter
                 and then Is_Access_Type (Retysp (Etype (E)))
               then

                  declare
                     Expr            : constant W_Term_Id :=
                       +Transform_Identifier
                          (Params => Params,
                           Expr   => E,
                           Ent    => E,
                           Domain => EW_Term);
                     Old_Expr        : constant W_Term_Id :=
                       +New_Old (+Expr, EW_Term);
                     Ty              : constant Type_Kind_Id :=
                       Retysp (Etype (E));
                     Des_Ty          : constant Type_Kind_Id :=
                       Retysp (Directly_Designated_Type (Ty));
                     Preserved_Parts : constant W_Pred_Id :=
                       New_Equality_Of_Preserved_Parts
                         (Ty    => Des_Ty,
                          Expr1 =>
                            New_Pointer_Value_Access
                              (E => Ty, Name => Old_Expr),
                          Expr2 =>
                            New_Pointer_Value_Access (E => Ty, Name => Expr));

                  begin
                     if not Is_True_Boolean (+Preserved_Parts) then
                        Result :=
                          New_And_Pred
                            (Left  => Result,
                             Right =>
                               New_Conditional
                                 (Condition =>
                                    New_Not
                                      (Right =>
                                         Pred_Of_Boolean_Term
                                           (New_Pointer_Is_Null_Access
                                              (Ty, Expr))),
                                  Then_Part => Preserved_Parts));
                     end if;
                  end;
               end if;
            end;
         end if;
      end loop;

      return Result;
   end Preservation_Of_Access_Parameters;

   -----------------------------
   -- Procedure_Logic_Binders --
   -----------------------------

   function Procedure_Logic_Binders (E : Entity_Id) return Binder_Array is
      Logic_Binders : constant Item_Array :=
        Compute_Raw_Binders (E) & Compute_Binders_For_Effects (E);
      New_Binders   : Item_Array := Logic_Binders;
      Old_Binders   : Item_Array := Logic_Binders;
   begin
      Localize_Binders (New_Binders);
      Localize_Binders (Old_Binders, "old");
      return
        To_Binder_Array (New_Binders, Keep_Const => Local_Only)
        & To_Binder_Array (Old_Binders, Keep_Const => Erase);
   end Procedure_Logic_Binders;

   ------------------
   -- Same_Globals --
   ------------------

   function Same_Globals (Subp_1, Subp_2 : Callable_Kind_Id) return Boolean is
      use type Flow_Types.Flow_Id_Sets.Set;

      Subp_1_Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
      Subp_2_Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
      Subp_1_Write_Ids : Flow_Types.Flow_Id_Sets.Set;
      Subp_2_Write_Ids : Flow_Types.Flow_Id_Sets.Set;

   begin
      --  Collect global variables potentially read and written

      Flow_Utility.Get_Proof_Globals
        (Subprogram      => Subp_1,
         Reads           => Subp_1_Read_Ids,
         Writes          => Subp_1_Write_Ids,
         Erase_Constants => True);

      Flow_Utility.Get_Proof_Globals
        (Subprogram      => Subp_2,
         Reads           => Subp_2_Read_Ids,
         Writes          => Subp_2_Write_Ids,
         Erase_Constants => True);

      return
        Subp_1_Read_Ids = Subp_2_Read_Ids
        and then Subp_1_Write_Ids = Subp_2_Write_Ids;
   end Same_Globals;

   ----------------------------------------
   -- Translate_Expression_Function_Body --
   ----------------------------------------

   procedure Translate_Expression_Function_Body (E : E_Function_Id) is
      Expr : constant Node_Id := Expression (Get_Expression_Function (E));

      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Flat_Binders       : constant Binder_Array :=
        To_Binder_Array (Logic_Func_Binders);

      Logic_Id     : constant W_Identifier_Id :=
        To_Why_Id
          (E,
           Domain   => EW_Term,
           Local    => False,
           Selector => Why.Inter.Standard);
      Pred_Name    : constant Why_Name_Enum := WNE_Func_Guard;
      Result_Id    : constant W_Identifier_Id :=
        New_Result_Ident (Type_Of_Node (E));
      Pred_Binders : constant Binder_Array :=
        Binder_Type'
          (Ada_Node => Empty,
           B_Name   => +Result_Id,
           B_Ent    => Null_Entity_Name,
           Mutable  => False,
           Labels   => <>)
        & Flat_Binders;
      Func_Guard   : constant W_Pred_Id :=
        (if not Use_Guard_For_Function (E) or else not Proof_Module_Cyclic (E)
         then True_Pred
         else
           New_Typed_Binding
             (Name    => Result_Id,
              Def     =>
                +New_Call
                   (Domain  => EW_Pred,
                    Name    => Logic_Id,
                    Binders => Flat_Binders,
                    Typ     => EW_Bool_Type),
              Context =>
                +New_Call
                   (Domain  => EW_Pred,
                    Name    => E_Symb (E, Pred_Name),
                    Binders => Pred_Binders,
                    Typ     => EW_Bool_Type)));

      Params            : Transformation_Params;
      Post_Axiom_Th     : Theory_UC;
      Expr_Fun_Axiom_Th : Theory_UC;
      Program_Th        : Theory_UC;
      Dispatch_Th       : Theory_UC := Empty_Theory;
      Dispatch_Post_Th  : Theory_UC := Empty_Theory;
      Refined_Post_Th   : Theory_UC := Empty_Theory;

   begin
      Program_Th :=
        Open_Theory
          (WF_Context,
           E_Module (E, Program_Function_Decl),
           Comment =>
             "Module giving a program function for the expression function "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);
      Post_Axiom_Th :=
        Open_Theory
          (WF_Context,
           E_Module (E, Fun_Post_Axiom),
           Comment =>
             "Module giving a post axiom for the expression function "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  If E is a dispatching operation, create a theory for the axioms of
      --  its dispatching version.

      if Is_Dispatching_Operation (E)
        and then not Is_Hidden_Dispatching_Operation (E)
      then
         Dispatch_Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Dispatch_Axiom),
              Comment =>
                "Module for declaring a program function and compatibility "
                & "axioms for the dispatching variant of "
                & """"
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
         Dispatch_Post_Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Dispatch_Post_Axiom),
              Comment =>
                "Module for declaring a post axiom for the dispatching variant"
                & " of """
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
      end if;

      if Entity_Body_In_SPARK (E)
        and then Has_Contracts (E, Pragma_Refined_Post)
      then
         Refined_Post_Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Refined_Post_Axiom),
              Comment =>
                "Module for declaring an axiom for the refined postcondition"
                & " of """
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
      end if;

      --  Store an appropriate value for the result identifier in Result_Name.
      --  If the result of the function is potentially invalid, use a temporary
      --  as the function returns a validity wrapper.

      Result_Name :=
        (if Is_Potentially_Invalid (E)
         then
           New_Temp_Identifier (Base_Name => "result", Typ => Type_Of_Node (E))
         else New_Result_Ident (Type_Of_Node (E)));
      Result_Is_Mutable := False;

      if Within_Protected_Type (E) then
         Self_Name := Concurrent_Self_Ident (Containing_Protected_Type (E));
         Self_Is_Mutable := False;
      end if;

      Generate_Subprogram_Program_Fun
        (Program_Th,
         Dispatch_Th,
         E,
         To_Why_Id (E, Domain => EW_Prog, Local => True));

      Close_Theory (Program_Th, Kind => Definition_Theory);

      Generate_Axiom_For_Post
        (Post_Axiom_Th, Dispatch_Post_Th, Refined_Post_Th, E);

      if Is_Dispatching_Operation (E)
        and then not Is_Hidden_Dispatching_Operation (E)
      then
         Generate_Dispatch_Compatibility_Axioms (Dispatch_Th, E);
      end if;

      Close_Theory (Post_Axiom_Th, Kind => Axiom_Theory, Defined_Entity => E);

      --  Close the dispatching axiom module if it is not empty and add an
      --  extra dependency to the dispatching definition module.

      if Dispatch_Th /= Empty_Theory then
         Close_Theory (Dispatch_Th, Kind => Definition_Theory);
         Record_Extra_Dependency
           (Defining_Module => E_Module (E, Dispatch),
            Axiom_Module    => Dispatch_Th.Module);

         Close_Theory (Dispatch_Post_Th, Kind => Definition_Theory);
         Record_Extra_Dependency
           (Defining_Module => E_Module (E, Dispatch),
            Axiom_Module    => Dispatch_Post_Th.Module);
      end if;

      --  Close the refined post axiom module if it is not empty

      if Refined_Post_Th /= Empty_Theory then
         Close_Theory (Refined_Post_Th, Kind => Definition_Theory);
      end if;

      --  If the entity's body is not in SPARK, if it is inlined for proof, or
      --  if it is a volatile function or a function with side effects, do not
      --  generate axiom.

      if not Entity_Body_Compatible_With_SPARK (E)
        or else Present (Retrieve_Inline_Annotation (E))
        or else Is_Function_With_Side_Effects (E)
        or else Has_Pragma_Volatile_Function (E)
      then
         Result_Name := Why_Empty;
         Result_Is_Mutable := False;
         return;
      end if;

      Expr_Fun_Axiom_Th :=
        Open_Theory
          (WF_Context,
           E_Module (E, Expr_Fun_Axiom),
           Comment =>
             "Module giving a defining axiom for the expression function "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  If E's body is deferred to the enclosing package's body, it needs
      --  special handling for visibility.

      if Has_Refinement (E) then
         Register_Function_With_Refinement (E);
      end if;

      Params := (Logic_Params with delta Gen_Marker => GM_Toplevel);

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Push_Binders_To_Symbol_Table (Logic_Func_Binders);

      --  Given an expression function F with expression E, define an axiom
      --  that states that: "for all <args> => F(<args>) = E".
      --  Except when F is recursive, there is no need to use the precondition
      --  here, as the above axiom is always sound.

      declare
         Guard : W_Pred_Id := Why_Empty;
      begin
         if Is_Recursive (E) then
            Guard :=
              +New_And_Then_Expr
                 (Left   =>
                    +Compute_Guard_Formula (Logic_Func_Binders, Params),
                  Right  =>
                    +Compute_Type_Invariants_For_Subprogram (E, Params, True),
                  Domain => EW_Pred);
            Guard :=
              +New_And_Then_Expr
                 (Left   => +Guard,
                  Right  =>
                    +Compute_Spec (Params, E, Pragma_Precondition, EW_Pred),
                  Domain => EW_Pred);
         end if;
         if Is_Standard_Boolean_Type (Etype (E)) then
            Emit
              (Expr_Fun_Axiom_Th,
               New_Defining_Bool_Axiom
                 (Ada_Node => E,
                  Name     => Logic_Id,
                  Binders  => Flat_Binders,
                  Pre      => Guard,
                  Dep_Kind => EW_Axdep_Func,
                  Def      => Transform_Pred (Expr, Params)));

         else
            declare
               Equ_Ty : constant W_Type_Id := Type_Of_Node (E);
            begin
               Emit
                 (Expr_Fun_Axiom_Th,
                  New_Defining_Axiom
                    (Ada_Node => E,
                     Name     => Logic_Id,
                     Binders  => Flat_Binders,
                     Pre      => Guard,
                     Def      =>
                       +Transform_Expr
                          (Expr,
                           Expected_Type => Equ_Ty,
                           Domain        => EW_Term,
                           Params        => Params)));
            end;
         end if;
      end;

      --  If the function is a traversal function add an axiom to assume the
      --  value of its borrowed at end function.

      if Is_Borrowing_Traversal_Function (E) then
         declare
            Guard                : constant W_Pred_Id :=
              +New_And_Then_Expr
                 (Left   =>
                    +Compute_Guard_Formula (Logic_Func_Binders, Params),
                  Right  => +Func_Guard,
                  Domain => EW_Pred);
            Params               : constant Binder_Array :=
              Flat_Binders
              & Binder_Type'
                  (B_Name => Get_Brower_At_End (E),
                   B_Ent  => Null_Entity_Name,
                   Labels => Symbol_Sets.Empty_Set,
                   others => <>);
            Borrowed_At_End_Call : constant W_Expr_Id :=
              New_Call
                (Domain  => EW_Term,
                 Name    => Get_Borrowed_At_End (E),
                 Binders => Params,
                 Typ     => Get_Typ (Get_Borrowed_At_End (E)));

            Def   : W_Term_Id;
            Dummy : W_Statement_Sequence_Id;
            --  The predicate checks are discarded, they should be checked as
            --  part of the verification of the body of E.

         begin
            Compute_Borrow_At_End_Value
              (Check_Node    => Empty,
               W_Brower      => +Get_Brower_At_End (E),
               Expr          => Expr,
               Reconstructed => Def,
               Checks        => Dummy,
               Params        => Logic_Params);
            Emit
              (Expr_Fun_Axiom_Th,
               New_Guarded_Axiom
                 (Ada_Node => E,
                  Name     => NID (Short_Name (E) & "__" & Pledge_Axiom),
                  Binders  => Params,
                  Triggers =>
                    New_Triggers
                      (Triggers =>
                         (1 =>
                            New_Trigger
                              (Terms => (1 => Borrowed_At_End_Call)))),
                  Pre      => Guard,
                  Def      =>
                    +New_Comparison
                       (Symbol => Why_Eq,
                        Left   => Borrowed_At_End_Call,
                        Right  => +Def,
                        Domain => EW_Pred),
                  Dep      =>
                    New_Axiom_Dep
                      (Name => Get_Borrowed_At_End (E),
                       Kind => EW_Axdep_Func)));
         end;
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      if Within_Protected_Type (E) then
         Self_Name := Why_Empty;
         Self_Is_Mutable := False;
      end if;

      Result_Name := Why_Empty;
      Result_Is_Mutable := False;

      --  If the body of the expression function is hidden by default, do not
      --  record the dependency to the defining module. It will be added on a
      --  case by case bases if the body is made visible.

      Close_Theory (Expr_Fun_Axiom_Th, Kind => Definition_Theory);

      if not Expr_Fun_Hidden_By_Default (E) then
         Record_Extra_Dependency
           (Axiom_Module    => Expr_Fun_Axiom_Th.Module,
            Defining_Module => E_Module (E));
      end if;

      --  The defining axiom has the form f params = expr which is always sound
      --  unless expr depends on f params, which should not be possible if F is
      --  not recursive or if it structurally terminates. We don't protect the
      --  axiom if F does not have a variant either, as in this case a check
      --  message about termination will be emitted.

      if Ekind (E) = E_Function
        and then Is_Recursive (E)
        and then Has_Subprogram_Variant (E)
        and then not Is_Structural_Subprogram_Variant
                       (Get_Pragma (E, Pragma_Subprogram_Variant))
      then

         --  Raise a warning about missing definition on recursive calls

         declare
            Scope            : constant Entity_Id := Enclosing_Unit (E);
            String_For_Scope : constant String :=
              (if Present (Scope)
                 and then Ekind (Scope)
                          in E_Package | E_Function | E_Procedure | E_Entry
                 and then Proof_Module_Cyclic (E, Scope)
               then " and on calls from enclosing unit"
               else "");
         begin
            Warning_Msg_N
              (Warn_Num_Variant, E, Extra_Message => String_For_Scope);
         end;

         Register_Proof_Cyclic_Function (E);
         Register_Dependency_For_Soundness (E_Module (E, Expr_Fun_Axiom), E);
      end if;
   end Translate_Expression_Function_Body;

   -------------------------------
   -- Translate_Subprogram_Spec --
   -------------------------------

   procedure Translate_Subprogram_Spec (E : Callable_Kind_Id) is
      Th          : Theory_UC;
      Dispatch_Th : Theory_UC := Empty_Theory;
   begin
      Th :=
        Open_Theory
          (WF_Context,
           E_Module (E),
           Comment =>
             "Module for possibly declaring "
             & "a logic function for "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  If E is a dispatching operation, create a theory for its dispatching
      --  version.

      if Is_Dispatching_Operation (E)
        and then not Is_Hidden_Dispatching_Operation (E)
      then
         Dispatch_Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Dispatch),
              Comment =>
                "Module for declaring the dispatching variant of the"
                & " subprogram"
                & """"
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
      end if;

      --  If E is potentially invalid, create a record wrapper for its
      --  result and its valid flag.

      if Is_Potentially_Invalid (E) then
         declare
            Validity_Module : constant W_Module_Id :=
              E_Module (E, Validity_Wrapper);
            Validity_Th     : Theory_UC :=
              Open_Theory
                (WF_Context,
                 Validity_Module,
                 Comment =>
                   "Module for the wrapper type for the potentially invalid"
                   & " result of "
                   & """"
                   & Get_Name_String (Chars (E))
                   & """"
                   & (if Sloc (E) > 0
                      then " defined at " & Build_Location_String (Sloc (E))
                      else "")
                   & ", created in "
                   & GNAT.Source_Info.Enclosing_Entity);
            E_Ty            : constant W_Type_Id := Type_Of_Node (E);
            Tree_Ty         : constant W_Type_Id :=
              Get_Validity_Tree_Type (Etype (E));

         begin
            Emit_Record_Declaration
              (Th      => Validity_Th,
               Name    => To_Local (E_Symb (E, WNE_Valid_Wrapper)),
               Binders =>
                 (1 =>
                    (B_Name =>
                       New_Identifier
                         (Domain => EW_Term,
                          Name   =>
                            To_Local (E_Symb (E, WNE_Valid_Wrapper_Result)),
                          Typ    => E_Ty),
                     others => <>),
                  2 =>
                    (B_Name =>
                       New_Identifier
                         (Domain => EW_Term,
                          Name   =>
                            To_Local (E_Symb (E, WNE_Valid_Wrapper_Flag)),
                          Typ    => Tree_Ty),
                     others => <>)));

            declare
               Wrapper_Id : constant W_Identifier_Id :=
                 New_Identifier
                   (Name => "x",
                    Typ  =>
                      New_Named_Type
                        (Name => To_Local (E_Symb (E, WNE_Valid_Wrapper))));
            begin
               Emit
                 (Validity_Th,
                  New_Function_Decl
                    (Domain      => EW_Prog,
                     Name        =>
                       To_Program_Space
                         (To_Local (E_Symb (E, WNE_Valid_Wrapper_Result))),
                     Binders     =>
                       Binder_Array'
                         (1 => (B_Name => Wrapper_Id, others => <>)),
                     Return_Type => E_Ty,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Pre         =>
                       +New_Is_Valid_Call_For_Expr
                          (Tree   =>
                             New_Record_Access
                               (Name  => +Wrapper_Id,
                                Field =>
                                  To_Local
                                    (E_Symb (E, WNE_Valid_Wrapper_Flag)),
                                Typ   => EW_Bool_Type),
                           Ty     => Etype (E),
                           Expr   =>
                             New_Record_Access
                               (Name  => +Wrapper_Id,
                                Field =>
                                  To_Local
                                    (E_Symb (E, WNE_Valid_Wrapper_Result)),
                                Typ   => E_Ty),
                           Domain => EW_Pred),
                     Post        =>
                       New_Comparison
                         (Symbol => Why_Eq,
                          Left   => +New_Result_Ident (Typ => E_Ty),
                          Right  =>
                            New_Record_Access
                              (Name  => +Wrapper_Id,
                               Field =>
                                 To_Local
                                   (E_Symb (E, WNE_Valid_Wrapper_Result)),
                               Typ   => E_Ty))));
            end;

            Close_Theory (Validity_Th, Kind => Definition_Theory);
         end;
      end if;

      --  No logic function is created for volatile functions and functions
      --  with side effects. The function's effects are modelled by an effect
      --  on the program function.

      if Ekind (E) = E_Function
        and then not Is_Function_With_Side_Effects (E)
        and then not Has_Pragma_Volatile_Function (E)
      then
         declare
            Logic_Module : constant W_Module_Id :=
              E_Module (E, Logic_Function_Decl);
            Logic_Th     : Theory_UC :=
              Open_Theory
                (WF_Context,
                 Logic_Module,
                 Comment =>
                   "Module for initial declaration of the logic function for "
                   & """"
                   & Get_Name_String (Chars (E))
                   & """"
                   & (if Sloc (E) > 0
                      then " defined at " & Build_Location_String (Sloc (E))
                      else "")
                   & ", created in "
                   & GNAT.Source_Info.Enclosing_Entity);
         begin
            Declare_Logic_Functions (Logic_Th, Dispatch_Th, E);

            Add_With_Clause (Th, Logic_Module, EW_Export);

            Close_Theory
              (Logic_Th, Kind => Definition_Theory, Defined_Entity => E);
         end;
      end if;

      Close_Theory (Th, Kind => Definition_Theory, Defined_Entity => E);

      --  Close the dispatching module if it is not empty

      if Dispatch_Th /= Empty_Theory then
         Close_Theory (Dispatch_Th, Kind => Definition_Theory);
      end if;
   end Translate_Subprogram_Spec;

   -------------------------------------------------
   -- Update_Symbol_Table_For_Inherited_Contracts --
   -------------------------------------------------

   procedure Update_Symbol_Table_For_Inherited_Contracts (E : Callable_Kind_Id)
   is
      procedure Relocate_Symbols (Overridden : Entity_Id);
      --  Relocate parameters and result from Overridden subprogram to E

      ----------------------
      -- Relocate_Symbols --
      ----------------------

      procedure Relocate_Symbols (Overridden : Entity_Id) is
         From_Formal : Entity_Id := First_Formal (Overridden);
         To_Formal   : Entity_Id := First_Formal (E);

      begin
         while Present (From_Formal) loop
            Ada_Ent_To_Why.Insert
              (Symbol_Table,
               From_Formal,
               Ada_Ent_To_Why.Element (Symbol_Table, To_Formal));

            Next_Formal (From_Formal);
            Next_Formal (To_Formal);
         end loop;

         pragma Assert (No (To_Formal));
      end Relocate_Symbols;

      Inherit_Subp  : constant Subprogram_List := Inherited_Subprograms (E);
      Subp_For_Pre  : Entity_Id := Empty;
      Subp_For_Post : Entity_Id := Empty;
      Contracts     : Node_Lists.List;

      --  Start of processing for Update_Symbol_Table_For_Inherited_Contracts

   begin
      --  Find the subprogram from which the precondition is inherited, if any

      for J in Inherit_Subp'Range loop
         Contracts :=
           Find_Contracts
             (Inherit_Subp (J), Pragma_Precondition, Classwide => True);

         if not Contracts.Is_Empty then
            Subp_For_Pre := Inherit_Subp (J);
            exit;
         end if;
      end loop;

      --  Find the subprogram from which the postcondition is inherited, if any

      for J in Inherit_Subp'Range loop
         Contracts :=
           Find_Contracts
             (Inherit_Subp (J), Pragma_Postcondition, Classwide => True);

         if not Contracts.Is_Empty then
            Subp_For_Post := Inherit_Subp (J);
            exit;
         end if;
      end loop;

      if Present (Subp_For_Pre) then
         Relocate_Symbols (Subp_For_Pre);
      end if;

      if Present (Subp_For_Post) and then Subp_For_Pre /= Subp_For_Post then
         Relocate_Symbols (Subp_For_Post);
      end if;
   end Update_Symbol_Table_For_Inherited_Contracts;

   --------------------------------------
   -- Wrap_Post_Of_Potentially_Invalid --
   --------------------------------------

   function Wrap_Post_Of_Potentially_Invalid
     (E : Entity_Id; Post : W_Pred_Id) return W_Pred_Id
   is
      Result_Id : constant W_Term_Id :=
        +New_Result_Ident (Validity_Wrapper_Type (E));
   begin
      --  Generate:
      --
      --  let result_name = result.valid_name in
      --  let result_name_valid = result.valid_id in
      --    post

      if Is_True_Boolean (+Post) then
         return Post;
      else
         return
           New_Typed_Binding
             (Name    => Result_Name,
              Def     =>
                +New_Function_Valid_Value_Access
                   (Fun => E, Name => +Result_Id),
              Context =>
                New_Typed_Binding
                  (Name    => Get_Valid_Flag_For_Id (Result_Name, Etype (E)),
                   Def     =>
                     +New_Function_Valid_Flag_Access
                        (Fun => E, Name => +Result_Id),
                   Context => Post));
      end if;
   end Wrap_Post_Of_Potentially_Invalid;

   ----------------------------
   -- Wrap_Post_Of_Traversal --
   ----------------------------

   function Wrap_Post_Of_Traversal
     (E      : Entity_Id;
      Post   : W_Pred_Id;
      Args   : W_Expr_Array;
      Params : Transformation_Params) return W_Pred_Id
   is
      Brower_Ty       : constant Entity_Id := Retysp (Etype (E));
      Brower_At_End   : constant W_Identifier_Id := Get_Brower_At_End (E);
      Borrowed_At_End : constant W_Identifier_Id :=
        To_Local (Get_Borrowed_At_End (E));
      Borrowed_Ent    : constant Entity_Id := First_Formal (E);
      Borrowed_Ty     : constant Entity_Id := Retysp (Etype (Borrowed_Ent));
      Borrowed        : constant W_Term_Id :=
        +Transform_Identifier
           (Expr   => Borrowed_Ent,
            Ent    => Borrowed_Ent,
            Domain => EW_Term,
            Params => Params);
      Borrowed_Call   : constant W_Expr_Id :=
        New_Call
          (Domain => EW_Term,
           Name   => Get_Borrowed_At_End (E),
           Args   => Args & (1 => +Brower_At_End),
           Typ    => Get_Typ (Borrowed_At_End));

   begin
      --  Generate:
      --    (forall result_at_end [E.borrowed_at_end args result_at_end].
      --       dyn_inv result_at_end ->
      --       result_at_end.is_null = result.is_null ->
      --         let borrowed_at_end = E.borrowed_at_end args result_at_end in
      --           borrowed_at_end.is_null = borrowed_arg.is_null
      --           /\ post)
      --    /\ borrowed_arg = E.borrowed_at_end args result
      --
      --  The ground call to E.borrowed_at_end is used to allow an instance of
      --  the quantified formula just after the borrow.

      --  No need to assume that the address of the borrower is initialized at
      --  the end of the borrow as traversal functions cannot have relaxed
      --  initialization.

      pragma Assert (not Fun_Has_Relaxed_Init (E));

      return
        New_And_Pred
          (Left  =>
             New_Universal_Quantif
               (Binders  =>
                  (1 =>
                     New_Binder
                       (Domain   => EW_Pred,
                        Name     => Brower_At_End,
                        Arg_Type => Get_Typ (Brower_At_End))),
                Labels   => Symbol_Sets.Empty_Set,
                Triggers =>
                  New_Triggers
                    (Triggers =>
                       (1 => New_Trigger (Terms => (1 => +Borrowed_Call)))),
                Pred     =>
                  New_Conditional
                    (Condition =>
                       New_And_Pred
                         (Left  =>
                            Compute_Dynamic_Inv_And_Initialization
                              (Expr   => +Brower_At_End,
                               Ty     => Brower_Ty,
                               Params => Params),
                          Right =>
                            New_Comparison
                              (Symbol => Why_Eq,
                               Left   =>
                                 New_Pointer_Is_Null_Access
                                   (E => Brower_Ty, Name => +Brower_At_End),
                               Right  =>
                                 New_Pointer_Is_Null_Access
                                   (E => Brower_Ty, Name => +Result_Name))),
                     Then_Part =>
                       New_Binding
                         (Name    => Borrowed_At_End,
                          Def     => +Borrowed_Call,
                          Context =>
                            New_And_Pred
                              (Left  =>
                                 New_Equality_Of_Preserved_Parts
                                   (Ty    => Borrowed_Ty,
                                    Expr1 => +Borrowed_At_End,
                                    Expr2 => Borrowed),
                               Right => Post),
                          Typ     => EW_Bool_Type))),
           Right =>
             New_Comparison
               (Symbol => Why_Eq,
                Left   =>
                  New_Call
                    (Name => Get_Borrowed_At_End (E),
                     Args => Args & (1 => +Result_Name),
                     Typ  => Get_Typ (Borrowed_At_End)),
                Right  => Borrowed));
   end Wrap_Post_Of_Traversal;

end Gnat2Why.Subprograms;
