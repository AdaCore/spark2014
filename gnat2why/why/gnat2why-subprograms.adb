------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with Ada.Containers.Doubly_Linked_Lists;
with Common_Containers;              use Common_Containers;
with Errout;                         use Errout;
with Flow_Dependency_Maps;           use Flow_Dependency_Maps;
with Flow_Generated_Globals;         use Flow_Generated_Globals;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Refinement;                use Flow_Refinement;
with Flow_Types;                     use Flow_Types;
with Flow_Utility;                   use Flow_Utility;
with GNAT.Source_Info;
with Gnat2Why.Annotate;              use Gnat2Why.Annotate;
with Gnat2Why.Error_Messages;        use Gnat2Why.Error_Messages;
with Gnat2Why.Expr;                  use Gnat2Why.Expr;
with Gnat2Why.Tables;                use Gnat2Why.Tables;
with Namet;                          use Namet;
with Nlists;                         use Nlists;
with Rtsfind;                        use Rtsfind;
with Sem_Aux;                        use Sem_Aux;
with Sem_Disp;                       use Sem_Disp;
with Sem_Util;                       use Sem_Util;
with Sinfo;                          use Sinfo;
with Sinput;                         use Sinput;
with Snames;                         use Snames;
with SPARK_Definition;               use SPARK_Definition;
with SPARK_Frame_Conditions;         use SPARK_Frame_Conditions;
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
with Why.Conversions;                use Why.Conversions;
with Why.Gen.Decl;                   use Why.Gen.Decl;
with Why.Gen.Expr;                   use Why.Gen.Expr;
with Why.Gen.Names;                  use Why.Gen.Names;
with Why.Gen.Preds;                  use Why.Gen.Preds;
with Why.Gen.Progs;                  use Why.Gen.Progs;
with Why.Gen.Records;                use Why.Gen.Records;
with Why.Gen.Terms;                  use Why.Gen.Terms;
with Why.Inter;                      use Why.Inter;
with Why.Types;                      use Why.Types;

package body Gnat2Why.Subprograms is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Compute_Args
     (E       : Entity_Id;
      Binders : Binder_Array) return W_Expr_Array;
   --  Given a function entity, and an array of logical binders,
   --  compute a call of the logical Why function corresponding to E.
   --  In general, the binder array has *more* arguments than the Ada entity,
   --  because of effects. Note that these effect variables are not bound here,
   --  they refer to the global variables

   procedure Compute_Contract_Cases_Guard_Map
     (E                  : Entity_Id;
      Guard_Map          : out Ada_To_Why_Ident.Map;
      Others_Guard_Ident : out W_Identifier_Id;
      Others_Guard_Expr  : out W_Expr_Id);
   --  Returns the map from contracts cases nodes attached to subprogram E,
   --  if any, to Why identifiers for the value of these guards in the Why3
   --  program. If the contract cases contain an "others" case, return in
   --  Others_Guard_Ident an identifier for a Boolean value set to true when
   --  this case is enabled, and in Others_Guard_Expr the Why3 expression
   --  to define this identifier. If there is no "others" case, return with
   --  Others_Guard_Ident set to Why_Empty.

   function Compute_Contract_Cases_Entry_Checks
     (E         : Entity_Id;
      Guard_Map : Ada_To_Why_Ident.Map) return W_Prog_Id;
   --  Returns the Why program for checking that the guards of the
   --  Contract_Cases pragma attached to subprogram E (if any) are disjoint,
   --  and that they cover all cases prescribed by the precondition. The checks
   --  that evaluating guards do not raise run-time errors are done separately,
   --  based on the result of Compute_Contract_Cases_Guard_Map. Guard_Map
   --  stores a mapping from guard AST nodes to temporary Why names, so that
   --  the caller can compute the Why expression for these in the pre-state,
   --  and bind them appropriately.

   function Compute_Contract_Cases_Exit_Checks
     (Params             : Transformation_Params;
      E                  : Entity_Id;
      Guard_Map          : Ada_To_Why_Ident.Map;
      Others_Guard_Ident : W_Identifier_Id) return W_Prog_Id;
   --  Returns in Result the Why program for checking that the consequence of
   --  enabled guard of the Contract_Cases pragma attached to subprogram E (if
   --  any) does not raise a run-time error, and that it holds. Guard_Map
   --  stores a mapping from guard AST nodes to temporary Why names, so that
   --  the caller can compute the Why expression for these in the pre-state,
   --  and bind them appropriately.

   function Compute_Contract_Cases_Postcondition
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Pred_Id;
   --  Returns the postcondition corresponding to the Contract_Cases pragma for
   --  subprogram E (if any), to be used in the postcondition of the program
   --  function.

   function Compute_Dynamic_Property_For_Inputs
     (E              : Entity_Id;
      Params         : Transformation_Params;
      Pred_Fun_Param : Entity_Id := Empty;
      Initialized    : Boolean := False) return W_Prog_Id
   with
       Pre => Ekind (E) in
         E_Procedure | E_Function | E_Package | E_Task_Type | E_Entry;
   --  Given an Ada node, collects the set of external dynamic objects
   --  that are referenced in this node.
   --  @param E Entity of subprogram or task or entry or package.
   --  @param Params the transformation parameters
   --  @param Pred_Fun_Param not Empty iff computing the dynamic property for
   --     inputs of a predicate function, in which case [Pred_Fun_Param] is
   --     the entity for the formal parameter of the predicate function.
   --  @param Initialized Assume global out to be initialized at this point.
   --  @result an assumption including the dynamic property of every external
   --     dynamic objects that are referenced in E.

   function Compute_Dynamic_Property_For_Effects
     (E      : Entity_Id;
      Params : Transformation_Params) return W_Pred_Id;
   --  Returns an assumption including the dynamic property of every object
   --  modified by a subprogram.

   function Compute_Type_Invariants_For_Subprogram
     (E         : Entity_Id;
      For_Input : Boolean;
      Params    : Transformation_Params) return W_Pred_Id
   with
     Pre  => Ekind (E) in E_Procedure | E_Function | E_Entry,
     Post => (if For_Input then
                Is_True_Boolean
                  (+Compute_Type_Invariants_For_Subprogram'Result)
                /= Subp_Needs_Invariant_Checks (E));
   --  @param E Entity of a subprogram or entry.
   --  @param For_Input True if we are interested in inputs of E, False if we
   --         are interested in its outputs.
   --  @param Params the transformation parameters
   --  @result a predicate including the type invariants that should be checked
   --          on entry/exit of E.

   function Compute_Type_Invariants_For_Package
     (E      : Entity_Id;
      Params : Transformation_Params) return W_Pred_Id
   with
     Pre  => Ekind (E) = E_Package;
   --  @param E Entity of a package.
   --  @param Params the transformation parameters
   --  @result a predicate including the type invariants that should be checked
   --          after E's elaboration.

   function Compute_Effects
     (E             : Entity_Id;
      Global_Params : Boolean := False) return W_Effects_Id;
   --  Compute the effects of the generated Why function. If Global_Params is
   --  True, then the global version of the parameters is used.

   function Compute_Binders (E : Entity_Id; Domain : EW_Domain)
                             return Item_Array;
   --  Return Why binders for the parameters of subprogram E.
   --  If Domain is EW_Term also generates binders for E's read effects.
   --  The array is a singleton of unit type if the array is empty.

   function Add_Logic_Binders (E           : Entity_Id;
                               Raw_Binders : Item_Array) return Item_Array;
   --  Return Why binders for the parameters and read effects of function E.
   --  The array is a singleton of unit type if E has no parameters and no
   --  effects.

   function Assume_Initial_Condition_Of_Withed_Units
     (E      : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id
   with Pre => Ekind (E) in Subprogram_Kind | E_Package
     and then Is_Compilation_Unit (E);
   --  Assume the Initial_Condition of every unit withed by a compilation unit.
   --  @param E entity for a compilation unit
   --  @param Params the transformation parameters
   --  @result a sequence of assumptions, one for each withed unit which has an
   --          Initial_Condition.

   function Compute_Raw_Binders (E : Entity_Id) return Item_Array;
   --  Return Why binders for the parameters of subprogram E. The array is
   --  empty if E has no parameters.

   function Compute_Guard_Formula (Binders : Item_Array) return W_Pred_Id;
   --  For every object in the binder array, build a predicate for the dynamic
   --  invariant of the object and join everything together with a conjunction.

   function Get_Location_For_Aspect
     (E         : Entity_Id;
      Kind      : Pragma_Id;
      Classwide : Boolean := False) return Node_Id
   with Pre => Kind in Pragma_Precondition
                     | Pragma_Postcondition
                     | Pragma_Refined_Post;
   --  Return a node with a proper location for the pre- or postcondition of E,
   --  if any.

   procedure Generate_Subprogram_Program_Fun
     (File : W_Section_Id;
      E    : Entity_Id);
   --  @param File section in which the expression should be translated
   --  @param E entry or subprogram entity
   --  Generate a why program function for E. Also generate a program function
   --  that performs invariant checks for global / parameters of E. It should
   --  be called before calling E's program function.

   procedure Generate_Axiom_For_Post
     (File : W_Section_Id;
      E    : Entity_Id);
   --  @param File section in which the expression should be translated
   --  @param E entry or subprogram entity
   --  Generate an axiom stating the postcondition of a subprogram E

   function Check_Ceiling_Protocol
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Prog_Id
     with Pre => Ekind (E) in E_Task_Type | E_Entry | E_Function | E_Procedure;
   --  @param Params the transformation params
   --  @param E a task type, entry, main-like or protected subprogram entity
   --  @return an assertion or sequence of assertion that expresses that the
   --    ceiling protocol is respected in the call graph starting from this
   --    entity, i.e. that external calls to protected operations are made with
   --    a priority lower or equal to the priority of the object in question.

   function Compute_Attach_Handler_Check
     (Ty     : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id
     with Pre => Is_Protected_Type (Ty);
   --  @param Ty a protected type
   --  @return an assertion (if necessary) that checks if any of the
   --    Attach_Handler pragmas of the procedures of the type is reserved
   --    see also Ada RM C.3.1(10/3)

   function Compute_Inlined_Expr
     (Function_Entity    : Entity_Id;
      Logic_Func_Binders : Item_Array;
      W_Return_Type      : W_Type_Id;
      File               : W_Section_Id) return W_Expr_Id;
   --  @param Function_Entity entity of a function
   --  @param Logic_Func_Binders binders for Function_Entity's declaration
   --  @param W_Return_Type Why3 type for Function_Entity's return type
   --  @param File section in which the expression should be translated
   --  @return if Function_Entity is non recursive and has a pragma Annotate
   --          (GNATprove, Inline_For_Proof), return the Why3 expression for
   --          its value. Otherwise return Why_Empty.

   ----------------------------------
   -- Add_Dependencies_For_Effects --
   ----------------------------------

   procedure Add_Dependencies_For_Effects
     (T : W_Section_Id;
      E : Entity_Id)
   is
      Reads  : Flow_Types.Flow_Id_Sets.Set;
      Writes : Flow_Types.Flow_Id_Sets.Set;

   begin
      --  Collect global variables potentially read and written
      Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                      Classwide  => True,
                                      Reads      => Reads,
                                      Writes     => Writes);

      --  Union reads with writes (essentially just ignore the variant)
      Reads.Union (Change_Variant (Writes, In_View));

      for N of Reads loop
         Add_Effect_Import (T, To_Name (N));
      end loop;
   end Add_Dependencies_For_Effects;

   ----------------------------------------------
   -- Assume_Initial_Condition_Of_Withed_Units --
   ----------------------------------------------

   function Assume_Initial_Condition_Of_Withed_Units
     (E      : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id
   is
      CU           : constant Node_Id := Enclosing_Comp_Unit_Node (E);
      Context_Item : Node_Id;
      Assumption   : W_Prog_Id := +Void;

   begin
      pragma Assert (Nkind (CU) = N_Compilation_Unit);

      --  For each withed unit which is a package declaration, assume its
      --  Initial_Condition

      Context_Item := First (Context_Items (CU));
      while Present (Context_Item) loop
         if Nkind (Context_Item) = N_With_Clause
           and then not Limited_Present (Context_Item)
           and then Nkind (Unit (Library_Unit (Context_Item)))
           = N_Package_Declaration
         then
            declare
               Package_E : constant Entity_Id :=
                 Unique_Defining_Entity (Unit (Library_Unit (Context_Item)));
               Init_Cond : constant Node_Id :=
                 Get_Pragma (Package_E, Pragma_Initial_Condition);
            begin
               if Present (Init_Cond) then
                  declare
                     Expr : constant Node_Id :=
                       Expression
                         (First (Pragma_Argument_Associations (Init_Cond)));
                  begin
                     Assumption :=
                       Sequence
                         (Assumption,
                          New_Assume_Statement
                            (Pred => +Transform_Expr
                               (Expr, EW_Bool_Type, EW_Pred, Params)));
                  end;
               end if;
            end;
         end if;
         Context_Item := Next (Context_Item);
      end loop;

      return Assumption;
   end Assume_Initial_Condition_Of_Withed_Units;

   ----------------------------
   -- Check_Ceiling_Protocol --
   ----------------------------

   function Check_Ceiling_Protocol
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Prog_Id is

      function Self_Priority return W_Expr_Id;
      --  @return expression for the priority of entity E

      -------------------
      -- Self_Priority --
      -------------------

      function Self_Priority return W_Expr_Id is
         --  If the priority is not explicitly specified then assume then use:
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
            elsif Ekind (E) = E_Entry
              or else (Ekind (E) in E_Function | E_Procedure
                         and then Is_Protected_Type (Scope (E)))
              then Scope (E)
            else raise Program_Error);
         --  Entity where Priority or Interrupt_Priority pragma is attached

         Prio_Expr     : constant Node_Id :=
           Get_Priority_Or_Interrupt_Priority (Pragma_Entity);
         --  Priority expression

      begin

         if Present (Prio_Expr) then
            return Transform_Expr (Prio_Expr, EW_Int_Type, EW_Pterm, Params);
         end if;

         --  No explicit priority was given

         if Ekind (E) = E_Task_Type then
            --  If pragma Interrupt_Priority is present then build expression
            --  for System.Interrupt_Priority'Last; otherwise for
            --  System.Priority'Last.
            return
              New_Attribute_Expr
                (Domain => EW_Term,
                 Ty     =>
                   RTE (if Present
                            (Find_Contract (E, Pragma_Interrupt_Priority))
                        then RE_Interrupt_Priority
                        else RE_Priority),
                 Attr   => Attribute_Last,
                 Params => Params);

         elsif Ekind (E) in Subprogram_Kind and then Might_Be_Main (E) then
            --  Return expression used that defined System.Default_Priority
            return
              Transform_Expr
                (Expr   => Expression (Parent (RTE (RE_Default_Priority))),
                 Domain => EW_Term,
                 Params => Params);

         else
            declare
               PT : constant Entity_Id := Scope (E);

               Type_Id : RE_Id;
               Attr_Id : Supported_Attribute_Id;
               --  Type and attribute for priority expression
            begin
               if Present (Find_Contract (PT, Pragma_Interrupt_Priority))
               then
                  --  Pragma Interrupt_Priority without expression defaults to
                  --  Interrupt_Priority'Last; RM J.15(12).
                  Type_Id := RE_Interrupt_Priority;
                  Attr_Id := Attribute_Last;

               elsif Has_Interrupt_Handler (PT)
                 or else Has_Attach_Handler (PT)
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
                 New_Attribute_Expr
                   (Domain => EW_Term,
                    Ty     => RTE (Type_Id),
                    Attr   => Attr_Id,
                    Params => Params);

            end;
         end if;

      end Self_Priority;

   --  Start of processing for Check_Ceiling_Protocol

   begin

      if Ekind (E) not in E_Task_Type | E_Entry
        and then not Might_Be_Main (E)
        and then
          (Ekind (E) not in E_Function | E_Procedure or else
                 not Is_Protected_Type (Scope (E)))
      then
         return +Void;
      end if;

      declare
         Prio : constant W_Expr_Id := Self_Priority;

         S    : W_Prog_Id := +Void;
      begin
         --  Placeholder for a Why3 sequence that will represent the check
         for Obj_Name of Directly_Called_Protected_Objects (E) loop

            --  Create a check that compares priorities of the task and of a
            --  single protected component of an object. See ARM, D.3 (7-11)
            --  for details.

            for Obj_Prio of Component_Priorities (Obj_Name) loop

               declare
                  Obj_Prio_Expr : constant W_Expr_Id :=
                    (case Obj_Prio.Kind is
                     --  ??? if type of the component is visible we should try
                     --  to transform the expression.
                        when Nonstatic =>
                           New_Attribute_Expr (Domain => EW_Term,
                                               Ty     => RTE (RE_Any_Priority),
                                               Attr   => Attribute_First,
                                               Params => Params),

                        when Static =>
                           New_Integer_Constant
                             (Value => UI_From_Int (Obj_Prio.Value)),

                        when Default_Prio =>
                           New_Attribute_Expr
                             (Domain => EW_Term,
                              Ty     => RTE (RE_Priority),
                              Attr   => Attribute_Last,
                              Params => Params),

                        when Default_Interrupt_Prio =>
                           New_Attribute_Expr
                             (Domain => EW_Term,
                              Ty     => RTE (RE_Interrupt_Priority),
                              Attr   => Attribute_First,
                              Params => Params),

                        when Last_Interrupt_Prio =>
                           New_Attribute_Expr
                             (Domain => EW_Term,
                              Ty     => RTE (RE_Interrupt_Priority),
                              Attr   => Attribute_Last,
                              Params => Params));

                  Pred         : constant W_Pred_Id :=
                    +New_Comparison
                      (Symbol => (case Obj_Prio.Kind is
                                     when Nonstatic => Why_Eq,
                                     when others    => Int_Infix_Le),
                     Left   => Prio,
                     Right  => Obj_Prio_Expr,
                     Domain => EW_Pred);

                  Check        : constant W_Prog_Id :=
                    New_Located_Assert (Ada_Node => E,
                                        Pred     => Pred,
                                        Reason   =>
                                          VC_Ceiling_Priority_Protocol,
                                        Kind     => EW_Check);
               begin
                  S := Sequence (S, Check);
               end;
            end loop;
         end loop;

         return S;
      end;
   end Check_Ceiling_Protocol;

   ------------------
   -- Compute_Args --
   ------------------

   function Compute_Args
     (E       : Entity_Id;
      Binders : Binder_Array) return W_Expr_Array
   is
      Cnt    : Natural := 1;
      Result : W_Expr_Array (1 .. Binders'Last);
      Ada_Binders : constant List_Id :=
        Parameter_Specifications (Subprogram_Specification (E));
      Arg_Length  : Nat := List_Length (Ada_Binders);

   begin

      if Is_Protected_Subprogram (E) then
         Arg_Length := Arg_Length + 1;
      end if;

      if Arg_Length = 0
        and then not Flow_Utility.Has_Proof_Global_Reads (E, Classwide => True)
      then
         return W_Expr_Array'(1 => +Void);
      end if;

      while Cnt <= Natural (Arg_Length) loop
         Result (Cnt) := +Binders (Cnt).B_Name;
         Cnt := Cnt + 1;
      end loop;

      while Cnt <= Binders'Last loop
         Result (Cnt) := Get_Logic_Arg (Binders (Cnt), True);
         Cnt := Cnt + 1;
      end loop;

      return Result;
   end Compute_Args;

   ----------------------------------
   -- Compute_Attach_Handler_Check --
   ----------------------------------

   function Compute_Attach_Handler_Check
     (Ty     : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id
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
           Expression (Next (First (Pragma_Argument_Associations
                       (Get_Pragma (Proc, Pragma_Attach_Handler)))));

         --  To check whether the attach handler is reserved, we call the
         --  Ada.Interrupts.Is_Reserved. However, this function reads a global
         --  state, which makes it a bit difficult to generate a call in
         --  the logic (we would have to come up with the state object - not
         --  impossible but not currently proposed by frontend). Instead,
         --  we call the program function, which has only the interrupt as
         --  argument, store the result in a temp and assert that the result
         --  is false. So we are essentially asserting "not is_reserved(int)".

         Res     : constant W_Expr_Id :=
           New_Temp_For_Expr
             (New_Call
                (Name   => To_Why_Id (RTE (RE_Is_Reserved), Domain => EW_Prog),
                 Domain => EW_Prog,
                 Args   =>
                   (1 =>
                      Transform_Expr (Att_Val, EW_Int_Type, EW_Term, Params)),
                 Typ    => EW_Bool_Type));

         Pred    : constant W_Pred_Id :=
           New_Call
             (Name => Why_Eq,
              Args => (1 => +Res,
                       2 => Bool_False (EW_Term)));
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
                  Ent : constant Entity_Id := Defining_Entity (Proc);
               begin
                  if Ekind (Ent) = E_Procedure
                    and then Present (Get_Pragma (Ent, Pragma_Attach_Handler))
                  then
                     Stat := Sequence (Stat,
                                       Single_Attach_Handler_Check (Ent));
                  end if;
               end;
            end if;
            Next (Proc);
         end loop;
      end Process_Declarations;

      pragma Assert (Nkind (Parent (Ty)) = N_Protected_Type_Declaration);

      PT_Def : constant Node_Id := Protected_Definition (Parent (Ty));

   --  Start of processing for Compute_Attach_Handler_Check

   begin
      Process_Declarations (Visible_Declarations (PT_Def));

      if Private_Spec_In_SPARK (Ty) then
         Process_Declarations (Private_Declarations (PT_Def));
      end if;

      return Stat;
   end Compute_Attach_Handler_Check;

   ---------------------
   -- Compute_Binders --
   ---------------------

   function Compute_Binders
     (E : Entity_Id;
      Domain : EW_Domain)
      return Item_Array
   is
      Binders : constant Item_Array :=
        Compute_Subprogram_Parameters (E, Domain);
   begin
      --  If E has no parameters, return a singleton of unit type.

      if Binders'Length = 0 then
         return (1 => (Regular, Unit_Param));
      else
         return Binders;
      end if;
   end Compute_Binders;

   -----------------------------------------
   -- Compute_Dynamic_Property_For_Inputs --
   -----------------------------------------

   function Compute_Dynamic_Property_For_Inputs
     (E              : Entity_Id;
      Params         : Transformation_Params;
      Pred_Fun_Param : Entity_Id := Empty;
      Initialized    : Boolean   := False) return W_Prog_Id
   is
      Includes : Node_Sets.Set;

   begin
      --  Collect global variables read or written in E

      case Ekind (E) is
         when E_Entry
            | E_Function
            | E_Procedure
            | E_Task_Type
         =>
            declare
               Write_Ids : Flow_Types.Flow_Id_Sets.Set;
               Read_Ids  : Flow_Types.Flow_Id_Sets.Set;

               procedure Include (S : Flow_Types.Flow_Id_Sets.Set);
               --  Include entities represented in S (as Flow_Ids) in Includes

               -------------
               -- Include --
               -------------

               procedure Include (S : Flow_Types.Flow_Id_Sets.Set) is
               begin
                  for F of S loop
                     case F.Kind is
                     when Direct_Mapping =>
                        Includes.Include (Get_Direct_Mapping_Id (F));

                     when Magic_String =>
                        declare
                           Entity : constant Entity_Id := Find_Entity (F.Name);
                        begin
                           if Present (Entity) then
                              Includes.Include (Entity);
                           end if;
                        end;

                     when others =>
                        raise Program_Error;
                     end case;
                  end loop;
               end Include;

            begin

               --  Also get references to global constants with variable inputs
               --  even if they are constants in Why.

               Flow_Utility.Get_Proof_Globals (Subprogram     => E,
                                               Classwide      => True,
                                               Reads          => Read_Ids,
                                               Writes         => Write_Ids,
                                               Keep_Constants => True);

               Include (Read_Ids);
               Include (Write_Ids);
            end;

            --  Collect parameters of E if any
            --  ??? We may want to collect discriminants of task types

            if Ekind (E) in E_Function | E_Procedure | E_Entry then
               declare
                  Params : constant List_Id :=
                    Parameter_Specifications
                      (if Is_Entry (E) then Parent (E)
                       else Subprogram_Specification (E));
                  Param  : Node_Id;
               begin
                  Param := First (Params);
                  while Present (Param) loop
                     Includes.Include (Defining_Identifier (Param));
                     Next (Param);
                  end loop;
               end;

               --  If E is a protected subprogram, add the type itself to stand
               --  for the self reference.

               if Is_Protected_Subprogram (E)
                 and then Present (Get_Body (E))
                 and then Entity_Body_In_SPARK (E)
               then
                  Includes.Include (Containing_Protected_Type (E));
               end if;
            end if;

         when E_Package =>
            if not Is_Wrapper_Package (E) then

               --  For packages, we use the Initializes aspect to get the
               --  variables referenced during elaboration.
               --  We don't do it for wrapper packages as Initializes are not
               --  generated for them.

               declare
                  Init_Map : constant Dependency_Maps.Map :=
                    Parse_Initializes (E, Get_Flow_Scope (E));

               begin
                  for S of Init_Map loop
                     for Y of S loop

                        --  Expand Abstract_State if any

                        declare
                           Reads : constant Flow_Id_Sets.Set :=
                             Expand_Abstract_State (Y,
                                                    Erase_Constants => False);
                        begin

                           --  Get the entity associated with the Flow_Ids
                           for X of Reads loop
                              case X.Kind is
                              when Direct_Mapping =>
                                 Includes.Include (Get_Direct_Mapping_Id (X));

                              when Magic_String =>
                                 declare
                                    Entity : constant Entity_Id :=
                                      Find_Entity (X.Name);
                                 begin
                                    if Present (Entity) then
                                       Includes.Include (Entity);
                                    end if;
                                 end;

                              when Null_Value
                                 | Record_Field
                                 | Synthetic_Null_Export
                              =>
                                 raise Program_Error;
                              end case;
                           end loop;
                        end;
                     end loop;
                  end loop;
               end;
            end if;

         when others =>
            raise Program_Error;
      end case;

      return Assume_Dynamic_Invariant_For_Variables
        (Vars             => Includes,
         Params           => Params,
         Scope            => E,
         Exclude_Top_Pred => Pred_Fun_Param,
         Initialized      => Initialized);
   end Compute_Dynamic_Property_For_Inputs;

   ------------------------------------------
   -- Compute_Dynamic_Property_For_Effects --
   ------------------------------------------

   function Compute_Dynamic_Property_For_Effects
     (E      : Entity_Id;
      Params : Transformation_Params) return W_Pred_Id
   is
      Func_Why_Binders     : constant Binder_Array :=
        To_Binder_Array (Compute_Binders (E, EW_Prog));
      Dynamic_Prop_Effects : W_Pred_Id := True_Pred;
   begin

      --  Compute the dynamic property of mutable parameters

      for I in Func_Why_Binders'Range loop
         if Func_Why_Binders (I).Mutable then
            declare
               Binder   : constant Binder_Type := Func_Why_Binders (I);
               Dyn_Prop : constant W_Pred_Id :=
                 Compute_Dynamic_Invariant
                   (Expr => +Transform_Identifier (Params => Params,
                                                   Expr   => Binder.Ada_Node,
                                                   Ent    => Binder.Ada_Node,
                                                   Domain => EW_Term),
                    Ty   => Etype (Binder.Ada_Node));
            begin
               Dynamic_Prop_Effects := +New_And_Expr
                 (Left   => +Dynamic_Prop_Effects,
                  Right  => +Dyn_Prop,
                  Domain => EW_Pred);
            end;
         end if;
      end loop;

      --  Compute the dynamic property of global output

      declare
         Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
         Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
         Write_Names : Name_Sets.Set;
      begin
         Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                         Classwide  => True,
                                         Reads      => Read_Ids,
                                         Writes     => Write_Ids);
         Write_Names := Flow_Types.To_Name_Set (Write_Ids);

         for Name of Write_Names loop
            declare
               Entity : constant Entity_Id := Find_Entity (Name);
            begin
               if Present (Entity)
                 and then not (Ekind (Entity) = E_Abstract_State)
                 and then Entity_In_SPARK (Entity)
               then

                  --  ??? skip dynamic invariant for protected type

                  if Ekind (Entity) in Type_Kind then
                     pragma Assert (Ekind (Entity) in Protected_Kind);
                     null;
                  else
                     declare
                        Dyn_Prop : constant W_Pred_Id :=
                          Compute_Dynamic_Invariant
                            (Expr =>
                               +Transform_Identifier (Params   => Params,
                                                      Expr     => Entity,
                                                      Ent      => Entity,
                                                      Domain   => EW_Term),
                             Ty   => Etype (Entity));
                     begin
                        Dynamic_Prop_Effects := +New_And_Expr
                          (Left   => +Dynamic_Prop_Effects,
                           Right  => +Dyn_Prop,
                           Domain => EW_Pred);
                     end;
                  end if;
               end if;
            end;
         end loop;
      end;

      return Dynamic_Prop_Effects;
   end Compute_Dynamic_Property_For_Effects;

   ---------------------
   -- Compute_Effects --
   ---------------------

   function Compute_Effects
     (E             : Entity_Id;
      Global_Params : Boolean := False) return W_Effects_Id
   is
      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Read_Names  : Name_Sets.Set;
      Write_Names : Name_Sets.Set;
      Eff         : constant W_Effects_Id := New_Effects;

      generic
         with procedure Effects_Append
           (Id : W_Effects_Id; New_Item : W_Identifier_Id);
      procedure Effects_Append_Binder (Binder : Item_Type);
      --  Append to effects Eff the variable associated with an item
      --  @param Binder variable to add to Eff

      ---------------------------
      -- Effects_Append_Binder --
      ---------------------------

      procedure Effects_Append_Binder (Binder : Item_Type)  is
      begin
         case Binder.Kind is
            when Regular
               | Concurrent_Self
            =>
               if Binder.Main.Mutable then
                  Effects_Append (Eff, Binder.Main.B_Name);
               end if;

            when UCArray =>
               Effects_Append (Eff, Binder.Content.B_Name);

            when DRecord =>
               if Binder.Fields.Present then
                  Effects_Append (Eff, Binder.Fields.Binder.B_Name);
               end if;
               if Binder.Discrs.Present
                 and then Binder.Discrs.Binder.Mutable
               then
                  Effects_Append (Eff, Binder.Discrs.Binder.B_Name);
               end if;

            when Func => raise Program_Error;
         end case;
      end Effects_Append_Binder;

      procedure Effects_Append_Binder_To_Reads is
         new Effects_Append_Binder (Effects_Append_To_Reads);

      procedure Effects_Append_Binder_To_Writes is
         new Effects_Append_Binder (Effects_Append_To_Writes);

   --  Start of processing for Compute_Effects

   begin
      --  Collect global variables potentially read and written

      Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                      Classwide  => True,
                                      Reads      => Read_Ids,
                                      Writes     => Write_Ids);
      Read_Names  := Flow_Types.To_Name_Set (Read_Ids);
      Write_Names := Flow_Types.To_Name_Set (Write_Ids);

      for Name of Write_Names loop
         declare
            Entity : constant Entity_Id := Find_Entity (Name);
         begin

            if Present (Entity)
              and then not (Ekind (Entity) = E_Abstract_State)
              and then Entity_In_SPARK (Entity)
            then
               --  Special case of effect on protected components

               declare
                  Binder : Item_Type;
               begin
                  if Is_Type (Entity) then
                     pragma Assert (Ekind (Entity) in E_Protected_Type);
                     Binder :=
                       Item_Type'(Kind => Concurrent_Self,
                                  Main => Concurrent_Self_Binder (Entity));
                  else
                     Binder := Ada_Ent_To_Why.Element (Symbol_Table, Entity);
                  end if;

                  Effects_Append_Binder_To_Writes (Binder);
               end;
            else
               Effects_Append_To_Writes
                 (Eff,
                  To_Why_Id (Obj => To_String (Name), Local => False));
            end if;
         end;
      end loop;

      --  Add all OUT and IN OUT parameters as potential writes.
      --  If Global_Params is True, use binders from the Symbol_Table;
      --  otherwise, use binders from the function declaration.

      if Global_Params then
         declare
            Params : constant List_Id :=
              Parameter_Specifications (Subprogram_Specification (E));
            Param  : Node_Id;
         begin
            Param := First (Params);
            while Present (Param) loop
               declare
                  B : constant Item_Type :=
                    Ada_Ent_To_Why.Element
                      (Symbol_Table, Defining_Entity (Param));
               begin
                  Effects_Append_Binder_To_Writes (B);
               end;
               Next (Param);
            end loop;
         end;
      else
         declare
            Binders : constant Item_Array := Compute_Raw_Binders (E);
         begin
            for B of Binders loop
               Effects_Append_Binder_To_Writes (B);
            end loop;
         end;
      end if;

      for Name of Read_Names loop
         declare
            Entity : constant Entity_Id := Find_Entity (Name);
         begin

            if Present (Entity)
              and then not (Ekind (Entity) = E_Abstract_State)
              and then Entity_In_SPARK (Entity)
            then
               declare
                  Binder : Item_Type;
               begin
                  --  Special case of effect on protected components
                  if Is_Type (Entity) then
                     pragma Assert (Ekind (Entity) in E_Protected_Type |
                                                      E_Task_Type);
                     Binder :=
                       Item_Type'(Kind => Concurrent_Self,
                                  Main => Concurrent_Self_Binder (Entity));
                  else
                     Binder :=
                       Ada_Ent_To_Why.Element (Symbol_Table, Entity);
                  end if;

                  Effects_Append_Binder_To_Reads (Binder);
               end;
            else
               Effects_Append_To_Reads
                 (Eff,
                  To_Why_Id (Obj => To_String (Name), Local => False));
            end if;
         end;
      end loop;

      return +Eff;
   end Compute_Effects;

   ---------------------------
   -- Compute_Guard_Formula --
   ---------------------------

   function Compute_Guard_Formula (Binders : Item_Array) return W_Pred_Id is
      Pred : W_Pred_Id := True_Pred;

   begin
      --  Add to guard the dynamic property of logic parameters.

      for B of Binders loop

         declare
            Ada_Node : constant Node_Id :=
              Get_Ada_Node_From_Item (B);
            Expr     : constant W_Expr_Id :=
              Reconstruct_Item (B, True);
            Ty_Node  : constant Entity_Id :=
              (if Present (Ada_Node) then
                   (if Is_Type (Ada_Node) then Ada_Node
                    else Etype (Ada_Node))
               else Empty);
            Dyn_Prop : constant W_Pred_Id :=
              (if Present (Ty_Node) then
                    Compute_Dynamic_Invariant (Expr => +Expr,
                                               Ty   => Ty_Node)
               else
                  True_Pred);
         begin
            if No (Ada_Node) then
               declare
                  K    : constant Item_Enum := B.Kind;
                  Name : constant W_Identifier_Id :=
                    B.Main.B_Name;
                  Ty   : constant W_Type_Id := Get_Typ (Name);
               begin

                  --  If there is no Ada_Node associated to the binder then
                  --  it must be either the unit binder or a binder for
                  --  a variable referenced for effects only.

                  pragma Assert
                    (K = Regular
                     and then (Ty in
                           M_Main.Type_Of_Heap |
                       EW_Private_Type |
                       EW_Unit_Type));
               end;
            end if;

            Pred :=
              +New_And_Then_Expr
              (Domain => EW_Pred,
               Left   => +Pred,
               Right  => +Dyn_Prop);
         end;
      end loop;
      return Pred;
   end Compute_Guard_Formula;

   ------------------------------------
   -- Compute_Subprogram_Parameters  --
   ------------------------------------

   function Compute_Subprogram_Parameters
     (E      : Entity_Id;
      Domain : EW_Domain) return Item_Array
   is
      Raw_Binders : constant Item_Array := Compute_Raw_Binders (E);
   begin
      return (if Domain = EW_Prog then Raw_Binders
              else Add_Logic_Binders (E, Raw_Binders));
   end Compute_Subprogram_Parameters;

   ------------------------------------------
   --  Compute_Type_Invariants_For_Package --
   ------------------------------------------

   function Compute_Type_Invariants_For_Package
     (E      : Entity_Id;
      Params : Transformation_Params) return W_Pred_Id
   is
      Inv_Pred : W_Pred_Id := True_Pred;

   begin
      --  We use the Initializes aspect to get the variables initialized during
      --  elaboration.
      --  We don't do it for wrapper packages as they do not have local
      --  variables / constants.

      if not Is_Wrapper_Package (E) then
         declare
            Init_Map : constant Dependency_Maps.Map :=
              Parse_Initializes (E, Get_Flow_Scope (E));

         begin
            for Cu in Init_Map.Iterate loop
               declare
                  K  : Flow_Id renames Dependency_Maps.Key (Cu);
                  FS : constant Flow_Id_Sets.Set :=
                    Expand_Abstract_State (K, Erase_Constants => False);
                  E  : Entity_Id;
               begin
                  for F of FS loop
                     if F.Kind = Direct_Mapping then
                        E := Get_Direct_Mapping_Id (F);

                        --  Only partial views of constants are stored in the
                        --  symbol map.

                        if Ekind (E) = E_Constant and then Is_Full_View (E)
                        then
                           E := Partial_View (E);
                        end if;

                        --  Only consider objects that are in SPARK. Other
                        --  objects are translated to a private type in Why.

                        if Present (E)
                          and then Ekind (E) in Object_Kind
                          and then Entity_In_SPARK (E)
                        then
                           declare
                              Binder : constant Item_Type :=
                                Ada_Ent_To_Why.Element (Symbol_Table, E);
                              Expr   : constant W_Expr_Id :=
                                Reconstruct_Item
                                  (Binder, Ref_Allowed => Params.Ref_Allowed);
                           begin
                              Inv_Pred := +New_And_Then_Expr
                                (Left   => +Inv_Pred,
                                 Right  => +Compute_Type_Invariant
                                   (Expr        => +Expr,
                                    Ty          => Etype (E),
                                    Params      => Params,
                                    On_Internal => True),
                                 Domain => EW_Pred);
                           end;
                        end if;
                     end if;
                  end loop;
               end;
            end loop;
         end;
      end if;

      return Inv_Pred;
   end Compute_Type_Invariants_For_Package;

   ---------------------------------------------
   -- Compute_Type_Invariants_For_Subprogram  --
   ---------------------------------------------

   function Compute_Type_Invariants_For_Subprogram
     (E         : Entity_Id;
      For_Input : Boolean;
      Params    : Transformation_Params) return W_Pred_Id
   is

      procedure Add_Type_Invariants_For_Globals
        (Ids      :        Flow_Types.Flow_Id_Sets.Set;
         Inv_Pred : in out W_Pred_Id);
      --  Add the type invariants of elements of Ids to Inv_Pred.
      --  @param Ids the set of read / write effects for the subprogram
      --  @param Inv_Pred a why predicate

      procedure Add_Type_Invariants_For_Params
        (Subp      : Entity_Id;
         For_Input : Boolean;
         Inv_Pred  : in out W_Pred_Id);
      --  Add the type invariants of Subp's parameters to Inv_Pred.
      --  @param Subp the entity of the subprogram
      --  @param For_Input True if we should consider inputs of Subp, False if
      --         we should consider outputs.
      --  @param Inv_Pred a why predicate

      function Compute_Type_Invariant_For_Entity
        (E : Entity_Id) return W_Pred_Id
      with Pre => Ada_Ent_To_Why.Has_Element (Symbol_Table, E);
      --  @param E Entity of an object stored in the Symbol_Table
      --  @return a predicate containing the invariants of all parts of E
      --          which have an external invariant.

      -------------------------------------
      -- Add_Type_Invariants_For_Globals --
      -------------------------------------

      procedure Add_Type_Invariants_For_Globals
        (Ids      :        Flow_Types.Flow_Id_Sets.Set;
         Inv_Pred : in out W_Pred_Id)
      is
      begin
         for F of Ids loop
            pragma Assert (F.Kind in Direct_Mapping | Magic_String);

            --  Magic_String are global state with no attached entities. As
            --  such state is translated as private in Why3, we do not need
            --  to consider any type invariant for it.

            if F.Kind = Direct_Mapping then
               declare
                  E : constant Entity_Id := Get_Direct_Mapping_Id (F);
               begin
                  if Present (E) then

                     --  Global variables accessed by the subprogram. Abstract
                     --  states and private variables are not considered here,
                     --  as they cannot have visible type invariants.

                     if Ekind (E) in Object_Kind and then Entity_In_SPARK (E)
                     then
                        Inv_Pred := +New_And_Then_Expr
                          (Left   => +Inv_Pred,
                           Right  => +Compute_Type_Invariant_For_Entity (E),
                           Domain => EW_Pred);

                     --  Self reference of protected subprograms

                     elsif Ekind (E) in Type_Kind then
                        pragma Assert (Is_Concurrent_Type (E));
                        Inv_Pred := +New_And_Then_Expr
                          (Left   => +Inv_Pred,
                           Right  => +Compute_Type_Invariant
                             (Expr        =>
                                  +Concurrent_Self_Binder (E).B_Name,
                              Ty          => E,
                              Params      => Params,
                              On_Internal => True),
                           Domain => EW_Pred);
                     end if;
                  end if;
               end;
            end if;
         end loop;
      end Add_Type_Invariants_For_Globals;

      ------------------------------------
      -- Add_Type_Invariants_For_Params --
      ------------------------------------

      procedure Add_Type_Invariants_For_Params
        (Subp      : Entity_Id;
         For_Input : Boolean;
         Inv_Pred  : in out W_Pred_Id)
      is
         Parameters : constant List_Id :=
           (if Is_Entry (E) then Parameter_Specifications (Parent (Subp))
            else Parameter_Specifications (Subprogram_Specification (Subp)));
         Parameter  : Node_Id := First (Parameters);
      begin
         while Present (Parameter) loop
            declare
               E : constant Entity_Id := Defining_Entity (Parameter);
            begin
               if (if For_Input then Ekind (E) /= E_Out_Parameter
                   else Ekind (E) /= E_In_Parameter)
               then
                  Inv_Pred := +New_And_Then_Expr
                    (Left   => +Inv_Pred,
                     Right  => +Compute_Type_Invariant_For_Entity (E),
                     Domain => EW_Pred);
               end if;
            end;
            Next (Parameter);
         end loop;
      end Add_Type_Invariants_For_Params;

      ---------------------------------------
      -- Compute_Type_Invariant_For_Entity --
      ---------------------------------------

      function Compute_Type_Invariant_For_Entity
        (E : Entity_Id) return W_Pred_Id
      is
         Binder : constant Item_Type :=
           Ada_Ent_To_Why.Element (Symbol_Table, E);
         Expr   : constant W_Expr_Id :=
           Reconstruct_Item (Binder, Ref_Allowed => Params.Ref_Allowed);
      begin
         return Compute_Type_Invariant
           (Expr        => +Expr,
            Ty          => Etype (E),
            Params      => Params,
            On_Internal => True);
      end Compute_Type_Invariant_For_Entity;

      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;

      Inv_Pred    : W_Pred_Id := True_Pred;

      Is_External : constant Boolean := Is_Globally_Visible (E);
      --  The subprogram is an external or a boundary subprogram if it is
      --  visible from outside the current compilation unit.

   begin
      --  If the subprogram is boundary or external, we should assume/check the
      --  type invariants of its parameters.

      if Is_External then
         Add_Type_Invariants_For_Params (E, For_Input, Inv_Pred);
      end if;

      Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                      Classwide  => True,
                                      Reads      => Read_Ids,
                                      Writes     => Write_Ids);

      --  If For_Input is True, add the invariants of the variables read by E,
      --  otherwise add the invariants of the variables written by E.

      if For_Input then
         Add_Type_Invariants_For_Globals (Read_Ids, Inv_Pred);
      else
         Add_Type_Invariants_For_Globals (Write_Ids, Inv_Pred);
      end if;

      --  If For_Input is false and E is a function, add the invariants of its
      --  result.

      if Is_External
        and then not For_Input
        and then Ekind (E) = E_Function
      then
         declare
            Result : constant W_Term_Id :=
              (if Params.Phase = Generate_Logic
               then +Result_Name
               else New_Deref
                 (Right => Result_Name,
                  Typ   => Get_Typ (+Result_Name)));
         begin
            Inv_Pred := +New_And_Then_Expr
              (Left   => +Inv_Pred,
               Right  => +Compute_Type_Invariant
                 (Expr        => Result,
                  Ty          => Etype (E),
                  Params      => Params,
                  On_Internal => True),
               Domain => EW_Pred);
         end;
      end if;

      return Inv_Pred;
   end Compute_Type_Invariants_For_Subprogram;

   -----------------------
   -- Add_Logic_Binders --
   -----------------------

   function Add_Logic_Binders (E           : Entity_Id;
                               Raw_Binders : Item_Array)
                                     return Item_Array is
      Num_Binders : Integer;
      Count       : Integer;

      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Read_Names  : Name_Sets.Set;

   begin
      --  Collect global variables potentially read

      Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                      Classwide  => True,
                                      Reads      => Read_Ids,
                                      Writes     => Write_Ids);
      Read_Names := Flow_Types.To_Name_Set (Read_Ids);

      --  If E has no parameters and no read effects, return a singleton of
      --  unit type.

      Num_Binders := Raw_Binders'Length + Integer (Read_Names.Length);

      declare
         Result : Item_Array (1 .. Num_Binders);

      begin
         --  First, copy all binders for parameters of E

         Result (1 .. Raw_Binders'Length) := Raw_Binders;

         --  Next, add binders for read effects of E

         Count := Raw_Binders'Length + 1;
         for R of Read_Names loop
            declare
               Entity : constant Entity_Id := Find_Entity (R);
            begin
               --  For state abstractions pretend there is no Entity

               if Present (Entity)
                 and then Ekind (Entity) /= E_Abstract_State
                 and then Entity_In_SPARK (Entity)
               then
                  Result (Count) :=
                    (Regular,
                     (Ada_Node => Entity,
                      B_Name   =>
                        New_Identifier
                          (Name => Full_Name (Entity),
                           Typ  => Type_Of_Node (Etype (Entity))),
                      B_Ent    => Null_Entity_Name,
                      Mutable  => False));
               else
                  Result (Count) :=
                    (Regular,
                     (Ada_Node => Empty,
                      B_Name   =>
                        New_Identifier
                          (Name => To_String (R),
                           Typ  => To_Why_Type (To_String (R))),
                      B_Ent    => R,
                      Mutable  => False));
               end if;
            end;
            Count := Count + 1;
         end loop;

         return Result;
      end;
   end Add_Logic_Binders;

   -------------------------
   -- Compute_Raw_Binders --
   -------------------------

   function Compute_Raw_Binders (E : Entity_Id) return Item_Array is
      Params        : constant List_Id :=
        (if Is_Entry (E) then Parameter_Specifications (Parent (E))
         else Parameter_Specifications (Subprogram_Specification (E)));
      Ada_Param_Len : constant Natural := Natural (List_Length (Params));
      Binder_Len    : constant Natural :=
        Ada_Param_Len + (if Is_Protected_Subprogram (E) then 1 else 0);
      Result        : Item_Array (1 .. Binder_Len);
      Param         : Node_Id;
      Count         : Positive;

   begin
      Param := First (Params);
      Count := 1;

      if Is_Protected_Subprogram (E) then
         declare
            Prot : constant Entity_Id := Containing_Protected_Type (E);
         begin
            Result (1) := (Concurrent_Self, Concurrent_Self_Binder (Prot));
            Count := 2;
         end;
      end if;

      while Present (Param) loop
         Result (Count) := Mk_Item_Of_Entity
           (E           => Defining_Identifier (Param),
            Local       => True,
            In_Fun_Decl => True);
         Next (Param);
         Count := Count + 1;
      end loop;

      return Result;
   end Compute_Raw_Binders;

   --------------------------------------
   -- Compute_Contract_Cases_Guard_Map --
   --------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  This helper subprogram stores in Guard_Map a map from guard expressions
   --  to temporary Why names. The temporary Why name for the OTHERS case
   --  is stored in Others_Guard_Ident, and the value of this guard in
   --  Others_Guard_Expr. These results will be used to generate bindings
   --  such as:

   --    let guard1 = ... in
   --    let guard2 = ... in
   --    ...
   --    let guardN = ... in
   --    let guardOTHERS = not (guard1 or guard2 ... or guardN) in

   procedure Compute_Contract_Cases_Guard_Map
     (E                  : Entity_Id;
      Guard_Map          : out Ada_To_Why_Ident.Map;
      Others_Guard_Ident : out W_Identifier_Id;
      Others_Guard_Expr  : out W_Expr_Id)
   is
      Prag          : constant Node_Id :=
        Get_Pragma (E, Pragma_Contract_Cases);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

   begin
      --  Initial values for outputs related to the "others" guard if any

      Others_Guard_Ident := Why_Empty;
      Others_Guard_Expr := New_Literal (Domain => EW_Term, Value  => EW_False);

      --  If no Contract_Cases on this subprogram, nothing to do

      if No (Prag) then
         return;
      end if;

      --  Process individual contract cases

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         declare
            --  Temporary Why name for the current guard
            Guard_Ident : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => EW_Bool_Type);

            --  Whether the current guard is enabled
            Enabled     : constant W_Expr_Id := +Guard_Ident;

         begin
            Case_Guard := First (Choices (Contract_Case));

            --  The OTHERS choice requires special processing

            if Nkind (Case_Guard) = N_Others_Choice then
               Others_Guard_Ident := Guard_Ident;
               Others_Guard_Expr := New_Not (Domain => EW_Pred,
                                             Right  => Others_Guard_Expr);

            --  Regular contract case

            else
               Guard_Map.Include (Case_Guard, Guard_Ident);
               Others_Guard_Expr := New_Or_Expr (Left   => Others_Guard_Expr,
                                                 Right  => Enabled,
                                                 Domain => EW_Term);
            end if;

            Next (Contract_Case);
         end;
      end loop;
   end Compute_Contract_Cases_Guard_Map;

   -----------------------------------------
   -- Compute_Contract_Cases_Entry_Checks --
   -----------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  leads to the generation of checks on subprogram entry. In a context
   --  where the precondition is known to hold, it is checked that no
   --  evaluation of a guard can lead to a run-time error, that no more than
   --  one guard evaluates to True (only if there are at least two non-OTHER
   --  guards), and that at least one guard evaluates to True (only in the case
   --  there is no OTHERS).

   --  Check that contract cases are disjoint only if there are at least two
   --  non-OTHER guards:

   --    assert ((if guard1 = True then 1 else 0) +
   --            (if guard2 = True then 1 else 0) +
   --            ...
   --            (if guardN = True then 1 else 0) <= 1)

   --  Check that contract cases are complete only if there is no OTHERS:

   --    assert ((if guard1 = True then 1 else 0) +
   --            (if guard2 = True then 1 else 0) +
   --            ...
   --            (if guardN = True then 1 else 0) >= 1)

   function Compute_Contract_Cases_Entry_Checks
     (E         : Entity_Id;
      Guard_Map : Ada_To_Why_Ident.Map) return W_Prog_Id
   is
      Prag          : constant Node_Id :=
        Get_Pragma (E, Pragma_Contract_Cases);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

      Has_Others  : Boolean := False;
      --  Set to True if there is an OTHERS guard

      Count       : W_Expr_Id := New_Integer_Constant (Value => Uint_0);
      --  Count of the guards enabled

      Result      : W_Prog_Id := +Void;
      --  Why program for these checks

   --  Start of processing for Compute_Contract_Cases_Entry_Checks

   begin
      --  If no Contract_Cases on this subprogram, return the void program

      if No (Prag) then
         return Result;
      end if;

      --  Process individual contract cases

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choices (Contract_Case));

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
               Enabled     : constant W_Expr_Id :=
                 New_Conditional
                   (Ada_Node    => Case_Guard,
                    Domain      => EW_Term,
                    Condition   =>
                      New_Call
                        (Domain => EW_Pred,
                         Name   => Why_Eq,
                         Args   => (1 => +Guard_Ident,
                                    2 => New_Literal (Domain => EW_Term,
                                                      Value  => EW_True)),
                         Typ    => EW_Bool_Type),
                    Then_Part   => New_Integer_Constant (Value => Uint_1),
                    Else_Part   => New_Integer_Constant (Value => Uint_0));
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
         Result := Sequence
           (Result,
            New_Assert
              (Pred     =>
                   +New_VC_Expr
                 (Prag,
                  New_Call
                    (Name => Int_Infix_Le,
                     Typ  => EW_Bool_Type,
                     Domain => EW_Pred,
                     Args =>
                       (+Count, New_Integer_Constant (Value => Uint_1))),
                  VC_Disjoint_Contract_Cases,
                  EW_Pred),
            Assert_Kind => EW_Check));
      end if;

      --  A check that contract cases are complete is generated only when there
      --  is no OTHER guard.

      if not Has_Others then
         Result := Sequence
           (Result,
            New_Assert
              (Pred       =>
                   +New_VC_Expr
                 (Prag,
                  New_Call
                    (Domain => EW_Pred,
                     Typ    => EW_Bool_Type,
                     Name   => Int_Infix_Ge,
                     Args => (+Count,
                              New_Integer_Constant (Value => Uint_1))),
                  VC_Complete_Contract_Cases,
                  EW_Pred),
               Assert_Kind => EW_Check));
      end if;

      return New_Ignore (Prog => Result);
   end Compute_Contract_Cases_Entry_Checks;

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
     (Params             : Transformation_Params;
      E                  : Entity_Id;
      Guard_Map          : Ada_To_Why_Ident.Map;
      Others_Guard_Ident : W_Identifier_Id) return W_Prog_Id
   is
      Prag          : constant Node_Id :=
        Get_Pragma (E, Pragma_Contract_Cases);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

      function Do_One_Contract_Case
        (Contract_Case : Node_Id;
         Enabled       : W_Expr_Id) return W_Prog_Id;
      --  Returns the Why program checking absence of run-time errors and
      --  function verification of the given Contract_Case. Enabled is a
      --  boolean term.

      function Do_One_Contract_Case
        (Contract_Case : Node_Id;
         Enabled       : W_Expr_Id) return W_Prog_Id
      is
         Consequence  : constant Node_Id := Expression (Contract_Case);

         --  Enabled must be converted to a predicate to be used as the
         --  condition in an if-expr inside a predicate.
         Enabled_Pred : constant W_Expr_Id :=
           New_Call
             (Domain => EW_Pred,
              Name   => Why_Eq,
              Typ    => EW_Bool_Type,
              Args   => (+Enabled,
                         New_Literal (Domain => EW_Term,
                                      Value  => EW_True)));
      begin
         return Sequence
           (New_Ignore
              (Prog =>
                 +W_Expr_Id'(New_Conditional
                   (Ada_Node    => Contract_Case,
                    Domain      => EW_Prog,
                    Condition   => Enabled,
                    Then_Part   =>
                      +Transform_Expr (Consequence, EW_Prog, Params),
                    Else_Part   =>
                      New_Literal (Domain => EW_Prog,
                                   Value  => EW_True)))),
            New_Assert
              (Pred => +New_VC_Expr
                 (Contract_Case,
                  New_Conditional
                    (Ada_Node    => Contract_Case,
                     Domain      => EW_Pred,
                     Condition   => Enabled_Pred,
                     Then_Part   =>
                       +Transform_Expr (Consequence, EW_Pred, Params)),
                    VC_Contract_Case,
                    EW_Pred),
               Assert_Kind => EW_Assert));
      end Do_One_Contract_Case;

      Result : W_Prog_Id := +Void;

   --  Start of processing for Compute_Contract_Cases_Exit_Checks

   begin
      --  If no Contract_Cases on this subprogram, return

      if No (Prag) then
         return Result;
      end if;

      --  Process individual contract cases

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choices (Contract_Case));

         declare
            --  Temporary Why name for the current guard
            Guard_Ident : constant W_Identifier_Id :=
              (if Nkind (Case_Guard) = N_Others_Choice then
                 Others_Guard_Ident
               else
                 Guard_Map.Element (Case_Guard));

            --  Whether the current guard is enabled
            Enabled     : constant W_Expr_Id := +Guard_Ident;

         begin
            Result := Sequence
              (Result, Do_One_Contract_Case (Contract_Case, Enabled));
         end;

         Next (Contract_Case);
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
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Pred_Id
   is
      Prag          : constant Node_Id :=
        Get_Pragma (E, Pragma_Contract_Cases);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;
      Consequence   : Node_Id;

      Result : W_Pred_Id := New_Literal (Value => EW_True);

   --  Start of processing for Compute_Contract_Cases_Postcondition

   begin
      --  If no Contract_Cases on this subprogram, return True

      if No (Prag) then
         return Result;
      end if;

      --  Process individual contract cases in reverse order, to create the
      --  proper if-elsif Why predicate.

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := Last (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choices (Contract_Case));
         Consequence := Expression (Contract_Case);

         --  The "others" choice requires special processing

         if Nkind (Case_Guard) = N_Others_Choice then
            Result := +Transform_Expr (Consequence, EW_Pred, Params);

         --  Regular contract case

         else
            declare
               --  Whether the current guard is enabled in the pre-state

               Enabled : constant W_Expr_Id :=
                 Transform_Attribute_Old (Case_Guard, EW_Pred, Params);
            begin
               Result := New_Conditional
                 (Condition   => Enabled,
                  Then_Part   =>
                    +Transform_Expr (Consequence, EW_Pred, Params),
                  Else_Part   => +Result);
            end;
         end if;

         Prev (Contract_Case);
      end loop;

      return Result;
   end Compute_Contract_Cases_Postcondition;

   --------------------------
   -- Compute_Inlined_Expr --
   --------------------------

   function Compute_Inlined_Expr
     (Function_Entity    : Entity_Id;
      Logic_Func_Binders : Item_Array;
      W_Return_Type      : W_Type_Id;
      File               : W_Section_Id) return W_Expr_Id
   is
      Value  : constant Node_Id :=
        Retrieve_Inline_Annotation (Function_Entity);
      Params : constant Transformation_Params :=
        (File        => File,
         Phase       => Generate_Logic,
         Gen_Marker  => False,
         Ref_Allowed => False);
      W_Def  : W_Expr_Id;

   begin
      if No (Value) then
         W_Def := Why_Empty;

      --  If Functon_Entity is recursive, it is not inlined as it may interfere
      --  with its verification.

      elsif Is_Recursive (Function_Entity) then
         Error_Msg_N
           ("?recursive function cannot be inlined for proof",
            Function_Entity);

         W_Def := Why_Empty;
      else

         --  We fill the map of parameters, so that in the definition, we use
         --  local names of the parameters, instead of the global names.

         Ada_Ent_To_Why.Push_Scope (Symbol_Table);

         for Binder of Logic_Func_Binders loop
            declare
               A : constant Node_Id :=
                 (case Binder.Kind is
                     when Regular | Concurrent_Self => Binder.Main.Ada_Node,
                     when others  => raise Program_Error);
               --  in parameters should not be split
            begin
               pragma Assert (Present (A) or else Binder.Kind = Regular);

               if Present (A) then
                  Ada_Ent_To_Why.Insert (Symbol_Table,
                                         Unique_Entity (A),
                                         Binder);
               elsif Binder.Main.B_Ent /= Null_Entity_Name then

                  --  If there is no Ada_Node, this is a binder generated
                  --  from an effect; we add the parameter in the name
                  --  map using its unique name.

                  Ada_Ent_To_Why.Insert
                    (Symbol_Table,
                     Binder.Main.B_Ent,
                     Binder);
               end if;
            end;
         end loop;

         --  Translate the Value expression in Why.

         W_Def := Transform_Expr
           (Expr          => Value,
            Expected_Type => W_Return_Type,
            Domain        => EW_Term,
            Params        => Params);

         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      end if;
      return W_Def;
   end Compute_Inlined_Expr;

   --------------------------
   -- Generate_VCs_For_LSP --
   --------------------------

   procedure Generate_VCs_For_LSP
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Name      : constant String := Full_Name (E);
      Params    : Transformation_Params;

      Inherited_Pre_List  : Node_Lists.List;
      Classwide_Pre_List  : Node_Lists.List;
      Pre_List            : Node_Lists.List;
      Inherited_Post_List : Node_Lists.List;
      Classwide_Post_List : Node_Lists.List;
      Post_List           : Node_Lists.List;

      Inherited_Pre_Spec   : W_Pred_Id;
      Classwide_Pre_Spec   : W_Pred_Id;
      Pre_Spec             : W_Pred_Id;
      Inherited_Post_Spec  : W_Pred_Id;
      Classwide_Post_Spec  : W_Pred_Id;
      Post_Spec            : W_Pred_Id;

      Inherited_Pre_Assume  : W_Prog_Id;
      Classwide_Pre_Check   : W_Prog_Id;
      Classwide_Pre_Assume  : W_Prog_Id;
      Pre_Check             : W_Prog_Id;
      Pre_Assume            : W_Prog_Id;
      Call_Effects          : W_Prog_Id;
      Post_Assume           : W_Prog_Id;
      Classwide_Post_Check  : W_Prog_Id;
      Classwide_Post_Assume : W_Prog_Id;
      Inherited_Post_Check  : W_Prog_Id;

      Why_Body                : W_Prog_Id := +Void;
      Classwide_Pre_RTE       : W_Prog_Id := +Void;
      Classwide_Weaker_Pre    : W_Prog_Id := +Void;
      Weaker_Pre              : W_Prog_Id := +Void;
      Stronger_Post           : W_Prog_Id := +Void;
      Classwide_Post_RTE      : W_Prog_Id := +Void;
      Stronger_Classwide_Post : W_Prog_Id := +Void;

   begin
      Open_Theory (File,
                   New_Module
                     (Name => NID (Name & "__subprogram_lsp"),
                      File => No_Name),
                   Comment =>
                     "Module for checking LSP for subprogram "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Current_Subp := E;

      --  First, clear the list of translations for X'Old expressions, and
      --  create a new identifier for F'Result.

      Reset_Map_For_Old;

      if Ekind (E) = E_Function then
         Result_Name :=
           New_Identifier
             (Name => Name & "__result", Typ => Type_Of_Node (Etype (E)));
      end if;

      Params :=
        (File        => File,
         Phase       => Generate_VCs_For_Contract,
         Gen_Marker  => False,
         Ref_Allowed => True);

      --  First retrieve contracts specified on the subprogram and the
      --  subprograms it overrides.

      Inherited_Pre_List := Find_Contracts
        (E, Pragma_Precondition, Inherited => True);
      Classwide_Pre_List := Find_Contracts
        (E, Pragma_Precondition, Classwide => True);
      Pre_List := Find_Contracts (E, Pragma_Precondition);

      Inherited_Post_List := Find_Contracts
        (E, Pragma_Postcondition, Inherited => True);
      Classwide_Post_List := Find_Contracts
        (E, Pragma_Postcondition, Classwide => True);
      Post_List := Find_Contracts (E, Pragma_Postcondition);

      --  Then, generate suitable predicates based on the specified contracts,
      --  with appropriate True defaults.

      Inherited_Pre_Spec :=
        +Compute_Spec (Params, Inherited_Pre_List, EW_Pred);
      Classwide_Pre_Spec :=
        +Compute_Spec (Params, Classwide_Pre_List, EW_Pred);
      Pre_Spec := +Compute_Spec (Params, Pre_List, EW_Pred);

      Inherited_Post_Spec :=
        +Compute_Spec (Params, Inherited_Post_List, EW_Pred);
      Classwide_Post_Spec :=
        +Compute_Spec (Params, Classwide_Post_List, EW_Pred);
      Post_Spec := +Compute_Spec (Params, Post_List, EW_Pred);

      --  Compute the effect of a call of the subprogram

      Call_Effects := New_Havoc_Statement
        (Ada_Node => E,
         Effects  => +Compute_Effects (E, Global_Params => True));

      Call_Effects := Sequence
        (Call_Effects,
         New_Assume_Statement
           (Ada_Node => E,
            Pred     => Compute_Dynamic_Property_For_Effects (E, Params)));

      --  If E has a class-wide precondition, check that it cannot raise a
      --  run-time error in an empty context.

      if not Classwide_Pre_List.Is_Empty then
         Classwide_Pre_RTE :=
           +Compute_Spec (Params, Classwide_Pre_List, EW_Prog);
         Classwide_Pre_RTE :=
           New_Abstract_Expr (Expr => Classwide_Pre_RTE, Post => True_Pred);
      end if;

      --  If E is overriding another subprogram, check that its specified
      --  classwide precondition is weaker than the inherited one.

      if Is_Overriding_Subprogram (E)
        and then not Classwide_Pre_List.Is_Empty
      then
         Inherited_Pre_Assume :=
           New_Assume_Statement (Pred => Inherited_Pre_Spec);

         Classwide_Pre_Check := New_Located_Assert
           (Ada_Node => Get_Location_For_Aspect (E, Pragma_Precondition,
                                                 Classwide => True),
            Pred     => Classwide_Pre_Spec,
            Reason   => VC_Weaker_Classwide_Pre,
            Kind     => EW_Assert);

         Classwide_Weaker_Pre := Sequence
           ((1 => New_Comment (Comment =>
                               NID ("Checking that class-wide precondition is"
                                  & " implied by inherited precondition")),
             2 => Inherited_Pre_Assume,
             3 => Classwide_Pre_Check));

         Classwide_Weaker_Pre :=
           New_Abstract_Expr (Expr => Classwide_Weaker_Pre, Post => True_Pred);
      end if;

      --  If E has a specific precondition, check that it is weaker than the
      --  dispatching one.

      if not Pre_List.Is_Empty then
         Classwide_Pre_Assume :=
           New_Assume_Statement (Pred =>
             Get_LSP_Contract (Params, E, Pragma_Precondition));

         Pre_Check := New_Located_Assert
           (Ada_Node => Get_Location_For_Aspect (E, Pragma_Precondition),
            Pred     => Pre_Spec,
            Reason   => (if Classwide_Pre_List.Is_Empty and then
                            Inherited_Pre_List.Is_Empty
                         then
                           VC_Trivial_Weaker_Pre
                         else
                           VC_Weaker_Pre),
            Kind     => EW_Assert);

         Weaker_Pre := Sequence
           ((1 => New_Comment (Comment =>
                               NID ("Checking that precondition is"
                                  & " implied by class-wide precondition")),
             2 => Classwide_Pre_Assume,
             3 => Pre_Check));

         Weaker_Pre :=
           New_Abstract_Expr (Expr => Weaker_Pre, Post => True_Pred);
      end if;

      --  If E has a specific postcondition, check that it is stronger than the
      --  dispatching one. To that end, perform equivalent effects of call in
      --  context of precondition for static call.
      --  Skip this check if the dispatching postcondition is the default True
      --  postcondition.

      if not Post_List.Is_Empty
        and then not (Classwide_Post_List.Is_Empty
                        and then
                      Inherited_Post_List.Is_Empty)
      then
         Pre_Assume :=
           New_Assume_Statement (Pred =>
             Get_Static_Call_Contract (Params, E, Pragma_Precondition));

         Post_Assume := New_Assume_Statement (Pred => Post_Spec);

         Classwide_Post_Check := New_Located_Assert
           (Ada_Node => Get_Location_For_Aspect (E, Pragma_Postcondition),
            Pred     =>
              Get_LSP_Contract (Params, E, Pragma_Postcondition),
            Reason   => VC_Stronger_Post,
            Kind     => EW_Assert);

         Stronger_Post := Sequence
           ((1 => New_Comment (Comment =>
                                 NID ("Simulate static call to subprogram "
                                 & """" & Get_Name_String (Chars (E)) & """")),
             2 => Pre_Assume,
             3 => Call_Effects,
             4 => New_Comment (Comment =>
                               NID ("Checking that class-wide postcondition is"
                                  & " implied by postcondition")),
             5 => Post_Assume,
             6 => Classwide_Post_Check));

         Stronger_Post :=
           New_Abstract_Expr (Expr => Stronger_Post, Post => True_Pred);
      end if;

      --  If E is overriding another subprogram, check that its specified
      --  classwide postcondition is stronger than the inherited one. Also
      --  check that the class-wide postcondition cannot raise runtime errors.
      --  To that end, perform equivalent effects of call in an empty context.
      --  Note that we should *not* assume the dispatching precondition for
      --  this check, as this would not be transitive.

      if not Classwide_Post_List.Is_Empty then
         Classwide_Post_RTE :=
           +Compute_Spec (Params, Classwide_Post_List, EW_Prog);
         Classwide_Post_RTE :=
           New_Abstract_Expr (Expr => Classwide_Post_RTE, Post => True_Pred);
         Classwide_Post_RTE := Sequence
           ((1 => Call_Effects,
             2 => Classwide_Post_RTE));

         if Is_Overriding_Subprogram (E) then
            Classwide_Post_Assume :=
              New_Assume_Statement (Pred => Classwide_Post_Spec);

            Inherited_Post_Check := New_Located_Assert
              (Ada_Node => Get_Location_For_Aspect (E, Pragma_Postcondition,
                                                    Classwide => True),
               Pred     => Inherited_Post_Spec,
               Reason   => VC_Stronger_Classwide_Post,
               Kind     => EW_Assert);

            Stronger_Classwide_Post := Sequence
              ((1 => New_Comment (Comment =>
                               NID ("Checking that inherited postcondition is"
                                  & " implied by class-wide postcondition")),
                2 => Call_Effects,
                3 => Classwide_Post_Assume,
                4 => Inherited_Post_Check));

            Stronger_Classwide_Post :=
              New_Abstract_Expr
                (Expr => Stronger_Classwide_Post, Post => True_Pred);
         end if;
      end if;

      Why_Body := Sequence
        ((1 => Classwide_Pre_RTE,
          2 => Classwide_Weaker_Pre,
          3 => Weaker_Pre,
          4 => Stronger_Post,
          5 => Classwide_Post_RTE,
          6 => Stronger_Classwide_Post));

      --  Assume dynamic property of inputs before the checks

      Why_Body := Sequence
        (Compute_Dynamic_Property_For_Inputs (Params => Params,
                                              E      => E),
         Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Body, E, Params);

      --  Declare a global variable to hold the result of a function

      if Ekind (E) = E_Function then
         Emit
           (File,
            New_Global_Ref_Declaration
              (Ada_Node => E,
               Name     => Result_Name,
               Labels   => Get_Counterexample_Labels (E),
               Ref_Type => Type_Of_Node (Etype (E))));
      end if;

      --  add declarations for 'Old variables

      Why_Body := Bind_From_Mapping_In_Expr
        (Params                 => Params,
         Map                    => Map_For_Old,
         Expr                   => Why_Body,
         Do_Runtime_Error_Check => False,
         Bind_Value_Of_Old      => True);

      declare
         Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Cur_Subp_Sloc);
      begin
         Label_Set.Include (NID ("W:diverges:N"));
         Emit (File,
               Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Prog,
                  Name    => Def_Name,
                  Binders => (1 => Unit_Param),
                  Labels  => Label_Set,
                  Def     => +Why_Body));
      end;

      --  We should *not* filter our own entity, it is needed for recursive
      --  calls.

      if Ekind (E) = E_Function then
         Result_Name := Why_Empty;
      end if;

      Close_Theory (File,
                    Kind => VC_Generation_Theory,
                    Defined_Entity => E);
   end Generate_VCs_For_LSP;

   ------------------------------------------
   -- Generate_VCs_For_Package_Elaboration --
   ------------------------------------------

   procedure Generate_VCs_For_Package_Elaboration
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Name       : constant String  := Full_Name (E);
      Spec_N     : constant Node_Id := Package_Specification (E);
      Body_N     : constant Node_Id := Package_Body (E);
      Vis_Decls  : constant List_Id := Visible_Declarations (Spec_N);
      Priv_Decls : constant List_Id := Private_Declarations (Spec_N);
      Init_Cond  : constant Node_Id :=
        Get_Pragma (E, Pragma_Initial_Condition);
      Params     : Transformation_Params;

      Why_Body   : W_Prog_Id := +Void;
      Post       : W_Pred_Id;

   begin
      --  We open a new theory, so that the context is fresh for that package

      Open_Theory (File,
                   New_Module
                     (Name => NID (Name & "__package_def"),
                      File => No_Name),
                   Comment =>
                     "Module for checking absence of run-time errors and "
                       & "package initial condition on package elaboration of "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);
      Current_Subp := E;

      Register_VC_Entity (E);

      Params := (File        => File,
                 Phase       => Generate_VCs_For_Body,
                 Gen_Marker  => False,
                 Ref_Allowed => True);

      --  Translate initial condition of E

      if Present (Init_Cond) then
         declare
            Expr : constant Node_Id :=
              Expression (First (Pragma_Argument_Associations (Init_Cond)));
         begin
            --  Generate postcondition for generated subprogram, that
            --  corresponds to the initial condition of the package.

            Params.Phase := Generate_Contract_For_Body;
            Post := +Transform_Expr (Expr, EW_Bool_Type, EW_Pred, Params);
            Post :=
              +New_VC_Expr (Init_Cond, +Post, VC_Initial_Condition, EW_Pred);

            --  Generate program to check the absence of run-time errors in the
            --  initial condition.

            Params.Phase := Generate_VCs_For_Contract;
            Why_Body :=
              +Transform_Expr (Expr, EW_Bool_Type, EW_Prog, Params);
         end;

      --  No initial condition, so no postcondition for the generated
      --  subprogram.

      else
         Post := True_Pred;
      end if;

      --  Translate declarations and statements in the package body, if there
      --  is one and it is in SPARK.

      if Present (Body_N) and then
        Entity_Body_In_SPARK (E)
      then
         if Present (Handled_Statement_Sequence (Body_N)) and then
           Body_Statements_In_SPARK (E)
         then
            Why_Body :=
              Sequence
                (Transform_Statements_And_Declarations
                   (Statements (Handled_Statement_Sequence (Body_N))),
                 Why_Body);
         end if;

         Why_Body :=
           Transform_Declarations_Block (Declarations (Body_N), Why_Body);
      end if;

      --  Introduce a check for the type invariant of all the variables
      --  initialized by the package.

      declare
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => False,
            Ref_Allowed => True);
         Check : constant W_Pred_Id :=
           Compute_Type_Invariants_For_Package (E, Params);
      begin
         if not Is_True_Boolean (+Check) then
            Why_Body :=
              Sequence
                (Why_Body,
                 New_Assert
                   (Pred        => New_Label
                      (Labels => New_VC_Labels (E, VC_Invariant_Check),
                       Def    => +Check),
                    Assert_Kind => EW_Assert));
         end if;
      end;

      --  Translate public and private declarations of the package

      if Present (Priv_Decls) and then
        Private_Spec_In_SPARK (E)
      then
         Why_Body := Transform_Declarations_Block (Priv_Decls, Why_Body);
      end if;

      if Present (Vis_Decls) then
         Why_Body := Transform_Declarations_Block (Vis_Decls, Why_Body);
      end if;

      --  Assume initial conditions of withed units.
      --  ??? Currently, we only assume initial conditions of withed units
      --  on compilation units though it is also valid for library level
      --  packages. This is because it does not seem relevant for nested
      --  packages. It may be interesting to rather inline them.

      if Is_Compilation_Unit (E) then
         Params.Phase := Generate_VCs_For_Contract;
         Why_Body := Sequence
           (Assume_Initial_Condition_Of_Withed_Units (E, Params), Why_Body);
      end if;

      --  We assume that objects used in the program are in range, if
      --  they are of a dynamic type.

      Params.Phase := Generate_VCs_For_Contract;

      Why_Body :=
        Sequence
          (Compute_Dynamic_Property_For_Inputs (Params => Params,
                                                E      => E),
           Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Body, E, Params);

      declare
         Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Cur_Subp_Sloc);
      begin
         Label_Set.Include (NID ("W:diverges:N"));
         Emit (File,
                Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Prog,
                  Name    => Def_Name,
                  Binders => (1 => Unit_Param),
                  Labels  => Label_Set,
                  Post    => Post,
                  Def     => +Why_Body));
      end;

      Close_Theory (File,
                    Kind => VC_Generation_Theory);
   end Generate_VCs_For_Package_Elaboration;

   -------------------------------------
   -- Generate_VCs_For_Protected_Type --
   -------------------------------------

   procedure Generate_VCs_For_Protected_Type
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      type Discr is record
         Id  : W_Identifier_Id;
         Val : W_Expr_Id;
      end record;
      --  Why3 representation of discriminants

      package Discriminant_Lists is new
        Ada.Containers.Doubly_Linked_Lists
          (Element_Type => Discr);

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

         if Has_Discriminants (E)
           or else Has_Unknown_Discriminants (E)
         then
            Discr_N := First_Discriminant (E);
         end if;

         while Present (Discr_N) loop
            declare
               Discr_W : constant Discr :=
                 (Id =>
                    New_Temp_Identifier
                      (Typ =>
                           EW_Abstract (Etype (Discr_N))),

                  Val =>
                    New_Ada_Record_Access
                      (Ada_Node => Empty,
                       Domain   => EW_Term,
                       Name     => +Self_Name,
                       Field    => Discr_N,
                       Ty       => E));
            begin
               Insert_Entity (Discriminal (Discr_N),
                              Discr_W.Id);

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
              +New_Typed_Binding
                 (Domain   => EW_Term,
                  Name     => W_D.Id,
                  Def      => W_D.Val,
                  Context  => +Expr);
         end loop;
         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      end Wrap_Discr;

      Why_Body   : W_Prog_Id := +Void;
      Name       : constant String  := Full_Name (E);
      Priv_Decls : constant List_Id := Private_Declarations_Of_Prot_Type (E);
      Vis_Decls  : constant List_Id := Visible_Declarations_Of_Prot_Type (E);

   --  Start of processing for Generate_VCs_For_Protected_Type

   begin
      --  We open a new theory, so that the context is fresh for this task

      Open_Theory (File,
                   New_Module
                     (Name => NID (Name & "__protected_type"),
                      File => No_Name),
                   Comment =>
                     "Module for various checks related to the protected type "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);
      Current_Subp := E;

      Register_VC_Entity (E);

      --  The Ada_Node is important here, because that's how we detect
      --  occurrences of "self" in a term later.

      Self_Name :=
        New_Identifier
          (Name     => "self__",
           Ada_Node => E,
           Typ      => Type_Of_Node (E));

      Emit (File,
            Why.Gen.Binders.New_Function_Decl
              (Domain  => EW_Term,
               Name    => Self_Name,
               Binders => (1 .. 0 => <>),
               Labels  => Name_Id_Sets.Empty_Set,
               Return_Type => Get_Typ (Self_Name)));

      --  ??? Where is the call to Push_Scope?

      Prepare_Discr;

      --  If protected object attaches an interrupt, the priority must be in
      --  range of System.Interrupt_Priorioty; see RM C.3.1(11/3).

      if Requires_Interrupt_Priority (E) then
         declare
            P : constant Node_Id :=
              Get_Priority_Or_Interrupt_Priority (E);
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

                  Why_Body := Sequence
                    (Why_Body,
                     New_Located_Assert
                       (Ada_Node => E,
                        Pred     =>
                          +New_Range_Expr
                          (Domain => EW_Pred,
                           Low    =>
                             New_Attribute_Expr
                               (Domain => EW_Term,
                                Ty     =>
                                  RTE (RE_Interrupt_Priority),
                                Attr   => Attribute_First,
                                Params => Body_Params),
                           High   =>
                             New_Attribute_Expr
                               (Domain => EW_Term,
                                Ty     =>
                                  RTE (RE_Interrupt_Priority),
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

      Why_Body := Sequence (Why_Body,
                            Compute_Attach_Handler_Check
                              (Base_Type (E), Body_Params));

      --  Translate public and private declarations of the package

      if Present (Priv_Decls) and then
        Private_Spec_In_SPARK (E)
      then
         --  Check for absence of runtime error in protected components initial
         --  values.

         declare
            Checks  : W_Prog_Id := +Void;
            F_Check : W_Prog_Id;
         begin
            for Field of Get_Component_Set (E) loop
               if Ekind (Field) in E_Component | E_Discriminant then

                  if Present (Expression (Parent (Field))) then

                     --  If Field has a default expression, use it

                     F_Check := +Transform_Expr
                       (Expr          => Expression (Parent (Field)),
                        Expected_Type => Type_Of_Node (Etype (Field)),
                        Domain        => EW_Prog,
                        Params        => Body_Params);
                  else

                     --  Otherwise, use its Field's Etype default value

                     F_Check :=
                       Compute_Default_Check (Etype (Field), Body_Params);
                  end if;

                  if F_Check /= +Void then
                     Checks := Sequence
                       (Left  => Checks,
                        Right => New_Ignore
                          (Ada_Node => Etype (Field),
                           Prog     => F_Check));
                  end if;
               end if;
            end loop;
            Why_Body := Sequence (Why_Body, Checks);
         end;

         Why_Body := Transform_Declarations_Block (Priv_Decls, Why_Body);
      end if;

      if Present (Vis_Decls) then
         Why_Body := Transform_Declarations_Block (Vis_Decls, Why_Body);
      end if;

      Wrap_Discr (Why_Body);

      declare
         Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Cur_Subp_Sloc);
      begin
         Label_Set.Include (NID ("W:diverges:N"));
         Emit (File,
                Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Prog,
                  Name    => Def_Name,
                  Binders => (1 => Unit_Param),
                  Labels  => Label_Set,
                  Def     => +Why_Body));
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      Self_Name := Why_Empty;
      Self_Is_Mutable := False;

      Close_Theory (File,
                    Kind => VC_Generation_Theory);
   end Generate_VCs_For_Protected_Type;

   ---------------------------------
   -- Generate_VCs_For_Subprogram --
   ---------------------------------

   procedure Generate_VCs_For_Subprogram
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Body_N : constant Node_Id := Get_Body (E);

      function Assume_For_Input return W_Prog_Id;
      --  Generate assumptions for dynamic types used in the program. An
      --  exception is made for predicate functions generated by the frontend,
      --  for which we should not assume that the predicate holds for checking
      --  the absence of RTE in the predicate itself.
      --  Also assume the type invariants of global inputs of E and of global
      --  parameters if E is a boundary subprogram.

      function Assume_Init_Cond_Of_Withed_Units return W_Prog_Id;
      --  For compilation units, generate assumptions for Initial conditions of
      --  withed units

      function Comp_Decl_At_Subp_Start return W_Prog_Id;
      --  The body of the subprogram may contain declarations that are in fact
      --  essential to prove absence of RTE in the pre, e.g. compiler-generated
      --  subtype declarations. We need to take those into account.

      function RTE_Of_Pre return W_Prog_Id;
      --  Compute an expression which contains the RTE checks of the
      --  precondition.

      function Assume_Or_Assert_Of_Pre return W_Prog_Id;
      --  usually assumes the precondition, except for main programs where
      --  the precondition needs to be proved in fact. In this latter case
      --  an assertion is returned instead of an assumption.

      function Check_Invariants_Of_Outputs return W_Prog_Id;
      --  Checks the type invariants of global output and of out parameters if
      --  E is a boundary subprogram.

      function Checking_Of_Refined_Post (Arg : W_Prog_Id) return W_Prog_Id;
      --  Encapsulate the translated body inside an abstract program with
      --  the Refined_Post as a postcondition.
      --  Assume the dynamic property of modified variables after the call.

      function Post_As_Pred return W_Pred_Id;
      --  compute the postcondition predicate based on the Ada postcondition

      function Try_Block (Prog : W_Prog_Id) return W_Prog_Id;
      --  adding try/catch block for the return exception on top of the program

      Pre_Prags  : Node_Lists.List;
      Post_Prags : Node_Lists.List;

      procedure Get_Pre_Post_Pragmas (Decls : Node_Lists.List);
      --  Retrieve pragmas Precondition and Postcondition from the list
      --  of body declarations, and add them to Pre_Prags and Post_Prags
      --  when they do not come from aspects.

      function Transform_All_Pragmas
        (Prags   : Node_Lists.List;
         Comment : String) return W_Prog_Id;
      --  Translate the pragma list in Prags into Why3.

      --  Mapping from guards to temporary names, and Why program to check
      --  contract cases on exit.
      Guard_Map          : Ada_To_Why_Ident.Map;
      Others_Guard_Ident : W_Identifier_Id;
      Others_Guard_Expr  : W_Expr_Id;

      function CC_And_RTE_Post return W_Prog_Id;
      --  return verification of the contract cases, plus runtime checks for
      --  the Post

      Body_Params     : Transformation_Params;
      Contract_Params : Transformation_Params;

      function Declare_Old_Variables (P : W_Prog_Id) return W_Prog_Id;

      function Wrap_Decls_For_CC_Guards (P : W_Prog_Id) return W_Prog_Id;

      ----------------------
      -- Assume_For_Input --
      ----------------------

      function Assume_For_Input return W_Prog_Id is
         Pred_Fun_Param : constant Entity_Id :=
           (if Ekind (E) in E_Function | E_Procedure
            and then Is_Predicate_Function (E)
            then
               Defining_Entity (First (Parameter_Specifications
              (Subprogram_Specification (E))))
            else
               Empty);
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => False,
            Ref_Allowed => True);
      begin
         return
           Sequence
             ((1 => New_Comment
               (Comment => NID ("Assume dynamic invariants of inputs of the"
                & " subprogram"
                & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                   else ""))),
               2 => Compute_Dynamic_Property_For_Inputs
                 (Params         => Params,
                  E              => E,
                  Pred_Fun_Param => Pred_Fun_Param),
               3 => New_Assume_Statement
                 (Pred => Compute_Type_Invariants_For_Subprogram
                    (E         => E,
                     For_Input => True,
                     Params    => Params))));
      end Assume_For_Input;

      --------------------------------------
      -- Assume_Init_Cond_Of_Withed_Units --
      --------------------------------------

      function Assume_Init_Cond_Of_Withed_Units return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => False,
            Ref_Allowed => True);
      begin
         if Is_Compilation_Unit (E) then
            return
              Sequence
                (New_Comment
                   (Comment =>
                          NID ("Assume Initial_Condition of withed units")),
                 Assume_Initial_Condition_Of_Withed_Units (E, Params));
         else
            return +Void;
         end if;
      end Assume_Init_Cond_Of_Withed_Units;

      -----------------------------
      -- Assume_Or_Assert_Of_Pre --
      -----------------------------

      function Assume_Or_Assert_Of_Pre return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => False,
            Ref_Allowed => True);
         Pre : W_Pred_Id :=
           Get_Static_Call_Contract (Params, E, Pragma_Precondition);
         Stmt : W_Prog_Id;
      begin

         --  Need to prove precondition of Main before use. The test for
         --  entries is just to protect the call to Might_Be_Main.

         if not Is_Entry (E) and then Might_Be_Main (E) then
            Stmt :=
              New_Located_Assert
                (Ada_Node => Get_Location_For_Aspect (E, Pragma_Precondition),
                 Pred     => Pre,
                 Reason   => VC_Precondition_Main,
                 Kind     => EW_Assert);
         else
            if Is_Entry (E)
              and then Present (Body_N)
              and then Entity_Body_In_SPARK (E)
            then
               declare
                  Params : constant Transformation_Params :=
                    (File        => File,
                     Phase       => Generate_Contract_For_Body,
                     Gen_Marker  => False,
                     Ref_Allowed => True);
                  Barrier : constant Node_Id :=
                    Condition (Entry_Body_Formal_Part (Body_N));
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
                (Comment => NID ("Assume Pre of the subprogram"
                 & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                   else ""))),
              Stmt);
      end Assume_Or_Assert_Of_Pre;

      ---------------------
      -- CC_And_RTE_Post --
      ---------------------

      function CC_And_RTE_Post return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => False,
            Ref_Allowed => True);
      begin
         return
           Sequence
             (New_Ignore
                (Prog => +Compute_Spec (Params,
                                        E, Pragma_Postcondition, EW_Prog)),
              Compute_Contract_Cases_Exit_Checks
                (Params             => Params,
                 E                  => E,
                 Guard_Map          => Guard_Map,
                 Others_Guard_Ident => Others_Guard_Ident));
      end CC_And_RTE_Post;

      ---------------------------------
      -- Check_Invariants_Of_Outputs --
      ---------------------------------

      function Check_Invariants_Of_Outputs return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => False,
            Ref_Allowed => True);
         Check : constant W_Pred_Id :=
           Compute_Type_Invariants_For_Subprogram (E, False, Params);
      begin
         if Is_True_Boolean (+Check) then
            return +Void;
         else
            return New_Assert
              (Pred =>
                 New_Label (Labels => New_VC_Labels (E, VC_Invariant_Check),
                            Def    => +Check),
               Assert_Kind => EW_Assert);
         end if;
      end Check_Invariants_Of_Outputs;

      ------------------------------
      -- Checking_Of_Refined_Post --
      ------------------------------

      function Checking_Of_Refined_Post (Arg : W_Prog_Id) return W_Prog_Id
      is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => False,
            Ref_Allowed => True);

         Prog : W_Prog_Id := Arg;
      begin
         if Has_Contracts (E, Pragma_Refined_Post) then
            Prog :=
              Sequence
                (Prog,
                 New_Ignore
                   (Prog => +Compute_Spec
                      (Params, E, Pragma_Refined_Post, EW_Prog)));
            Prog :=
              New_Located_Abstract
                (Ada_Node => Get_Location_For_Aspect (E, Pragma_Refined_Post),
                 Expr => Prog,
                 Reason => VC_Refined_Post,
                 Post => +Compute_Spec
                   (Params, E, Pragma_Refined_Post, EW_Pred));
            Prog := Sequence
              (Prog,
               New_Assume_Statement
                 (Pred => Compute_Dynamic_Property_For_Effects (E, Params)));
         end if;
         return Prog;
      end Checking_Of_Refined_Post;

      -----------------------------
      -- Comp_Decl_At_Subp_Start --
      -----------------------------

      function Comp_Decl_At_Subp_Start return W_Prog_Id is
      begin
         if Present (Body_N) and then Entity_Body_In_SPARK (E) then
            return
           Sequence
             ((New_Comment
              (Comment => NID ("Declarations introduced by the compiler at the"
               & " beginning of the subprogram"
               & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                 else ""))),
              Transform_Declarations_For_Params (Declarations (Body_N))));
         else
            return +Void;
         end if;
      end Comp_Decl_At_Subp_Start;

      ---------------------------
      -- Declare_Old_Variables --
      ---------------------------

      function Declare_Old_Variables (P : W_Prog_Id) return W_Prog_Id is
      begin
         return
           Bind_From_Mapping_In_Expr
             (Params                 => Body_Params,
              Map                    => Map_For_Old,
              Expr                   => P,
              Guard_Map              => Guard_Map,
              Others_Guard_Ident     => Others_Guard_Ident,
              Do_Runtime_Error_Check => True,
              Bind_Value_Of_Old      => True);
      end Declare_Old_Variables;

      --------------------------
      -- Get_Pre_Post_Pragmas --
      --------------------------

      procedure Get_Pre_Post_Pragmas (Decls : Node_Lists.List) is
      begin
         for Decl of Decls loop
            if Is_Pragma (Decl, Pragma_Precondition) and then
              not From_Aspect_Specification (Decl)
            then
               Pre_Prags.Append (Decl);

            elsif Is_Pragma (Decl, Pragma_Postcondition) and then
              not From_Aspect_Specification (Decl)
            then
               Post_Prags.Append (Decl);
            end if;
         end loop;
      end Get_Pre_Post_Pragmas;

      ------------------
      -- Post_As_Pred --
      ------------------

      function Post_As_Pred return W_Pred_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_Contract_For_Body,
            Gen_Marker  => False,
            Ref_Allowed => True);
         Mark_Params : Transformation_Params := Params;
         Post_N    : Node_Id;
      begin

         Mark_Params.Gen_Marker := True;

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
            Post_N := E;
         else
            Post_N := Empty;
         end if;
         if Present (Body_N) and then Entity_Body_In_SPARK (E) then

            --  Translate contract of E. A No_Return subprogram, from the
            --  inside, has postcondition true as non termination verification
            --  is done by the frontend, but the precondition is unchanged.

            if No_Return (E) then
               return True_Pred;
            else
               return
                 +New_VC_Expr (Post_N,
                               +Get_Static_Call_Contract
                                 (Mark_Params, E, Pragma_Postcondition),
                               VC_Postcondition,
                               EW_Pred);
            end if;
         else
            return True_Pred;
         end if;
      end Post_As_Pred;

      ----------------
      -- RTE_Of_Pre --
      ----------------

      function RTE_Of_Pre return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => False,
            Ref_Allowed => True);

         Pre   : constant W_Prog_Id :=
           +Compute_Spec (Params, E, Pragma_Precondition, EW_Prog);

      begin
         return
           Sequence
             (New_Comment
                (Comment => NID ("Check for RTE in the Pre of the subprogram"
                 & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                    else ""))),
              New_Ignore
                (Prog => Pre));
      end RTE_Of_Pre;

      ---------------------------
      -- Transform_All_Pragmas --
      ---------------------------

      function Transform_All_Pragmas
        (Prags   : Node_Lists.List;
         Comment : String) return W_Prog_Id
      is
         Result : W_Prog_Id := +Void;
      begin
         for Prag of Prags loop
            Result :=
              Sequence (Result, Transform_Pragma (Prag, Force => True));
         end loop;
         return
           Sequence (New_Comment
                     (Comment => NID (Comment
                      & (if Sloc (E) > 0 then
                           " " & Build_Location_String (Sloc (E))
                        else ""))),
                     Result);
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
                (1 =>
                       New_Handler
                   (Name => M_Main.Return_Exc,
                    Def  => +Void)));
      end Try_Block;

      ------------------------------
      -- Wrap_Decls_For_CC_Guards --
      ------------------------------

      function Wrap_Decls_For_CC_Guards (P : W_Prog_Id) return W_Prog_Id is
         Prog : W_Prog_Id := P;
      begin
         if Present (Others_Guard_Ident) then
            Prog := +New_Typed_Binding (Name    => Others_Guard_Ident,
                                        Domain  => EW_Prog,
                                        Def     => Others_Guard_Expr,
                                        Context => +Prog);
         end if;

         Prog := Bind_From_Mapping_In_Expr
           (Params                 => Contract_Params,
            Map                    => Guard_Map,
            Expr                   => Prog,
            Do_Runtime_Error_Check => True);
         return Prog;
      end Wrap_Decls_For_CC_Guards;

      Name      : constant String := Full_Name (E);

      Prog      : W_Prog_Id;
      Why_Body  : W_Prog_Id;

      Result_Var : W_Prog_Id;

      Raise_Stmt : constant W_Prog_Id :=
        New_Raise
          (Ada_Node => Body_N,
           Name     => M_Main.Return_Exc);

   --  Start of processing for Generate_VCs_For_Subprogram

   begin
      Open_Theory (File,
                   New_Module
                     (Name => NID (Name & "__subprogram_def"),
                      File => No_Name),
                   Comment =>
                     "Module for checking contracts and absence of "
                       & "run-time errors in subprogram "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Current_Subp := E;

      Register_VC_Entity (E);

      Body_Params :=
        (File        => File,
         Phase       => Generate_VCs_For_Body,
         Gen_Marker  => False,
         Ref_Allowed => True);

      Contract_Params :=
        (File        => File,
         Phase       => Generate_VCs_For_Contract,
         Gen_Marker  => False,
         Ref_Allowed => True);

      --  First, clear the list of translations for X'Old expressions, and
      --  create a new identifier for F'Result.

      Reset_Map_For_Old;

      if Ekind (E) = E_Function then
         Result_Name :=
           New_Identifier
             (Name => Name & "__result", Typ => Type_Of_Node (Etype (E)));

         Result_Var :=
           New_Deref
             (Ada_Node => Body_N,
              Right    => Result_Name,
              Typ      => Type_Of_Node (Etype (E)));

      else
         Result_Var := +Void;
      end if;

      if Is_Protected_Subprogram (E) then
         declare
            CPT : constant Entity_Id := Containing_Protected_Type (E);
         begin
            --  The Ada_Node is important here, because that's how we detect
            --  occurrences of "self" in a term later.

            Self_Name :=
              New_Identifier
                (Name     => "self__",
                 Ada_Node => CPT,
                 Typ      => Type_Of_Node (CPT));
            Self_Is_Mutable := True;
         end;
      end if;

      for Expr of Get_Precondition_Expressions (E) loop
         if Nkind (Expr) = N_Identifier
           and then Entity (Expr) = Standard_False
         then
            Error_Msg_N (Msg  => "?precondition is statically false",
                         N    => Expr);
         end if;
      end loop;

      --  If contract cases are present, generate checks for absence of
      --  run-time errors in guards, and check that contract cases are disjoint
      --  and complete. The completeness is checked in a context where the
      --  precondition is assumed. Init_Prog is set to the program up to the
      --  precondition assumption, and Prog is set to the program starting
      --  with the contract case entry checks.

      Compute_Contract_Cases_Guard_Map
        (E                  => E,
         Guard_Map          => Guard_Map,
         Others_Guard_Ident => Others_Guard_Ident,
         Others_Guard_Expr  => Others_Guard_Expr);

      Prog := Compute_Contract_Cases_Entry_Checks (E, Guard_Map);

      if Present (Body_N) and then Entity_Body_In_SPARK (E) then

         Get_Pre_Post_Pragmas
           (Get_Flat_Statement_And_Declaration_List
              (Declarations (Body_N)));

         --  Declare a global variable to hold the result of a function

         if Ekind (E) = E_Function then
            Emit
              (File,
               New_Global_Ref_Declaration
                 (Ada_Node => E,
                  Name     => Result_Name,
                  Labels   => Get_Counterexample_Labels (E),
                  Ref_Type => Type_Of_Node (Etype (E))));
         end if;

         --  Declare global variable to hold the state of a protected object

         if Is_Protected_Subprogram (E) then
            Emit
              (File,
               New_Global_Ref_Declaration
                 (Ada_Node    => Containing_Protected_Type (E),
                  Name        => Self_Name,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Ref_Type =>
                    Type_Of_Node (Containing_Protected_Type (E))));
         end if;

         Why_Body :=
           Sequence
             ((Check_Ceiling_Protocol (Body_Params, E),
              Transform_Declarations_For_Body (Declarations (Body_N)),
              Transform_Statements_And_Declarations
                (Statements
                   (Handled_Statement_Sequence (Body_N))),
              Raise_Stmt));

         --  Enclose the subprogram body in a try-block, so that return
         --  statements can be translated as raising exceptions.

         Why_Body := Try_Block (Why_Body);

         --  Check pragmas Precondition and Postcondition in the body of the
         --  subprogram as plain assertions.

         Why_Body := Sequence
           ((1 =>
                 Transform_All_Pragmas
               (Pre_Prags,
                "checking of pragma precondition"),
             2 => Why_Body,
             3 => Transform_All_Pragmas
               (Post_Prags,
                "checking of pragma postcondition")));

         Why_Body := Checking_Of_Refined_Post (Why_Body);

         --  Check type invariants on subprogram's ouput, absence of runtime
         --  errors in Post and RTE + validity of contract cases.

         Why_Body := Sequence
           ((1 => Why_Body,
             2 => Check_Invariants_Of_Outputs,
             3 => CC_And_RTE_Post,
             4 => Result_Var));

         --  add declarations for 'Old variables

         Why_Body := Declare_Old_Variables (Why_Body);

         Prog := Sequence (Prog, Why_Body);
      end if;

      Prog := Wrap_Decls_For_CC_Guards (Prog);

      Prog := Sequence
        ((Assume_For_Input,
          Assume_Init_Cond_Of_Withed_Units,
          Comp_Decl_At_Subp_Start,
          RTE_Of_Pre,
          Assume_Or_Assert_Of_Pre,
          Prog));

      --  Assume values of constants

      Assume_Value_Of_Constants (Prog, E, Contract_Params);

      declare
         Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Cur_Subp_Sloc);
      begin
         Label_Set.Include (NID ("W:diverges:N"));
         Emit (File,
               Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Prog,
                  Name    => Def_Name,
                  Binders => (1 => Unit_Param),
                  Labels  => Label_Set,
                  Post    => Post_As_Pred,
                  Def     => +Prog));
      end;

      --  cleanup

      Self_Name := Why_Empty;
      Self_Is_Mutable := False;

      if Ekind (E) = E_Function then
         Result_Name := Why_Empty;
      end if;

      --  We should *not* filter our own entity, it is needed for recursive
      --  calls.

      Close_Theory (File,
                    Kind => VC_Generation_Theory,
                    Defined_Entity => E);
   end Generate_VCs_For_Subprogram;

   ---------------------------
   -- Generate_VCs_For_Task --
   ---------------------------

   procedure Generate_VCs_For_Task
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Name   : constant String  := Full_Name (E);
      Body_N : constant Node_Id := Task_Body (E);
      Params : Transformation_Params;

      Why_Body   : W_Prog_Id := +Void;
      Post       : W_Pred_Id;
      Priv_Decls : constant List_Id := Private_Declarations_Of_Task_Type (E);
      Vis_Decls  : constant List_Id := Visible_Declarations_Of_Task_Type (E);

   begin
      --  We open a new theory, so that the context is fresh for this task

      Open_Theory (File,
                   New_Module
                     (Name => NID (Name & "__task_body"),
                      File => No_Name),
                   Comment =>
                     "Module for checking absence of run-time errors and "
                       & "non-termination of task body of the task type "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);
      Current_Subp := E;

      Register_VC_Entity (E);

      Params := (File        => File,
                 Phase       => Generate_VCs_For_Body,
                 Gen_Marker  => False,
                 Ref_Allowed => True);

      Post :=
        +New_VC_Expr (Ada_Node   => E,
                      Expr       => +False_Pred,
                      Reason     => VC_Task_Termination,
                      Domain     => EW_Pred);

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      --  Translate declarations and statements in the task body, if there
      --  is one.

      if Present (Body_N)
        and then Entity_Body_In_SPARK (E)
      then
         if Present (Handled_Statement_Sequence (Body_N)) then
            Why_Body :=
              Sequence
                (Transform_Statements_And_Declarations
                   (Statements (Handled_Statement_Sequence (Body_N))),
                 Why_Body);
         end if;

         Why_Body :=
           Transform_Declarations_Block (Declarations (Body_N), Why_Body);
      end if;

      --  We check any assertions and pragma (Interrupt)_Priority in the
      --  declarations of the task.

      --  Translate public and private declarations of the package

      if Present (Priv_Decls)
        and then Private_Spec_In_SPARK (E)
      then
         Why_Body := Transform_Declarations_Block (Priv_Decls, Why_Body);
      end if;

      if Present (Vis_Decls) then
         Why_Body := Transform_Declarations_Block (Vis_Decls, Why_Body);
      end if;

      --  We check that the call graph starting from this task respects the
      --  ceiling priority protocol.

      Why_Body :=
        Sequence
          (Check_Ceiling_Protocol (Params, E),
           Why_Body);

      --  We assume that objects used in the program are in range, if
      --  they are of a dynamic type.

      Why_Body :=
        Sequence
          (Compute_Dynamic_Property_For_Inputs (Params => Params,
                                                E      => E),
           Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Body, E, Params);

      declare
         Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Cur_Subp_Sloc);
      begin
         Label_Set.Include (NID ("W:diverges:N"));
         Emit (File,
                Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Prog,
                  Name    => Def_Name,
                  Binders => (1 => Unit_Param),
                  Labels  => Label_Set,
                  Post    => Post,
                  Def     => +Why_Body));
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      Close_Theory (File,
                    Kind => VC_Generation_Theory);

   end Generate_VCs_For_Task;

   -----------------------------
   -- Get_Location_For_Aspect --
   -----------------------------

   function Get_Location_For_Aspect
     (E         : Entity_Id;
      Kind      : Pragma_Id;
      Classwide : Boolean := False) return Node_Id is
   begin

      --  In the case of a No_Return Subprogram, there is no real location for
      --  the postcondition; simply return the subprogram entity node.

      if Kind = Pragma_Postcondition
        and then No_Return (E)
      then
         return E;
      end if;

      --  Pre- and postconditions are stored in reverse order in
      --  Pre_Post_Conditions, hence retrieve the last assertion in this
      --  list to get the first one in source code.

      declare
         L : constant Node_Lists.List :=
           Find_Contracts (E, Kind, Classwide => Classwide);
      begin
         if L.Is_Empty then
            return Empty;
         else
            return L.Last_Element;
         end if;
      end;
   end Get_Location_For_Aspect;

   -----------------------------
   -- Generate_Axiom_For_Post --
   -----------------------------

   procedure Generate_Axiom_For_Post
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Params             : Transformation_Params;
      Pre                : W_Pred_Id;
      Post               : W_Pred_Id;
      Dispatch_Pre       : W_Pred_Id := Why_Empty;
      Dispatch_Post      : W_Pred_Id := Why_Empty;
      Refined_Post       : W_Pred_Id := Why_Empty;
      Why_Type           : W_Type_Id := Why_Empty;

   begin
      --  Do not generate an axiom for:
      --    * recursive functions, as the axiom could be used to prove the
      --      function itself,
      --    * potentially non returning functions as the axiom could be
      --      unsound,
      --    * volatile functions and protected subprograms.

      if Ekind (E) in E_Procedure | Entry_Kind
        or else No_Return (E)
        or else Is_Recursive (E)
        or else Is_Potentially_Nonreturning (E)
        or else (Is_Volatile_Function (E) and not Is_Protected_Subprogram (E))
      then
         return;
      end if;

      Why_Type := Type_Of_Node (Etype (E));

      --  If the function has a postcondition, is not mutually recursive
      --  and is not annotated with No_Return, then generate an axiom:
      --  axiom def_axiom:
      --     forall args [f (args)]. pre (args) ->
      --           let result = f (args) in post (args)

      Params :=
        (File        => File,
         Phase       => Generate_Logic,
         Gen_Marker  => False,
         Ref_Allowed => False);

      --  We fill the map of parameters, so that in the Pre and Post, we use
      --  local names of the parameters, instead of the global names.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      for Binder of Logic_Func_Binders loop
         declare
            A : constant Node_Id :=
              (case Binder.Kind is
                  when Regular | Concurrent_Self => Binder.Main.Ada_Node,
                  when others  => raise Program_Error);
            --  in parameters should not be split
         begin
            pragma Assert (Present (A) or else Binder.Kind = Regular);

            if Present (A) then
               Ada_Ent_To_Why.Insert (Symbol_Table,
                                      Unique_Entity (A),
                                      Binder);
            elsif Binder.Main.B_Ent /= Null_Entity_Name then

               --  If there is no Ada_Node, this is a binder generated from
               --  an effect; we add the parameter in the name map using its
               --  unique name.

               Ada_Ent_To_Why.Insert
                 (Symbol_Table,
                  Binder.Main.B_Ent,
                  Binder);
            end if;
         end;
      end loop;

      Pre := +Compute_Spec (Params, E, Pragma_Precondition, EW_Pred);
      Post :=
        +New_And_Expr
        (Left   =>
           +Compute_Spec (Params, E, Pragma_Postcondition, EW_Pred),
         Right  => +Compute_Contract_Cases_Postcondition (Params, E),
         Domain => EW_Pred);

      if Is_Dispatching_Operation (E) then
         Dispatch_Pre :=
           Get_Dispatching_Call_Contract (Params, E, Pragma_Precondition);
         Dispatch_Post :=
           Get_Dispatching_Call_Contract (Params, E, Pragma_Postcondition);
      end if;

      if Has_Contracts (E, Pragma_Refined_Post) then
         Refined_Post := +Compute_Spec (Params,
                                        E, Pragma_Refined_Post, EW_Pred);
      end if;

      declare
         Logic_Why_Binders   : constant Binder_Array :=
           To_Binder_Array (Logic_Func_Binders);
         Logic_Id            : constant W_Identifier_Id :=
           To_Why_Id (E, Domain => EW_Term, Local => False);
         Dispatch_Logic_Id   : constant W_Identifier_Id :=
           To_Why_Id
             (E, Domain => EW_Term, Local => False, Selector => Dispatch);
         Refine_Logic_Id     : constant W_Identifier_Id :=
           To_Why_Id
             (E, Domain => EW_Term, Local => False, Selector => Refine);
         Guard               : constant W_Pred_Id :=
           +New_And_Then_Expr
           (Left   => +Compute_Guard_Formula (Logic_Func_Binders),
            Right  => +Compute_Type_Invariants_For_Subprogram
              (E, True, Params),
            Domain => EW_Pred);
         --  Dynamic invariant / type invariants of the inputs

         Dynamic_Prop_Result : constant W_Pred_Id :=
           +New_And_Then_Expr
           (Left   => +Compute_Dynamic_Invariant
              (Expr     => +New_Result_Ident (Why_Type),
               Ty       => Etype (E),
               Only_Var => False_Term),
            Right  => +Compute_Type_Invariants_For_Subprogram
              (E, False, Params),
            Domain => EW_Pred);
         --  Dynamic invariant / type invariants of the result

         procedure Emit_Post_Axiom
           (Suffix : String;
            Id     : W_Identifier_Id;
            Pre, Post : W_Pred_Id);
         --  Emit the post_axiom with the given axiom_suffix, id, pre and post

         ---------------------
         -- Emit_Post_Axiom --
         ---------------------

         procedure Emit_Post_Axiom
           (Suffix : String;
            Id     : W_Identifier_Id;
            Pre, Post : W_Pred_Id) is
            Complete_Post : constant W_Pred_Id :=
              +New_And_Expr
              (Left   => +Post,
               Right  => +Dynamic_Prop_Result,
               Domain => EW_Pred);
         begin
            if not Is_True_Boolean (+Complete_Post) then
               Emit
                 (File,
                  New_Guarded_Axiom
                    (Ada_Node => Empty,
                     Name     => NID (Short_Name (E) & "__" & Suffix),
                     Binders  => Logic_Why_Binders,
                     Triggers =>
                       New_Triggers
                         (Triggers =>
                              (1 => New_Trigger
                                 (Terms =>
                                    (1 => New_Call
                                         (Domain  => EW_Term,
                                          Name    => Id,
                                          Binders => Logic_Why_Binders))))),
                     Pre      =>
                       +New_And_Expr (Left   => +Guard,
                                      Right  => +Pre,
                                      Domain => EW_Pred),
                     Def      =>
                       +New_Typed_Binding
                       (Ada_Node => Empty,
                        Domain   => EW_Pred,
                        Name     => +New_Result_Ident (Why_Type),
                        Def      => New_Call
                          (Domain  => EW_Term,
                           Name    => Id,
                           Binders => Logic_Why_Binders),
                        Context  => +Complete_Post)));
            end if;
         end Emit_Post_Axiom;

      --  Start of processing for Generate_Axiom_For_Post

      begin
         --  Do not emit an axiom for E if it is inlined for proof

         if No (Retrieve_Inline_Annotation (E)) then
            Emit_Post_Axiom (Post_Axiom, Logic_Id, Pre, Post);
         end if;

         --  ??? clean up this code duplication for dispatch and refine

         if Is_Dispatching_Operation (E) then
            pragma Assert (Present (Dispatch_Pre)
                            and then Present (Dispatch_Post));
            Emit_Post_Axiom (Post_Dispatch_Axiom,
                             Dispatch_Logic_Id,
                             Dispatch_Pre,
                             Dispatch_Post);
         end if;

         if Has_Contracts (E, Pragma_Refined_Post) then
            pragma Assert (Present (Refined_Post));
            Emit_Post_Axiom (Post_Refine_Axiom,
                             Refine_Logic_Id,
                             Pre,
                             Refined_Post);
         end if;
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
   end Generate_Axiom_For_Post;

   ------------------------------------
   -- Generate_Subprogram_Completion --
   ------------------------------------

   procedure Generate_Subprogram_Completion
     (File : W_Section_Id;
      E    : Entity_Id) is
   begin
      Open_Theory (File, E_Axiom_Module (E),
                   Comment =>
                     "Module for declaring a program function (and possibly "
                       & "an axiom) for "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Add_Dependencies_For_Effects (File, E);

      declare
         Use_Result_Name : constant Boolean := Ekind (E) = E_Function;
         --  Store the result identifier in Result_Name
      begin
         if Use_Result_Name then
            Result_Name := New_Result_Ident (Type_Of_Node (Etype (E)));
         end if;

         Generate_Subprogram_Program_Fun (File, E);

         Generate_Axiom_For_Post (File, E);

         if Use_Result_Name then
            Result_Name := Why_Empty;
         end if;
      end;

      Close_Theory (File,
                    Kind => Axiom_Theory,
                    Defined_Entity => E);
   end Generate_Subprogram_Completion;

   --------------------------------------
   -- Generate_Subprogram_Program_Fun --
   --------------------------------------

   procedure Generate_Subprogram_Program_Fun
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Func_Binders       : constant Item_Array := Compute_Binders (E, EW_Prog);
      Func_Why_Binders   : constant Binder_Array :=
        To_Binder_Array (Func_Binders);
      Params             : Transformation_Params;
      Effects            : W_Effects_Id;
      Pre                : W_Pred_Id;
      Post               : W_Pred_Id;
      Dispatch_Pre       : W_Pred_Id;
      Dispatch_Post      : W_Pred_Id;
      Refined_Post       : W_Pred_Id;
      Prog_Id            : constant W_Identifier_Id :=
        To_Why_Id (E, Domain => EW_Prog, Local => True);
      Why_Type           : W_Type_Id := Why_Empty;

   begin
      Params :=
        (File        => File,
         Phase       => Generate_Logic,
         Gen_Marker  => False,
         Ref_Allowed => True);

      --  We fill the map of parameters, so that in the Pre and Post, we use
      --  local names of the parameters, instead of the global names.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      for Binder of Func_Binders loop
         declare
            A : constant Node_Id := Get_Ada_Node_From_Item (Binder);
         begin

            --  If the Ada_Node is Empty, it's not an interesting binder (e.g.
            --  void_param).

            if Present (A) and then not Is_Type (E) then
               Ada_Ent_To_Why.Insert (Symbol_Table, A, Binder);
            end if;
         end;
      end loop;

      Effects := Compute_Effects (E);

      Pre := Get_Static_Call_Contract (Params, E, Pragma_Precondition);

      if Is_Dispatching_Operation (E) then
         Dispatch_Pre :=
           Get_Dispatching_Call_Contract (Params, E, Pragma_Precondition);
      end if;

      --  For a subprogram marked with No_Return, the postcondition at call
      --  site should be "False", so that it is known in the caller that the
      --  call does not return.

      if No_Return (E) then
         Post := False_Pred;

         if Is_Dispatching_Operation (E) then
            Dispatch_Post := False_Pred;
         end if;

         if Has_Contracts (E, Pragma_Refined_Post) then
            Refined_Post := False_Pred;
         end if;

      --  In other cases, the postcondition is extracted from the subprogram
      --  contract.

      else
         Post :=
           +New_And_Expr
           (Left   =>
              +Get_Static_Call_Contract (Params, E, Pragma_Postcondition),
            Right  => +Compute_Contract_Cases_Postcondition (Params, E),
            Domain => EW_Pred);

         if Is_Dispatching_Operation (E) then
            Dispatch_Post :=
              Get_Dispatching_Call_Contract (Params, E, Pragma_Postcondition);
         end if;

         if Has_Contracts (E, Pragma_Refined_Post) then
            Refined_Post :=
              Get_Static_Call_Contract (Params, E, Pragma_Refined_Post);
         end if;
      end if;

      if Ekind (E) = E_Function then

         Why_Type := Type_Of_Node (Etype (E));

         declare
            Logic_Why_Binders   : constant Binder_Array :=
              To_Binder_Array (Logic_Func_Binders);
            Logic_Func_Args     : constant W_Expr_Array :=
              Compute_Args (E, Logic_Why_Binders);
            Logic_Id            : constant W_Identifier_Id :=
              To_Why_Id (E, Domain => EW_Term, Local => False);
            Dispatch_Logic_Id   : constant W_Identifier_Id :=
              To_Why_Id
                (E, Domain => EW_Term, Local => False, Selector => Dispatch);
            Refine_Logic_Id     : constant W_Identifier_Id :=
              To_Why_Id
                (E, Domain => EW_Term, Local => False, Selector => Refine);
            Dynamic_Prop_Result : constant W_Pred_Id :=
              +New_And_Then_Expr
              (Left   => +Compute_Dynamic_Invariant
                 (Expr     => +New_Result_Ident (Why_Type),
                  Ty       => Etype (E),
                  Only_Var => False_Term),
               Right  => +Compute_Type_Invariants_For_Subprogram
                 (E, False, Params),
               Domain => EW_Pred);
            --  Dynamic invariant and type invariant of the result

            Expr_Fun_N          : constant Node_Id :=
              Get_Expression_Function (E);

            Volatile_State  : constant W_Identifier_Id :=
              New_Identifier
                (Domain => EW_Term,
                 Name   => "volatile__effect");

            function Create_Function_Decl
              (Logic_Id : W_Identifier_Id;
               Prog_Id  : W_Identifier_Id;
               Pre      : W_Pred_Id;
               Post     : W_Pred_Id) return W_Declaration_Id;
            --  create the function declaration with the given Logic_Id,
            --  Prog_Id, Pre and Post.

            --------------------------
            -- Create_Function_Decl --
            --------------------------

            function Create_Function_Decl
              (Logic_Id : W_Identifier_Id;
               Prog_Id  : W_Identifier_Id;
               Pre      : W_Pred_Id;
               Post     : W_Pred_Id) return W_Declaration_Id
            is
               --  Each function has in its postcondition that its result is
               --  equal to the application of the corresponding logic function
               --  to the same arguments.

               Param_Post : W_Pred_Id :=
                 +New_And_Expr
                 (Left   => +Dynamic_Prop_Result,
                  Right  => +Post,
                  Domain => EW_Pred);

               Effects : constant W_Effects_Id := New_Effects;

            begin

               --  A volatile function has an effect, and should not have the
               --  special postcondition which says it's result is equal to the
               --  logic function.

               --  For a volatile function that is not protected, we need to
               --  generate a dummy effect. Protected functions are OK, they
               --  already have their own state (the protected object).

               if Is_Volatile_Function (E)
                 and then not Is_Protected_Subprogram (E)
               then
                  Effects_Append_To_Writes (Effects, Volatile_State);
               else
                  Param_Post :=
                    +New_And_Expr
                    (Domain => EW_Pred,
                     Left   =>
                       New_Call
                         (Name   => Why_Eq,
                          Domain => EW_Pred,
                          Typ    => EW_Bool_Type,
                          Args   => (+New_Result_Ident (Why_Type),
                                     New_Call
                                       (Domain => EW_Term,
                                        Name   => Logic_Id,
                                        Args   => Logic_Func_Args))),
                     Right  => +Param_Post);
               end if;
               return New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Id,
                  Binders     => Func_Why_Binders,
                  Return_Type => Type_Of_Node (Etype (E)),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => Param_Post);
            end Create_Function_Decl;

         begin
            --  If E is an expression function, add its body to its
            --  postcondition.

            if Present (Expr_Fun_N)
              and then Entity_Body_In_SPARK (E)
              and then not No_Return (E)
              and then
                (not Is_Volatile_Function (E)
                 or else Is_Protected_Subprogram (E))
            then
               declare
                  Use_Base  : constant Boolean :=
                    not Is_Standard_Boolean_Type (Etype (E))
                    and then Has_Scalar_Type (Etype (E))
                    and then Use_Base_Type_For_Type (Etype (E));
                  Eq_Ty     : constant W_Type_Id :=
                    (if Use_Base then Base_Why_Type (Etype (E))
                     else Why_Type);
                  Domain    : constant EW_Domain :=
                    (if Is_Standard_Boolean_Type (Etype (E)) then EW_Pred
                     else EW_Term);
                  Expr_Body : constant W_Expr_Id :=
                    Transform_Expr (Expression (Expr_Fun_N),
                                    Expected_Type => Eq_Ty,
                                    Domain        => Domain,
                                    Params        => Params);
                  Res_Expr  : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain         => EW_Term,
                       Expr           => +New_Result_Ident (Why_Type),
                       To             => Eq_Ty,
                       Force_No_Slide => True);
                  Eq_Expr   : constant W_Pred_Id :=
                    (if Is_Standard_Boolean_Type (Etype (E))
                     then New_Equal_Bool (+Res_Expr, +Expr_Body)
                     else New_Call (Name => Why_Eq,
                                    Args => (Res_Expr, Expr_Body),
                                    Typ  => EW_Bool_Type));
               begin
                  if Has_Contracts (E, Pragma_Refined_Post) then
                     Refined_Post :=
                       +New_And_Expr (+Eq_Expr, +Refined_Post, EW_Pred);
                  else
                     Post := +New_And_Expr (+Eq_Expr, +Post, EW_Pred);
                  end if;
               end;
            end if;

            if Is_Volatile_Function (E)
              and then not Is_Protected_Subprogram (E)
            then
               Emit
                 (File,
                  New_Global_Ref_Declaration
                    (Ada_Node => E,
                     Labels   => Name_Id_Sets.Empty_Set,
                     Name     => Volatile_State,
                     Ref_Type => EW_Private_Type));
            end if;

            Emit
              (File,
               Create_Function_Decl (Logic_Id => Logic_Id,
                                     Prog_Id  => Prog_Id,
                                     Pre      => Pre,
                                     Post     => Post));

            if Is_Dispatching_Operation (E) then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Dispatch_Module)),
                     Declarations =>
                       (1 => Create_Function_Decl
                            (Logic_Id => Dispatch_Logic_Id,
                             Prog_Id  => Prog_Id,
                             Pre      => Dispatch_Pre,
                             Post     => Dispatch_Post))));
            end if;

            if Has_Contracts (E, Pragma_Refined_Post) then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => Create_Function_Decl
                            (Logic_Id => Refine_Logic_Id,
                             Prog_Id  => Prog_Id,
                             Pre      => Pre,
                             Post     => Refined_Post))));
            end if;
         end;

      else
         pragma Assert (Ekind (E) in E_Entry | E_Procedure);

         declare
            Dynamic_Prop_Effects : constant W_Pred_Id :=
              +New_And_Then_Expr
              (Left   => +Compute_Dynamic_Property_For_Effects (E, Params),
               Right  =>
                 +Compute_Type_Invariants_For_Subprogram (E, False, Params),
               Domain => EW_Pred);
            --  Dynamic invariant and type invariant for outputs of the
            --  procedure.

         begin
            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Id,
                  Binders     => Func_Why_Binders,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Unit_Type,
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => +New_And_Expr
                    (Left   => +Post,
                     Right  => +Dynamic_Prop_Effects,
                     Domain => EW_Pred)));

            if Is_Dispatching_Operation (E) then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Dispatch_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => EW_Unit_Type,
                             Effects     => Effects,
                             Pre         => Dispatch_Pre,
                             Post        => +New_And_Expr
                               (Left   => +Dispatch_Post,
                                Right  => +Dynamic_Prop_Effects,
                                Domain => EW_Pred)))));
            end if;

            --  For error-signaling procedures, define a variant of the
            --  program function with a precondition of False inside the
            --  namespace No_Return. This variant is used when calling the
            --  error-signaling procedure outside another error-signaling
            --  procedure. This ensures that a check is issued for each
            --  such call, to detect when they are reachable.

            if Is_Error_Signaling_Procedure (E) then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_No_Return_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => EW_Unit_Type,
                             Effects     => Effects,
                             Pre         => False_Pred,
                             Post        => False_Pred))));
            end if;

            if Has_Contracts (E, Pragma_Refined_Post) then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => EW_Unit_Type,
                             Effects     => Effects,
                             Pre         => Pre,
                             Post        => +New_And_Expr
                               (Left   => +Refined_Post,
                                Right  => +Dynamic_Prop_Effects,
                                Domain => EW_Pred)))));
            end if;
         end;
      end if;

      --  Generate a check_invariants_on_call program function with the
      --  same parameters as E but with the invariant for E's inputs as a
      --  precondition.

      declare
         Inv_Checks : constant W_Pred_Id :=
           Compute_Type_Invariants_For_Subprogram (E, True, Params);
      begin
         if not Is_True_Boolean (+Inv_Checks) then
            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        =>
                    To_Local (E_Symb (E, WNE_Check_Invariants_On_Call)),
                  Binders     => Func_Why_Binders,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Unit_Type,
                  Pre         => Inv_Checks,
                  Post        => Inv_Checks));
         end if;
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
   end Generate_Subprogram_Program_Fun;

   -------------------
   -- Get_Logic_Arg --
   -------------------

   function Get_Logic_Arg
     (Binder      : Binder_Type;
      Ref_Allowed : Boolean) return W_Expr_Id
   is
      Id : W_Identifier_Id;
      T  : W_Expr_Id;
      C : constant Ada_Ent_To_Why.Cursor :=
        (if Present (Binder.Ada_Node) then
              Ada_Ent_To_Why.Find (Symbol_Table, Binder.Ada_Node)
         else Ada_Ent_To_Why.Find (Symbol_Table, Binder.B_Ent));
      E : Item_Type;
   begin
      pragma Assert (if Present (Binder.Ada_Node) then
                        Ada_Ent_To_Why.Has_Element (C));

      if Ada_Ent_To_Why.Has_Element (C) then

         E := Ada_Ent_To_Why.Element (C);
         T := Reconstruct_Item (E, Ref_Allowed);

         --  If the global is associated to an entity and it is in
         --  split form, then we need to reconstruct it.

         T :=
           Insert_Simple_Conversion
             (Domain   => EW_Term,
              Expr     => T,
              To       => Get_Typ (Binder.B_Name));
      else
         Id := To_Why_Id (To_String (Binder.B_Ent), Local => False);

         if Ref_Allowed then
            T := New_Deref (Right => Id,
                            Typ   => Get_Typ (Id));
         else
            T := +Id;
         end if;
      end if;

      return T;
   end Get_Logic_Arg;

   ----------------------------------------
   -- Translate_Expression_Function_Body --
   ----------------------------------------

   procedure Translate_Expression_Function_Body
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Expr_Fun_N         : constant Node_Id := Get_Expression_Function (E);
      pragma Assert (Present (Expr_Fun_N));
      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Flat_Binders       : constant Binder_Array :=
        To_Binder_Array (Logic_Func_Binders);
      Logic_Id           : constant W_Identifier_Id :=
        To_Why_Id (E, Domain => EW_Term, Local => False,
                   Selector => (if Has_Contracts (E, Pragma_Refined_Post)
                                then Refine
                                else Why.Inter.Standard));

      Params : Transformation_Params;
   begin

      Open_Theory (File, E_Axiom_Module (E),
                   Comment =>
                     "Module giving a program function and a defining axiom "
                       & "for the expression function "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Add_Dependencies_For_Effects (File, E);

      --  Store an appropriate value for the result identifier in Result_Name.

      Result_Name := New_Result_Ident (Type_Of_Node (Etype (E)));

      Generate_Subprogram_Program_Fun (File, E);

      Generate_Axiom_For_Post (File, E);

      --  If the entity's body is not in SPARK,
      --  or if the function does not return, do not generate axiom.

      if not Entity_Body_Compatible_With_SPARK (E)
        or else No_Return (E)
        or else
          (Is_Volatile_Function (E) and then not Is_Protected_Subprogram (E))
      then
         Close_Theory (File,
                       Kind => Definition_Theory);
         Result_Name := Why_Empty;
         return;
      end if;

      Params :=
        (File        => File,
         Phase       => Generate_Logic,
         Gen_Marker   => False,
         Ref_Allowed => False);

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      for Binder of Logic_Func_Binders loop
         declare
            A : constant Node_Id :=
              (case Binder.Kind is
                  when Regular | Concurrent_Self => Binder.Main.Ada_Node,
                  when others              => raise Program_Error);
         begin
            pragma Assert (Present (A) or else Binder.Kind = Regular);

            if Present (A) then
               Ada_Ent_To_Why.Insert (Symbol_Table,
                                      Unique_Entity (A),
                                      Binder);
            elsif Binder.Main.B_Ent /= Null_Entity_Name then

               --  if there is no Ada_Node, this in a binder generated from
               --  an effect; we add the parameter in the name map using its
               --  unique name

               Ada_Ent_To_Why.Insert
                 (Symbol_Table,
                  Binder.Main.B_Ent,
                  Binder);
            end if;
         end;
      end loop;

      --  Given an expression function F with expression E, define an axiom
      --  that states that: "for all <args> => F(<args>) = E".
      --  There is no need to use the precondition here, as the above axiom
      --  is always sound.

      if Is_Standard_Boolean_Type (Etype (E)) then
         Emit
           (File,
            New_Defining_Bool_Axiom
              (Ada_Node => E,
               Name     => Logic_Id,
               Binders  => Flat_Binders,
               Def      => +Transform_Expr (Expression (Expr_Fun_N),
                                            EW_Pred,
                                            Params)));

      else
         --  For scalar types which are not modeled as their representation
         --  type in Why, using instead this representation type
         --  facilitate the job of automatic provers. As it is potentially
         --  incorrect if there can be a runtime error in the expression
         --  function body, it should not be done if the function may be
         --  recursive.
         --  For example for:

         --    function F return Natural is (Largest_Int + 1);

         --  we should *not* generate the incorrect axiom:

         --    axiom f__def:
         --      forall x:natural. to_int(f x) = to_int(largest_int) + 1

         --  but the correct one:

         --    axiom f__def:
         --      forall x:natural. f x = of_int (to_int(largest_int) + 1)

         if Is_Recursive (E)
           or else Is_Potentially_Nonreturning (E)
           or else not Has_Scalar_Type (Etype (E))
           or else Use_Split_Form_For_Type (Etype (E))
         then
            declare
               Ty_Ent  : constant Entity_Id := Etype (E);
               Equ_Ty  : constant W_Type_Id := Type_Of_Node (Ty_Ent);
               Guard   : constant W_Pred_Id :=
                 Compute_Guard_Formula (Logic_Func_Binders);
            begin
               Emit
                 (File,
                  New_Defining_Axiom
                    (Ada_Node    => E,
                     Name        => Logic_Id,
                     Binders     => Flat_Binders,
                     Pre         => Guard,
                     Def         =>
                       +Transform_Expr
                         (Expression (Expr_Fun_N),
                          Expected_Type => Equ_Ty,
                          Domain        => EW_Term,
                          Params        => Params)));
            end;
         else
            declare
               --  Here we should use the precondition as the axiom could only
               --  be sound in its context.

               Ty_Ent  : constant Entity_Id := Etype (E);
               Equ_Ty  : constant W_Type_Id := Base_Why_Type (Ty_Ent);
               Guard   : constant W_Pred_Id :=
                 Compute_Guard_Formula (Logic_Func_Binders);
               Pre     : constant W_Pred_Id :=
                 +Compute_Spec (Params, E, Pragma_Precondition, EW_Pred);
            begin
               Emit
                 (File,
                  New_Guarded_Axiom
                    (Ada_Node => Empty,
                     Name     => NID (Short_Name (E) & "__" & Def_Axiom),
                     Binders  => Flat_Binders,
                     Triggers =>
                       New_Triggers
                         (Triggers =>
                            (1 => New_Trigger
                               (Terms =>
                                  (1 => New_Call
                                     (Domain  => EW_Term,
                                      Name    => Logic_Id,
                                      Binders => Flat_Binders))))),
                     Pre      =>
                       +New_And_Expr (Left   => +Guard,
                                      Right  => +Pre,
                                      Domain => EW_Pred),
                     Def      =>
                       New_Call
                         (Name => Why_Eq,
                          Args => (Insert_Simple_Conversion
                                     (Domain         => EW_Term,
                                      Expr           => +New_Call
                                        (Name    => Logic_Id,
                                         Domain  => EW_Term,
                                         Binders => Flat_Binders,
                                         Typ     => Type_Of_Node (Ty_Ent)),
                                      To             => Equ_Ty),
                                   +Transform_Expr
                                     (Expression (Expr_Fun_N),
                                      Expected_Type => Equ_Ty,
                                      Domain        => EW_Term,
                                      Params        => Params)),
                          Typ  => EW_Bool_Type)));
            end;
         end if;
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      Result_Name := Why_Empty;

      --  No filtering is necessary here, as the theory should on the contrary
      --  use the previously defined theory for the function declaration. Pass
      --  in the defined entity E so that the graph of dependencies between
      --  expression functions can be built.
      --  Attach the newly created theory as a completion of the existing one.

      Close_Theory (File,
                    Kind => Axiom_Theory,
                    Defined_Entity => E);
   end Translate_Expression_Function_Body;

   -------------------------------
   -- Translate_Subprogram_Spec --
   -------------------------------

   procedure Translate_Subprogram_Spec
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Why_Type           : W_Type_Id;
   begin
      Open_Theory (File, E_Module (E),
                   Comment =>
                     "Module for possibly declaring "
                       & "a logic function for "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  No logic function is created for volatile functions The function's
      --  effects are model by an effect on the program function.

      if Ekind (E) = E_Function
        and then (if Is_Volatile_Function (E) then Is_Protected_Subprogram (E))
      then
         Why_Type := Type_Of_Node (Etype (E));

         declare
            Logic_Why_Binders : constant Binder_Array :=
              To_Binder_Array (Logic_Func_Binders);
            Logic_Id          : constant W_Identifier_Id :=
              To_Why_Id (E, Domain => EW_Term, Local => True);
            Def               : constant W_Expr_Id :=
              Compute_Inlined_Expr (E, Logic_Func_Binders, Why_Type, File);
         begin
            --  Generate a logic function

            Add_Dependencies_For_Effects (File, E);

            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => Logic_Id,
                  Binders     => Logic_Why_Binders,
                  Labels      =>
                    (if Def = Why_Empty then Name_Id_Sets.Empty_Set
                     else Name_Id_Sets.To_Set (NID ("inline"))),
                  Def         => Def,
                  Return_Type => Why_Type));

            if Is_Dispatching_Operation (E) then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Dispatch_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Term,
                             Name        => Logic_Id,
                             Binders     => Logic_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => Why_Type))));
            end if;

            if Has_Contracts (E, Pragma_Refined_Post) then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Term,
                             Name        => Logic_Id,
                             Binders     => Logic_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => Why_Type))));
            end if;
         end;

         Ada_Ent_To_Why.Insert (Symbol_Table, E, Mk_Item_Of_Entity (E));
      elsif Ekind (E) = E_Function then
         Ada_Ent_To_Why.Insert (Symbol_Table, E, Mk_Item_Of_Entity (E));
      else
         Insert_Entity (E, To_Why_Id (E, Typ => Why_Empty));
      end if;

      Close_Theory (File,
                    Kind => Definition_Theory,
                    Defined_Entity => E);
   end Translate_Subprogram_Spec;

   -------------------------------------------------
   -- Update_Symbol_Table_For_Inherited_Contracts --
   -------------------------------------------------

   procedure Update_Symbol_Table_For_Inherited_Contracts (E : Entity_Id) is

      procedure Relocate_Symbols (Overridden : Entity_Id);
      --  Relocate parameters and result from Overridden subprogram to E

      ----------------------
      -- Relocate_Symbols --
      ----------------------

      procedure Relocate_Symbols (Overridden : Entity_Id) is
         From_Params : constant List_Id :=
           Parameter_Specifications (Subprogram_Specification (Overridden));
         To_Params   : constant List_Id :=
           Parameter_Specifications (Subprogram_Specification (E));
         From_Param  : Node_Id;
         To_Param    : Node_Id;

      begin
         From_Param := First (From_Params);
         To_Param := First (To_Params);
         while Present (From_Param) loop
            declare
               From_Id : constant Entity_Id :=
                 Defining_Identifier (From_Param);
               To_Id   : constant Entity_Id :=
                 Defining_Identifier (To_Param);
            begin
               Ada_Ent_To_Why.Insert
                 (Symbol_Table,
                  From_Id,
                  Ada_Ent_To_Why.Element (Symbol_Table, To_Id));
            end;

            Next (From_Param);
            Next (To_Param);
         end loop;

         pragma Assert (No (To_Param));
      end Relocate_Symbols;

      Inherit_Subp  : constant Subprogram_List := Inherited_Subprograms (E);
      Subp_For_Pre  : Entity_Id := Empty;
      Subp_For_Post : Entity_Id := Empty;
      Contracts     : Node_Lists.List;

   begin
      --  Find the subprogram from which the precondition is inherited, if any

      for J in Inherit_Subp'Range loop
         Contracts := Find_Contracts
           (Inherit_Subp (J), Pragma_Precondition, Classwide => True);

         if not Contracts.Is_Empty then
            Subp_For_Pre := Inherit_Subp (J);
            exit;
         end if;
      end loop;

      --  Find the subprogram from which the postcondition is inherited, if any

      for J in Inherit_Subp'Range loop
         Contracts := Find_Contracts
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

end Gnat2Why.Subprograms;
