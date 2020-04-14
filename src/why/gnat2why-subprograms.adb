------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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
with Atree;
with Common_Containers;              use Common_Containers;
with Debug;
with Errout;                         use Errout;
with Flow_Dependency_Maps;           use Flow_Dependency_Maps;
with Flow_Generated_Globals;         use Flow_Generated_Globals;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Refinement;                use Flow_Refinement;
with Flow_Types;                     use Flow_Types;
with Flow_Utility;                   use Flow_Utility;
with GNAT.Source_Info;
with GNATCOLL.Symbols;               use GNATCOLL.Symbols;
with Gnat2Why.Error_Messages;        use Gnat2Why.Error_Messages;
with Gnat2Why.Expr;                  use Gnat2Why.Expr;
with Gnat2Why.Tables;                use Gnat2Why.Tables;
with Gnat2Why_Args;
with Namet;                          use Namet;
with Nlists;                         use Nlists;
with Opt;                            use type Opt.Warning_Mode_Type;
with Rtsfind;                        use Rtsfind;
with Sinput;                         use Sinput;
with Snames;                         use Snames;
with SPARK_Annotate;                 use SPARK_Annotate;
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
with Why.Conversions;                use Why.Conversions;
with Why.Gen.Decl;                   use Why.Gen.Decl;
with Why.Gen.Expr;                   use Why.Gen.Expr;
with Why.Gen.Names;                  use Why.Gen.Names;
with Why.Gen.Pointers;               use Why.Gen.Pointers;
with Why.Gen.Preds;                  use Why.Gen.Preds;
with Why.Gen.Progs;                  use Why.Gen.Progs;
with Why.Gen.Records;                use Why.Gen.Records;
with Why.Gen.Terms;                  use Why.Gen.Terms;
with Why.Inter;                      use Why.Inter;
with Why.Types;                      use Why.Types;

package body Gnat2Why.Subprograms is

   Subprogram_Exceptions : Why_Node_Sets.Set;
   --  Set of exception declarations

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Compute_Args
     (E       : Entity_Id;
      Binders : Binder_Array) return W_Expr_Array;
   --  Given a function entity, and an array of program binders,
   --  compute a call of the logical Why function corresponding to E.
   --  In general, the resulting expression array has *more* arguments than the
   --  Ada entity, because of effects. Note that these effect variables are not
   --  bound here, they refer to the global variables

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
     Pre  => Is_Subprogram_Or_Entry (E),
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
     Pre => Ekind (E) = E_Package;
   --  @param E Entity of a package.
   --  @param Params the transformation parameters
   --  @result a predicate including the type invariants that should be checked
   --          after E's elaboration.

   function Compute_Effects
     (E             : Entity_Id;
      Global_Params : Boolean := False) return W_Effects_Id;
   --  Compute the effects of the generated Why function. If Global_Params is
   --  True, then the global version of the parameters is used.

   function Compute_Call_Effects
     (Params : Transformation_Params;
      E      : Entity_Id)
      return W_Prog_Id;
   --  Generate a Why3 program simulating the effects of a call of the
   --  subprogram.

   function Compute_Binders (E : Entity_Id; Domain : EW_Domain)
                             return Item_Array;
   --  Return Why binders for the parameters of subprogram E.
   --  If Domain is EW_Term also generates binders for E's read effects.
   --  The array is a singleton of unit type if the array is empty.

   function Compute_Binders_For_Effects
     (E       : Entity_Id;
      Compute : Boolean) return Item_Array
   with Pre => Ekind (E) in Subprogram_Kind | E_Entry;
   --  @param E an enity for a subprogram
   --  @param Compute True if binders should be created when not in the
   --    symbol table.
   --  @result an array containing an Item per global variable read / written
   --          by E.

   function Add_Logic_Binders (E           : Entity_Id;
                               Raw_Binders : Item_Array) return Item_Array;
   --  Return Why binders for the parameters and read effects of function E.
   --  The array is a singleton of unit type if E has no parameters and no
   --  effects.

   function Assume_Initial_Condition_Of_Withed_Units
     (Main   : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id
   with Pre => Ekind (Main) in Subprogram_Kind | E_Package | E_Package_Body
     and then Is_Compilation_Unit (Main);
   --  Assume the Initial_Condition of every unit withed by a compilation unit.
   --  @param Main entity for a compilation unit
   --  @param Params the transformation parameters
   --  @result a sequence of assumptions, one for each withed unit which has an
   --          Initial_Condition.

   function Compute_Raw_Binders (E : Entity_Id) return Item_Array;
   --  Return Why binders for the parameters of subprogram E. The array is
   --  empty if E has no parameters.

   function Compute_Guard_Formula
     (Binders : Item_Array;
      Params  : Transformation_Params) return W_Pred_Id;
   --  For every object in the binder array, build a predicate for the dynamic
   --  invariant of the object and join everything together with a conjunction.

   procedure Clear_Exceptions;
   --  Initialization procedure to call before start of subprogram/package
   --  handling.

   procedure Declare_Exceptions (File : W_Section_Id);
   --  Declare exceptions needed for translation of the current unit. Those
   --  are introduced when translating loop exit statements and goto
   --  statements.

   function Get_Location_For_Aspect
     (E         : Entity_Id;
      Kind      : Pragma_Id;
      Classwide : Boolean := False) return Node_Id
   with Pre => Kind in Pragma_Precondition
                     | Pragma_Postcondition
                     | Pragma_Refined_Post
                     | Pragma_Contract_Cases;
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
      Params             : Transformation_Params) return W_Expr_Id;
   --  @param Function_Entity entity of a function
   --  @param Logic_Func_Binders binders for Function_Entity's declaration if
   --     local names should be used for these binders
   --  @param W_Return_Type Why3 type for Function_Entity's return type
   --  @param Params parameters for the translation
   --  @return if Function_Entity is non recursive and has a pragma Annotate
   --          (GNATprove, Inline_For_Proof), return the Why3 expression for
   --          its value. Otherwise return Why_Empty.

   function Number_Of_Func_Args (E : Entity_Id) return Natural is
     (Natural
        (List_Length
              (Parameter_Specifications (Subprogram_Specification (E))))
       + (if Within_Protected_Type (E) then 1 else 0));

   function Include_Non_Local_Type_Inv_For_Subp
     (E : Entity_Id) return W_Term_Id
   is
     (if not Is_Globally_Visible (E)
      and then not Is_Declared_In_Main_Lib_Unit (E)
      then False_Term
      else True_Term);
   --  If E is a private subprogram, type invariants of its enclosing units may
   --  be broken for its parameters and result. Ignore type invariants for
   --  private subprograms declared in other library units (for those declared
   --  in the current unit, it is OK, as local subprograms are already not part
   --  of the dynamic invariant).

   function Tag_Binder return Binder_Type is
      (Binder_Type'(Ada_Node => Empty,
                    B_Name   =>
                       New_Identifier
                      (Name   => To_String (WNE_Attr_Tag),
                       Typ    => EW_Int_Type),
                    B_Ent    => Null_Entity_Name,
                    Mutable  => False,
                    Labels   => <>));
   --  Binder to be used as additional tag argument for dispatching functions

   function Procedure_Logic_Binders (E : Entity_Id) return Binder_Array;
   --  Return binders that should be used for specific_post of a procedure E

   procedure Generate_Dispatch_Compatibility_Axioms
     (File : W_Section_Id;
      E    : Entity_Id)
   with Pre => Is_Visible_Dispatching_Operation (E);
   --  @param E a dispatching subprogram
   --  Emit compatibility axioms between the dispatching version of E and each
   --  visible overriding / inherited versions of E.

   ----------------------------------------------
   -- Assume_Initial_Condition_Of_Withed_Units --
   ----------------------------------------------

   function Assume_Initial_Condition_Of_Withed_Units
     (Main   : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id
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
      --  to precede the elaboration of E.

      Context_Item := First (Context_Items (CU));
      while Present (Context_Item) loop
         if Nkind (Context_Item) = N_With_Clause
           and then not Limited_Present (Context_Item)
         then
            Withed_Unit := Unit (Library_Unit (Context_Item));
            Withed := (if Present (Withed_Unit) then
                         Unique_Defining_Entity (Withed_Unit)
                       else Empty);

            if Nkind (Withed_Unit) = N_Package_Declaration
              and then Known_To_Precede (Withed => Withed, Main => Main)
            then
               declare
                  Init_Cond : constant Node_Id :=
                    Get_Pragma (Withed, Pragma_Initial_Condition);
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
         end if;

         Next (Context_Item);
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
            elsif Is_Protected_Operation (E) then Enclosing_Type (E)
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
                            (Get_Rep_Item (E, Name_Interrupt_Priority))
                        then RE_Interrupt_Priority
                        else RE_Priority),
                 Attr   => Attribute_Last,
                 Params => Params);

         elsif Ekind (E) in Subprogram_Kind and then Might_Be_Main (E) then
            --  Return expression used that defined System.Default_Priority
            return
              Transform_Expr
                (Expr   =>
                   Expression
                     (Enclosing_Declaration (RTE (RE_Default_Priority))),
                 Domain => EW_Term,
                 Params => Params);

         else
            pragma Assert (Is_Protected_Operation (E));
            declare
               PT : constant Entity_Id := Enclosing_Type (E);

               Type_Id : RE_Id;
               Attr_Id : Supported_Attribute_Id;
               --  Type and attribute for priority expression
            begin
               if Present (Get_Rep_Item (PT, Name_Interrupt_Priority))
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
        and then not Is_Protected_Operation (E)
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

   ----------------------
   -- Clear_Exceptions --
   ----------------------

   procedure Clear_Exceptions is
   begin
      Subprogram_Exceptions.Clear;
   end Clear_Exceptions;

   ------------------
   -- Compute_Args --
   ------------------

   function Compute_Args
     (E       : Entity_Id;
      Binders : Binder_Array) return W_Expr_Array
   is
      Logic_Args  : constant W_Expr_Array := Get_Logic_Args (E, True);
      Params      : constant W_Expr_Array :=
        (if Number_Of_Func_Args (E) = 0 then (1 .. 0 => <>)
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
                      Transform_Expr (Att_Val, EW_Int_Type, EW_Prog, Params)),
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
                  Ent : constant Entity_Id := Unique_Defining_Entity (Proc);
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
     (E : Entity_Id;
      Domain : EW_Domain)
      return Item_Array
   is
      Binders : constant Item_Array :=
        Compute_Subprogram_Parameters (E, Domain);
   begin
      --  If E has no parameters, return a singleton of unit type.

      if Binders'Length = 0 then
         return (1 =>
                   (Regular, Local => True, Init => <>, Main => Unit_Param));
      else
         return Binders;
      end if;
   end Compute_Binders;

   --------------------------
   -- Compute_Call_Effects --
   --------------------------

   function Compute_Call_Effects
     (Params : Transformation_Params;
      E      : Entity_Id)
      return W_Prog_Id
   is
      Call_Effects : W_Prog_Id;
   begin
      Call_Effects := New_Havoc_Statement
        (Ada_Node => E,
         Effects  => +Compute_Effects (E, Global_Params => True));

      Call_Effects := Sequence
        (Call_Effects,
         New_Assume_Statement
           (Ada_Node => E,
            Pred     => Compute_Dynamic_Property_For_Effects (E, Params)));

      return Call_Effects;
   end Compute_Call_Effects;

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

      procedure Include_Referenced_Entities is
         new Process_Referenced_Entities (Include_Entity);
   begin
      --  Collect global variables read or written in E

      case Ekind (E) is
         when E_Entry
            | E_Function
            | E_Procedure
            | E_Task_Type
            | E_Package
         =>
            Include_Referenced_Entities (E);

            --  Collect parameters of E if any

            if Is_Subprogram_Or_Entry (E) then
               Includes.Union (Get_Explicit_Formals (E));

               --  If E is a protected subprogram, add the type itself to stand
               --  for the self reference.

               if Within_Protected_Type (E)
                 and then Entity_Body_In_SPARK (E)
               then
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
      Func_Why_Binders     : constant Item_Array :=
        Compute_Binders (E, EW_Prog);
      Dynamic_Prop_Effects : W_Pred_Id := True_Pred;
   begin

      --  Compute the dynamic property of mutable parameters

      for I in Func_Why_Binders'Range loop

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
                       (if Self_Is_Mutable then
                           New_Deref (Right => Self_Name,
                                      Typ   => Get_Typ (Self_Name))
                        else +Self_Name);
                     Dyn_Prop  : constant W_Pred_Id :=
                       Compute_Dynamic_Invariant
                         (Expr             => +Self_Expr,
                          Ty               => Ada_Type,
                          Params           => Params,
                          Include_Type_Inv =>
                            Include_Non_Local_Type_Inv_For_Subp (E));
                  begin
                     Dynamic_Prop_Effects := +New_And_Expr
                       (Left   => +Dynamic_Prop_Effects,
                        Right  => +Dyn_Prop,
                        Domain => EW_Pred);
                  end;
               end if;
            end;
         elsif Item_Is_Mutable (Func_Why_Binders (I))
           and then Entity_In_SPARK
             (Get_Ada_Node_From_Item (Func_Why_Binders (I)))
         then
            declare
               Ada_Type : constant Node_Id :=
                 Get_Ada_Type_From_Item (Func_Why_Binders (I));
               Dyn_Prop : constant W_Pred_Id :=
                 Compute_Dynamic_Invariant
                   (Expr             =>
                      +Transform_Identifier
                      (Params => Params,
                       Expr   =>
                         Get_Ada_Node_From_Item (Func_Why_Binders (I)),
                       Ent    =>
                         Get_Ada_Node_From_Item (Func_Why_Binders (I)),
                       Domain => EW_Term),
                    Ty               => Ada_Type,
                    Params           => Params,
                    Include_Type_Inv =>
                      Include_Non_Local_Type_Inv_For_Subp (E));
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

      begin
         Flow_Utility.Get_Proof_Globals (Subprogram      => E,
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
                        Dyn_Prop : constant W_Pred_Id :=
                          Compute_Dynamic_Invariant
                            (Expr   =>
                               +Transform_Identifier (Params   => Params,
                                                      Expr     => Entity,
                                                      Ent      => Entity,
                                                      Domain   => EW_Term),
                             Ty     => Etype (Entity),
                             Params => Params);
                     begin
                        Dynamic_Prop_Effects := +New_And_Expr
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
      Global_Params : Boolean := False) return W_Effects_Id
   is
      Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids : Flow_Types.Flow_Id_Sets.Set;
      Eff       : constant W_Effects_Id := New_Effects;

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

            when Pointer =>
               if Binder.Mutable then
                  Effects_Append (Eff, Binder.Value.B_Name);
                  Effects_Append (Eff, Binder.Is_Null);
                  Effects_Append (Eff, Binder.Address);
               elsif Binder.Value.Mutable then
                  Effects_Append (Eff, Binder.Value.B_Name);
               end if;

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

      Flow_Utility.Get_Proof_Globals (Subprogram      => E,
                                      Reads           => Read_Ids,
                                      Writes          => Write_Ids,
                                      Erase_Constants => True);

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
                       (Ada_Ent_To_Why.Element (Symbol_Table, Entity));

                     if Is_Local_Borrower (Entity) then
                        Effects_Append_To_Writes (Eff, Get_Pledge_Id (Entity));
                     end if;
                  end if;

               end;

            when Magic_String =>
               Effects_Append_To_Writes
                 (Eff,
                  To_Why_Id (Obj => To_Name (Write_Id), Local => False));

            when others =>
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
                    Ada_Ent_To_Why.Element
                      (Symbol_Table, Formal);
               begin
                  Effects_Append_Binder_To_Writes (B);
               end;
               Next_Formal (Formal);
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

      --  For a possibly nonreturning procedure, add the special variable
      --  no__return in the write effects.

      if Has_Might_Not_Return_Annotation (E) then
         Effects_Append_To_Writes (Eff, M_Main.No_Return);
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
                       (Ada_Ent_To_Why.Element (Symbol_Table, Entity));
                  end if;
               end;

            when Magic_String =>
               Effects_Append_To_Reads
                 (Eff,
                  To_Why_Id (Obj => To_Name (Read_Id), Local => False));

            when others =>
               raise Program_Error;
         end case;
      end loop;

      return +Eff;
   end Compute_Effects;

   ---------------------------
   -- Compute_Guard_Formula --
   ---------------------------

   function Compute_Guard_Formula
     (Binders : Item_Array;
      Params  : Transformation_Params) return W_Pred_Id is
      Pred : W_Pred_Id := True_Pred;

   begin
      --  Add to guard the dynamic property of logic parameters.

      for B of Binders loop

         declare
            Ada_Node : constant Node_Id :=
              Get_Ada_Node_From_Item (B);
            Expr     : constant W_Expr_Id :=
              Reconstruct_Item (B, Params.Ref_Allowed);
            Ty_Node  : constant Entity_Id :=
              (if Present (Ada_Node) then
                   (if Is_Type (Ada_Node) then Ada_Node
                    else Etype (Ada_Node))
               else Empty);
            Dyn_Prop : constant W_Pred_Id :=
              (if Present (Ty_Node)  then
                    Compute_Dynamic_Invariant (Expr   => +Expr,
                                               Ty     => Ty_Node,
                                               Params => Params)
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
                    Expand_Abstract_State (K);

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
                              E : Entity_Id := Get_Direct_Mapping_Id (F);

                              pragma Assert (Ekind (E) in E_Abstract_State
                                                        | E_Constant
                                                        | E_Variable);

                           begin
                              --  Only partial views of constants are stored in
                              --  the symbol map.

                              if Ekind (E) = E_Constant
                                and then Is_Full_View (E)
                              then
                                 E := Partial_View (E);
                              end if;

                              --  Only consider objects that are in SPARK.
                              --  Other objects (and abstract states) are
                              --  translated to a private type in Why.

                              if Is_Object (E)
                                and then not Is_Part_Of_Concurrent_Object (E)
                              then
                                 declare
                                    Binder : constant Item_Type :=
                                      Ada_Ent_To_Why.Element (Symbol_Table, E);
                                    Expr   : constant W_Expr_Id :=
                                      Reconstruct_Item
                                        (Binder,
                                         Ref_Allowed => Params.Ref_Allowed);
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
                           end;

                        when Magic_String =>
                           pragma Assert (Is_Opaque_For_Proof (F));

                        when others =>
                           raise Program_Error;
                     end case;
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
                  --  Global variables accessed by the subprogram. Abstract
                  --  states and private variables are not considered here,
                  --  as they cannot have visible type invariants.

                  if Is_Object (E) then
                     Inv_Pred := +New_And_Then_Expr
                       (Left   => +Inv_Pred,
                        Right  => +Compute_Type_Invariant_For_Entity (E),
                        Domain => EW_Pred);

                  --  Self reference of protected subprograms

                  else pragma Assert (Is_Concurrent_Type (E));

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
         Formal : Entity_Id := First_Formal (Subp);

      begin
         while Present (Formal) loop
            if (if For_Input then Ekind (Formal) /= E_Out_Parameter
                else Ekind (Formal) /= E_In_Parameter)
            then
               Inv_Pred := +New_And_Then_Expr
                 (Left   => +Inv_Pred,
                  Right  => +Compute_Type_Invariant_For_Entity (Formal),
                  Domain => EW_Pred);
            end if;

            Next_Formal (Formal);
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

      Flow_Utility.Get_Proof_Globals (Subprogram      => E,
                                      Reads           => Read_Ids,
                                      Writes          => Write_Ids,
                                      Erase_Constants => True);

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
              (if not Result_Is_Mutable
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
      Effect_Binders : Item_Array :=
        Compute_Binders_For_Effects (E, Compute => True);
   begin
      Localize_Variable_Parts (Effect_Binders);
      return Raw_Binders & Effect_Binders;
   end Add_Logic_Binders;

   ---------------------------------
   -- Compute_Binders_For_Effects --
   ---------------------------------

   function Compute_Binders_For_Effects
     (E       : Entity_Id;
      Compute : Boolean) return Item_Array
   is
      Read_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids  : Flow_Types.Flow_Id_Sets.Set;

   begin
      --  Collect global variables potentially read and written

      Flow_Utility.Get_Proof_Globals (Subprogram      => E,
                                      Reads           => Read_Ids,
                                      Writes          => Write_Ids,
                                      Erase_Constants => True);

      --  Do not include binder for self reference as it is already included
      --  in binders for parameters.

      return Get_Binders_From_Variables
        (Read_Ids.Union (Write_Ids), Compute, Ignore_Self => True);
   end Compute_Binders_For_Effects;

   -------------------------
   -- Compute_Raw_Binders --
   -------------------------

   function Compute_Raw_Binders (E : Entity_Id) return Item_Array is
      Params        : constant List_Id :=
        Parameter_Specifications (Subprogram_Specification (E));
      Ada_Param_Len : constant Natural := Natural (List_Length (Params));
      Binder_Len    : constant Natural :=
        Ada_Param_Len + (if Within_Protected_Type (E) then 1 else 0);
      Result        : Item_Array (1 .. Binder_Len);
      Formal        : Entity_Id;
      Count         : Positive;

   begin
      Formal := First_Formal (E);
      Count := 1;

      if Within_Protected_Type (E) then
         declare
            Prot : constant Entity_Id := Containing_Protected_Type (E);
         begin
            Result (1) :=
              (Concurrent_Self, Local => True, Init => <>,
               Main => Concurrent_Self_Binder
                 (Prot, Mutable => Ekind (E) /= E_Function));
            Count := 2;
         end;
      end if;

      while Present (Formal) loop
         Result (Count) := Mk_Item_Of_Entity
           (E           => Formal,
            Local       => True,
            In_Fun_Decl => True);
         Next_Formal (Formal);
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

         WP_Consequence : W_Expr_Id :=
           Transform_Expr (Consequence, EW_Prog, Params);

      begin
         --  Possibly warn on an unreachable case

         WP_Consequence :=
           Warn_On_Dead_Branch (Consequence, WP_Consequence, Params.Phase);

         return Sequence
           (New_Ignore
              (Prog =>
                 +W_Expr_Id'(New_Conditional
                   (Ada_Node    => Contract_Case,
                    Domain      => EW_Prog,
                    Condition   => Enabled,
                    Then_Part   => WP_Consequence,
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
                 (Condition => Enabled,
                  Then_Part =>
                    Transform_Expr (Consequence, EW_Pred, Params),
                  Else_Part => +Result);
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
      Params             : Transformation_Params) return W_Expr_Id
   is
      Value  : constant Node_Id :=
        Retrieve_Inline_Annotation (Function_Entity);
      W_Def  : W_Expr_Id;

   begin
      if No (Value) then
         W_Def := Why_Empty;

      --  If Function_Entity is recursive, it is not inlined as it may
      --  interfere with its verification.

      elsif Is_Recursive (Function_Entity) then
         Error_Msg_N
           ("?recursive function cannot be inlined for proof",
            Function_Entity);

         W_Def := Why_Empty;

         --  We fill the map of parameters, so that in the definition, we use
         --  local names of the parameters, instead of the global names.

      else
         Ada_Ent_To_Why.Push_Scope (Symbol_Table);
         Push_Binders_To_Symbol_Table (Logic_Func_Binders);

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

   ------------------------
   -- Declare_Exceptions --
   ------------------------

   procedure Declare_Exceptions (File : W_Section_Id) is
   begin
      for Exc of Subprogram_Exceptions loop
         Emit (File, New_Exception_Declaration (Name => +Exc));
      end loop;
   end Declare_Exceptions;

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
                     (Name => Name & "__subprogram_lsp",
                      File => No_Symbol),
                   Comment =>
                     "Module for checking LSP for subprogram "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Current_Subp := E;

      --  First create a new identifier for F'Result

      if Ekind (E) = E_Function then
         Result_Is_Mutable := True;
         Result_Name :=
           New_Identifier
             (Name  => Name & "__result",
              Typ   => Type_Of_Node (E));
      end if;

      --  Clear the list of translations for X'Old expressions

      Reset_Map_For_Old;

      Params :=
        (File        => File,
         Phase       => Generate_VCs_For_Contract,
         Gen_Marker  => GM_None,
         Ref_Allowed => True,
         Old_Policy  => Use_Map);

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
      Post_Spec :=
        +New_And_Expr
        (Left   =>
           +Compute_Spec (Params, Post_List, EW_Pred),
         Right  => +Compute_Contract_Cases_Postcondition (Params, E),
         Domain => EW_Pred);

      --  Compute the effect of a call of the subprogram

      Call_Effects := Compute_Call_Effects (Params, E);

      --  If E has a class-wide precondition, check that it cannot raise a
      --  run-time error in an empty context.

      if not Classwide_Pre_List.Is_Empty then
         Classwide_Pre_RTE :=
           +Compute_Spec (Params, Classwide_Pre_List, EW_Prog);
         Classwide_Pre_RTE := New_Ignore (Prog => Classwide_Pre_RTE);
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

         Classwide_Weaker_Pre := New_Ignore (Prog => Classwide_Weaker_Pre);
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

         Weaker_Pre := New_Ignore (Prog => Weaker_Pre);
      end if;

      --  If E has a specific postcondition, check that it is stronger than the
      --  dispatching one. To that end, perform equivalent effects of call in
      --  context of precondition for static call.
      --  Skip this check if the dispatching postcondition is the default True
      --  postcondition.

      if not (Post_List.Is_Empty
               and then No (Get_Pragma (E, Pragma_Contract_Cases)))
        and then not (Classwide_Post_List.Is_Empty
                        and then
                      Inherited_Post_List.Is_Empty)
      then
         Pre_Assume :=
           New_Assume_Statement (Pred =>
             Get_Static_Call_Contract (Params, E, Pragma_Precondition));

         Post_Assume := New_Assume_Statement (Pred => Post_Spec);

         Classwide_Post_Check := New_Located_Assert
           (Ada_Node =>
              (if Post_List.Is_Empty then
                    Get_Location_For_Aspect (E, Pragma_Contract_Cases)
               else Get_Location_For_Aspect (E, Pragma_Postcondition)),
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
           New_Ignore (Prog => Stronger_Post);
      end if;

      --  If E is overriding another subprogram, check that its specified
      --  classwide postcondition is stronger than the inherited one.
      --  Note that we should *not* assume the dispatching precondition for
      --  this check, as this would not be transitive.

      if not Classwide_Post_List.Is_Empty
        and then Is_Overriding_Subprogram (E)
      then

         Classwide_Post_Assume :=
           New_Assume_Statement (Pred => Classwide_Post_Spec);

         Inherited_Post_Check := New_Located_Assert
           (Ada_Node => Get_Location_For_Aspect (E, Pragma_Postcondition,
            Classwide => True),
            Pred     => Inherited_Post_Spec,
            Reason   => VC_Stronger_Classwide_Post,
            Kind     => EW_Assert);

         Stronger_Classwide_Post := Sequence
           ((1 => New_Comment
             (Comment =>
                NID ("Checking that inherited postcondition is"
                  & " implied by class-wide postcondition")),
             2 => Call_Effects,
             3 => Classwide_Post_Assume,
             4 => Inherited_Post_Check));

         Stronger_Classwide_Post :=
           New_Ignore (Prog => Stronger_Classwide_Post);
      end if;

      Why_Body := Sequence
        ((1 => Classwide_Pre_RTE,
          2 => Classwide_Weaker_Pre,
          3 => Weaker_Pre,
          4 => Stronger_Post,
          5 => Stronger_Classwide_Post));

      --  add declarations for 'Old variables

      Why_Body := Bind_From_Mapping_In_Expr
        (Params                 => Params,
         Map                    => Map_For_Old,
         Expr                   => Why_Body,
         Do_Runtime_Error_Check => False,
         Bind_Value_Of_Old      => True);

      --  Check that the class-wide postcondition cannot raise runtime errors.
      --  To that end, perform equivalent effects of call in an empty context.
      --  Also check that the evaluation of 'Old variables are free of RTE in
      --  the empty context. Here again, we should *not* assume the dispatching
      --  precondition for this check, as this postcondition can be inherited
      --  in overridings weakening the precondition.

      if not Classwide_Post_List.Is_Empty then

         --  Clear the list of translations for X'Old expressions

         Reset_Map_For_Old;

         Classwide_Post_RTE :=
           +Compute_Spec (Params, Classwide_Post_List, EW_Prog);
         Classwide_Post_RTE :=
           New_Ignore (Prog => Classwide_Post_RTE);
         Classwide_Post_RTE := Sequence
           ((1 => New_Comment (Comment =>
                               NID ("Checking absence of RTE in"
                                  & " class-wide postcondition")),
             2 => Call_Effects,
             3 => Classwide_Post_RTE));

         --  add declarations for 'Old variables with RTE

         Classwide_Post_RTE := Bind_From_Mapping_In_Expr
           (Params                 => Params,
            Map                    => Map_For_Old,
            Expr                   => Classwide_Post_RTE,
            Do_Runtime_Error_Check => True,
            Bind_Value_Of_Old      => True);
      end if;

      Why_Body := Sequence (Why_Body, Classwide_Post_RTE);

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
               Location => No_Location,
               Ref_Type => Type_Of_Node (E)));
      end if;

      Emit (File,
            Why.Gen.Binders.New_Function_Decl
              (Domain   => EW_Prog,
               Name     => Def_Name,
               Binders  => (1 => Unit_Param),
               Labels   => Symbol_Sets.To_Set (Cur_Subp_Sloc),
               Location => Safe_First_Sloc (E),
               Def      => +Why_Body));

      --  We should *not* filter our own entity, it is needed for recursive
      --  calls.

      if Ekind (E) = E_Function then
         Result_Name := Why_Empty;
         Result_Is_Mutable := False;
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
      Body_N     : constant Node_Id := Package_Body (E);
      Vis_Decls  : constant List_Id :=
        Visible_Declarations_Of_Package (E);
      Priv_Decls : constant List_Id :=
        Private_Declarations_Of_Package (E);
      Init_Cond  : constant Node_Id :=
        Get_Pragma (E, Pragma_Initial_Condition);
      Params     : Transformation_Params;

      Why_Body   : W_Prog_Id := +Void;
      Post       : W_Pred_Id;

   begin
      --  We open a new theory, so that the context is fresh for that package

      Open_Theory (File,
                   New_Module
                     (Name => Name & "__package_def",
                      File => No_Symbol),
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
                 Gen_Marker  => GM_None,
                 Ref_Allowed => True,
                 Old_Policy  => Use_Map);

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

         Emit
           (File,
            New_Global_Ref_Declaration
              (Ada_Node => Containing_Protected_Type (E),
               Name     => Self_Name,
               Labels   => Symbol_Sets.Empty_Set,
               Location => Safe_First_Sloc (E),
               Ref_Type =>
                 Type_Of_Node (Containing_Protected_Type (E))));
      end if;

      --  Translate initial condition of E

      if Present (Init_Cond)
        and then (No (Body_N) or else Entity_Body_In_SPARK (E))
      then
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
         Post := Why_Empty;
      end if;

      --  Translate declarations and statements in the package body, if there
      --  is one and it is in SPARK.

      if Entity_Body_In_SPARK (E) then
         if Present (Handled_Statement_Sequence (Body_N))
           and then Body_Statements_In_SPARK (E)
         then
            Why_Body :=
              Sequence
                (Transform_Statements_And_Declarations
                   (Statements (Handled_Statement_Sequence (Body_N))),
                 Why_Body);
         end if;

         Why_Body :=
           Transform_Declarations_Block (Declarations (Body_N), Why_Body);

         --  Assume initial conditions of withed units from the body

         if Is_Compilation_Unit (E) then
            Params.Phase := Generate_VCs_For_Contract;
            Why_Body := Sequence
              (Assume_Initial_Condition_Of_Withed_Units
                 (Package_Body_Entity (Body_N), Params),
               Why_Body);
         end if;
      end if;

      --  Introduce a check for the type invariant of all the variables
      --  initialized by the package.

      declare
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);
         Check : constant W_Pred_Id :=
           Compute_Type_Invariants_For_Package (E, Params);
      begin
         if not Is_True_Boolean (+Check) then
            Why_Body :=
              Sequence
                (Why_Body,
                 New_Assert
                      (Pred        =>
                         +New_VC_Expr (E, +Check, VC_Invariant_Check, EW_Pred),
                       Assert_Kind => EW_Assert));
         end if;
      end;

      --  Translate public and private declarations of the package

      if Present (Priv_Decls)
        and then Private_Spec_In_SPARK (E)
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
                       (File        => File,
                        Phase       => Generate_Contract_For_Body,
                        Gen_Marker  => GM_None,
                        Ref_Allowed => True,
                        Old_Policy  => Use_Map);
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

               Why_Body := Sequence
                 (New_Assume_Statement (Pred => Pre), Why_Body);
            end;
         end if;
      end;

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

      --  Declare the toplevel exceptions for exit paths

      Declare_Exceptions (File);

      Emit (File,
            Why.Gen.Binders.New_Function_Decl
              (Domain   => EW_Prog,
               Name     => Def_Name,
               Binders  => (1 => Unit_Param),
               Location => Safe_First_Sloc (E),
               Labels   => Symbol_Sets.To_Set (Cur_Subp_Sloc),
               Post     => Post,
               Def      => +Why_Body));

      --  Cleanup

      Self_Name := Why_Empty;
      Self_Is_Mutable := False;

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

         if Has_Discriminants (E) then
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
               Insert_Entity (Discr_N, Discr_W.Id);

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
                     (Name => Name & "__protected_type",
                      File => No_Symbol),
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

      Self_Name := Concurrent_Self_Ident (E);
      Self_Is_Mutable := False;

      Emit (File,
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

      if Present (Priv_Decls)
        and then Private_Spec_In_SPARK (E)
      then
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

                     F_Check := +Transform_Expr
                       (Expr          =>
                          Expression (Enclosing_Declaration (Field)),
                        Expected_Type => Type_Of_Node (Etype (Field)),
                        Domain        => EW_Prog,
                        Params        => Body_Params);
                  else

                     --  Otherwise, use its Field's Etype default value

                     F_Check :=
                       Compute_Default_Check
                         (Field, Etype (Field), Body_Params);
                  end if;

                  if F_Check /= +Void then
                     Sequence_Append
                       (Checks,
                        New_Ignore
                          (Ada_Node => Etype (Field),
                           Prog     => F_Check));
                  end if;
               end if;
            end loop;
            Why_Body := Sequence (Why_Body, +Checks);
         end;

         Why_Body := Transform_Declarations_Block (Priv_Decls, Why_Body);
      end if;

      if Present (Vis_Decls) then
         Why_Body := Transform_Declarations_Block (Vis_Decls, Why_Body);
      end if;

      Wrap_Discr (Why_Body);

      Emit (File,
            Why.Gen.Binders.New_Function_Decl
              (Domain   => EW_Prog,
               Name     => Def_Name,
               Binders  => (1 => Unit_Param),
               Location => Safe_First_Sloc (E),
               Labels   => Symbol_Sets.To_Set (Cur_Subp_Sloc),
               Def      => +Why_Body));

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

      function Comp_Decl_At_Subp_Start return W_Prog_Id;
      --  The body of the subprogram may contain declarations that are in fact
      --  essential to prove absence of RTE in the pre, e.g. compiler-generated
      --  subtype declarations. We need to take those into account.

      function RTE_Of_Pre return W_Prog_Id;
      --  Compute an expression which contains the RTE checks of the
      --  precondition.

      function Assume_Or_Assert_Of_Pre return W_Prog_Id;
      --  Usually assumes the precondition, except for main programs where
      --  the precondition needs to be proved in fact. In this latter case
      --  an assertion is returned instead of an assumption.

      function Check_Inline_For_Proof return W_Prog_Id;
      --  Checks that the expression used for inlining is equal to the result

      function Check_Init_Of_Out_Params return W_Prog_Id;
      --  Checks initialization of out parameters at the end of the subprogram

      function Check_Invariants_Of_Outputs return W_Prog_Id;
      --  Checks the type invariants of global output and of out parameters if
      --  E is a boundary subprogram.

      function Checking_Of_Refined_Post (Arg : W_Prog_Id) return W_Prog_Id
      with Pre => Entity_Body_In_SPARK (E);
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

      function Warn_On_Inconsistent_Pre return W_Prog_Id;
      --  Generate a VC to warn on inconsistent preconditions

      function Warn_On_Inconsistent_Post return W_Prog_Id;
      --  Generate a VC to warn on inconsistent postconditions

      function Wrap_Decls_For_CC_Guards (P : W_Prog_Id) return W_Prog_Id;

      function Havoc_Borrowed_Expressions
        (Borrows : Node_Lists.List) return W_Prog_Id;

      ----------------------
      -- Assume_For_Input --
      ----------------------

      function Assume_For_Input return W_Prog_Id is
         Pred_Fun_Param : constant Entity_Id :=
           (if Ekind (E) = E_Function and then Is_Predicate_Function (E)
            then
               First_Formal (E)
            else
               Empty);
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);
      begin
         if Ekind (E) = E_Procedure and then Null_Present (E) then
            return +Void;
         end if;
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

      -----------------------------
      -- Assume_Or_Assert_Of_Pre --
      -----------------------------

      function Assume_Or_Assert_Of_Pre return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);
         Pre_Node : constant Node_Id :=
           Get_Location_For_Aspect (E, Pragma_Precondition);
         Pre : W_Pred_Id :=
           Get_Static_Call_Contract (Params, E, Pragma_Precondition);
         Stmt : W_Prog_Id;

      begin
         --  Need to prove precondition of Main before use. The test for
         --  entries is just to protect the call to Might_Be_Main.

         if not Is_Entry (E) and then Might_Be_Main (E) then
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
            if Is_Entry (E)
              and then Entity_Body_In_SPARK (E)
            then
               declare
                  Params : constant Transformation_Params :=
                    (File        => File,
                     Phase       => Generate_Contract_For_Body,
                     Gen_Marker  => GM_None,
                     Ref_Allowed => True,
                     Old_Policy  => Use_Map);
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
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);
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
               if B.Init.Present then
                  pragma Assert (Ekind (Param) = E_Out_Parameter);
                  Checks := Sequence
                    (Left  => Checks,
                     Right => New_Located_Assert
                       (Ada_Node => Param,
                        Pred     => Pred_Of_Boolean_Term
                          (New_Deref (Right => B.Init.Id,
                                      Typ   => EW_Bool_Type)),
                        Reason   => VC_Initialization_Check,
                        Kind     => EW_Assert));
               end if;
            end;
            Next_Formal (Param);
         end loop;
         return Checks;
      end Check_Init_Of_Out_Params;

      ----------------------------
      -- Check_Inline_For_Proof --
      ----------------------------

      function Check_Inline_For_Proof return W_Prog_Id is
         Value  : constant Node_Id := Retrieve_Inline_Annotation (E);
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);
      begin
         if Present (Value) and then
           (not Is_Expression_Function_Or_Completion (E)
            or else not Entity_Body_Compatible_With_SPARK (E))
         then
            return New_Assert
              (Pred        =>
                 +New_VC_Expr
                 (Ada_Node => Find_Inline_Pragma (E),
                  Expr     =>
                    New_Comparison
                      (Symbol => Why_Eq,
                       Left   => New_Deref
                         (Right => Result_Name,
                          Typ   => Get_Typ (Result_Name)),
                       Right  => Compute_Inlined_Expr
                         (Function_Entity    => E,
                          Logic_Func_Binders => (1 .. 0 => <>),
                          W_Return_Type      => Get_Typ (Result_Name),
                          Params             => Params),
                       Domain => EW_Pred),
                    Reason   => VC_Inline_Check,
                    Domain   => EW_Pred),
               Assert_Kind => EW_Assert);
         else
            return +Void;
         end if;
      end Check_Inline_For_Proof;

      ---------------------------------
      -- Check_Invariants_Of_Outputs --
      ---------------------------------

      function Check_Invariants_Of_Outputs return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);
         Check : constant W_Pred_Id :=
           Compute_Type_Invariants_For_Subprogram (E, False, Params);
      begin
         if Is_True_Boolean (+Check) then
            return +Void;
         else
            return New_Assert
              (Pred        =>
                 +New_VC_Expr
                   (Ada_Node => E,
                    Expr     => +Check,
                    Reason   => VC_Invariant_Check,
                    Domain   => EW_Pred),
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
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);

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
         if Entity_Body_In_SPARK (E) then
            return
           Sequence
             (New_Comment
              (Comment => NID ("Declarations introduced by the compiler at the"
               & " beginning of the subprogram"
               & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                 else ""))),
              Transform_Declarations_For_Params (Declarations (Body_N)));
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

      --------------------------------
      -- Havoc_Borrowed_Expressions --
      --------------------------------

      function Havoc_Borrowed_Expressions
        (Borrows : Node_Lists.List) return W_Prog_Id
      is
         Result : W_Statement_Sequence_Id := Void_Sequence;

      begin
         --  Don't havoc local borrowers in functions. They cannot have
         --  modified anything visible from outside of the subprogram.

         if Ekind (E) /= E_Function then
            for E of Borrows loop
               Sequence_Append
                 (Result,
                  Havoc_Borrowed_Expression (E));
            end loop;
         end if;
         return +Result;
      end Havoc_Borrowed_Expressions;

      ------------------
      -- Post_As_Pred --
      ------------------

      function Post_As_Pred return W_Pred_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_Contract_For_Body,
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => As_Old);
         Mark_Params : Transformation_Params := Params;
         Post_N    : Node_Id;
      begin

         Mark_Params.Gen_Marker := GM_All;

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
         if Entity_Body_In_SPARK (E) then

            --  Translate contract of E. A No_Return subprogram, from the
            --  inside, has postcondition true as non-termination verification
            --  is done by the frontend, but the precondition is unchanged.

            if No_Return (E) or else No (Post_N) then
               pragma Assert (if No (Post_N) then
                                 Is_True_Boolean
                                (+Get_Static_Call_Contract
                                   (Mark_Params, E, Pragma_Postcondition)));
               return Why_Empty;
            else
               return
                 +New_VC_Expr (Post_N,
                               +Get_Static_Call_Contract
                                 (Mark_Params, E, Pragma_Postcondition),
                               VC_Postcondition,
                               EW_Pred);
            end if;
         else
            return Why_Empty;
         end if;
      end Post_As_Pred;

      ----------------
      -- RTE_Of_Pre --
      ----------------

      function RTE_Of_Pre return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);

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
         Result : W_Prog_Id;
      begin
         if Prags.Is_Empty then
            Result := +Void;
         else
            Result :=
              New_Comment
                (Comment => NID (Comment &
                                 (if Sloc (E) > 0 then
                                  " " & Build_Location_String (Sloc (E))
                                  else "")));

            for Prag of Prags loop
               Result :=
                 Sequence (Result, Transform_Pragma (Prag, Force => True));
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
                (1 =>
                       New_Handler
                   (Name => M_Main.Return_Exc,
                    Def  => +Void)));
      end Try_Block;

      -------------------------------
      -- Warn_On_Inconsistent_Post --
      -------------------------------

      function Warn_On_Inconsistent_Post return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);
         Post : W_Pred_Id :=
           Get_Static_Call_Contract (Params, E, Pragma_Postcondition);
         Stmt : W_Prog_Id;
         Post_Node : constant Node_Id :=
           Get_Location_For_Aspect (E, Pragma_Postcondition);
      begin
         if No (Post_Node) then
            return +Void;
         end if;

         --  Negate the condition to check for an inconsistency
         Post := New_Not (Right => +Post);

         Stmt := Sequence
           (Compute_Call_Effects (Params, E),
            New_Located_Assert
              (Ada_Node => Post_Node,
               Pred     => Post,
               Reason   => VC_Inconsistent_Post,
               Kind     => EW_Assert));

         return
           Sequence
             (New_Comment
                (Comment => NID ("Check inconsistency of Post of subprogram"
                 & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                   else ""))),
              New_Ignore (Prog => Stmt));
      end Warn_On_Inconsistent_Post;

      ------------------------------
      -- Warn_On_Inconsistent_Pre --
      ------------------------------

      function Warn_On_Inconsistent_Pre return W_Prog_Id is
         Params : constant Transformation_Params :=
           (File        => File,
            Phase       => Generate_VCs_For_Contract,
            Gen_Marker  => GM_None,
            Ref_Allowed => True,
            Old_Policy  => Use_Map);
         Pre : W_Pred_Id :=
           Get_Static_Call_Contract (Params, E, Pragma_Precondition);
         Stmt : W_Prog_Id;
         Pre_Node : constant Node_Id :=
           Get_Location_For_Aspect (E, Pragma_Precondition);
      begin
         if No (Pre_Node) then
            return +Void;
         end if;

         if Is_Entry (E) then
            declare
               Params : constant Transformation_Params :=
                 (File        => File,
                  Phase       => Generate_Contract_For_Body,
                  Gen_Marker  => GM_None,
                  Ref_Allowed => True,
                  Old_Policy  => Use_Map);
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
                (Comment => NID ("Check inconsistency of Pre of subprogram"
                 & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                   else ""))),
              New_Ignore (Prog => Stmt));
      end Warn_On_Inconsistent_Pre;

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

      CC_Check  : W_Prog_Id;
      Prog      : W_Prog_Id;
      Why_Body  : W_Prog_Id;

      Result_Var : W_Prog_Id;

      Raise_Stmt : constant W_Prog_Id :=
        New_Raise
          (Ada_Node => Body_N,
           Name     => M_Main.Return_Exc);

      Precondition_Is_Statically_False  : Boolean := False;
      Postcondition_Is_Statically_False : Boolean := False;

      Borrowers : Node_Lists.List;

   --  Start of processing for Generate_VCs_For_Subprogram

   begin
      Open_Theory (File,
                   New_Module
                     (Name => Name & "__subprogram_def",
                      File => No_Symbol),
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
         Gen_Marker  => GM_None,
         Ref_Allowed => True,
         Old_Policy  => Use_Map);

      Contract_Params :=
        (File        => File,
         Phase       => Generate_VCs_For_Contract,
         Gen_Marker  => GM_None,
         Ref_Allowed => True,
         Old_Policy  => As_Old);

      --  Reset the toplevel exceptions for exit paths

      Clear_Exceptions;

      --  First, clear the list of translations for X'Old expressions, and
      --  create a new identifier for F'Result.

      Reset_Map_For_Old;

      if Ekind (E) = E_Function then
         Result_Name :=
           New_Identifier
             (Name  => Name & "__result",
              Typ   => Type_Of_Node (E));
         Result_Is_Mutable := True;

         Result_Var :=
           New_Deref
             (Ada_Node => Body_N,
              Right    => Result_Name,
              Typ      => Type_Of_Node (E));
      else
         Result_Var := +Void;
      end if;

      if Within_Protected_Type (E) then
         declare
            CPT : constant Entity_Id := Containing_Protected_Type (E);
         begin
            --  The Ada_Node is important here, because that's how we detect
            --  occurrences of "self" in a term later.

            Self_Name := Concurrent_Self_Ident (CPT);
            Self_Is_Mutable := True;
         end;
      end if;

      --  Only warn on statically False precondition that is not written as
      --  "False" in the source code, so as to warn about cases where the
      --  configuration leads to a precondition being False.

      for Expr of Get_Precondition_Expressions (E) loop
         if Nkind (Expr) in N_Expanded_Name | N_Identifier
           and then Entity (Expr) = Standard_False
           and then Original_Node (Expr) /= Expr
         then
            Precondition_Is_Statically_False := True;
            Error_Msg_N (Msg  => "?precondition is statically False",
                         N    => Expr);
         end if;
      end loop;

      for Expr of Get_Postcondition_Expressions (E, Refined => False) loop
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

      Compute_Contract_Cases_Guard_Map
        (E                  => E,
         Guard_Map          => Guard_Map,
         Others_Guard_Ident => Others_Guard_Ident,
         Others_Guard_Expr  => Others_Guard_Expr);

      CC_Check := Compute_Contract_Cases_Entry_Checks (E, Guard_Map);

      --  Declare global variable to hold the state of a protected object

      if Within_Protected_Type (E) then
         Emit
           (File,
            New_Global_Ref_Declaration
              (Ada_Node => Containing_Protected_Type (E),
               Name     => Self_Name,
               Labels   => Symbol_Sets.Empty_Set,
               Location => Safe_First_Sloc (E),
               Ref_Type =>
                 Type_Of_Node (Containing_Protected_Type (E))));
      end if;

      --  Declare a global variable to hold the result of a function. This is
      --  useful both for verifying the body of E when it is in SPARK, and for
      --  the warning on inconsistent postcondition when it is issued.

      if Ekind (E) = E_Function then
         Emit
           (File,
            New_Global_Ref_Declaration
              (Ada_Node => E,
               Name     => Result_Name,
               Labels   => Get_Counterexample_Labels (E),
               Location => No_Location,
               Ref_Type => Type_Of_Node (E)));

         --  If E is a traversal function returning a borrower, declare a
         --  reference for the plege of its result.

         if Is_Borrowing_Traversal_Function (E) then
            declare
               Result_Pledge : constant W_Identifier_Id :=
                 Result_Pledge_Id (E);
            begin
               Emit (File,
                     New_Global_Ref_Declaration
                       (Name     => Result_Pledge,
                        Ref_Type => Get_Typ (Result_Pledge),
                        Labels   => Symbol_Sets.Empty_Set,
                        Location => No_Location));
            end;
         end if;
      end if;

      if Entity_Body_In_SPARK (E) then

         Get_Pre_Post_Pragmas
           (Get_Flat_Statement_And_Declaration_List
              (Declarations (Body_N)));

         Get_Borrows_From_Decls (Declarations (Body_N), Borrowers);

         Why_Body :=
           Sequence
             ((1 => Check_Ceiling_Protocol (Body_Params, E),
               2 => Transform_Declarations_For_Body (Declarations (Body_N)),
               3 => Transform_Statements_And_Declarations
                 (Statements
                   (Handled_Statement_Sequence (Body_N))),
               4 => Raise_Stmt));

         --  Enclose the subprogram body in a try-block, so that return
         --  statements can be translated as raising exceptions.

         Why_Body := Try_Block (Why_Body);

         --  Check pragmas Precondition and Postcondition in the body of the
         --  subprogram as plain assertions.

         Why_Body := Sequence
           ((1 => Transform_All_Pragmas
                    (Pre_Prags, "checking of pragma precondition"),
             2 => Why_Body,
             3 => Havoc_Borrowed_Expressions (Borrowers),
             4 => Transform_All_Pragmas
                    (Post_Prags, "checking of pragma postcondition")));

         Why_Body := Checking_Of_Refined_Post (Why_Body);

         --  Check type invariants on subprogram's ouput, absence of runtime
         --  errors in Post and RTE + validity of contract cases, and
         --  Inline_For_Proof annotation.

         Why_Body := Sequence
           ((1 => Why_Body,
             2 => Check_Init_Of_Out_Params,
             3 => Check_Invariants_Of_Outputs,
             4 => CC_And_RTE_Post,
             5 => Check_Inline_For_Proof,
             6 => Result_Var));

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

            procedure Search_Olds is new
              Traverse_More_Proc (Search_Old);

            Prag_Post : constant Node_Id :=
              Get_Pragma (E, Pragma_Postcondition);

            Prag_CC : constant Node_Id :=
              Get_Pragma (E, Pragma_Contract_Cases);

         begin
            Search_Olds (Prag_Post);
            Search_Olds (Prag_CC);

            Why_Body := +Void;
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

         Prog := Sequence ((CC_Check, Warn_Post, Why_Body));
         Prog := Declare_Old_Variables (Prog);
         Prog := Wrap_Decls_For_CC_Guards (Prog);

         Prog := Sequence
           ((Assume_For_Input,
             Comp_Decl_At_Subp_Start,
             RTE_Of_Pre,
             Warn_Pre,
             Assume_Or_Assert_Of_Pre,
             Prog));
      end;

      --  Assume values of constants

      Assume_Value_Of_Constants (Prog, E, Contract_Params);

      --  Declare the toplevel exceptions for exit paths

      Declare_Exceptions (File);

      Emit (File,
            Why.Gen.Binders.New_Function_Decl
              (Domain   => EW_Prog,
               Name     => Def_Name,
               Binders  => (1 => Unit_Param),
               Labels   => Symbol_Sets.To_Set (Cur_Subp_Sloc),
               Location => Safe_First_Sloc (E),
               Post     => Post_As_Pred,
               Def      => +Prog));

      --  cleanup

      Self_Name := Why_Empty;
      Self_Is_Mutable := False;

      if Ekind (E) = E_Function then
         Result_Name := Why_Empty;
         Result_Is_Mutable := False;
      end if;

      --  We should *not* filter our own entity, it is needed for recursive
      --  calls.

      Close_Theory (File,
                    Kind => VC_Generation_Theory,
                    Defined_Entity => E);

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
            Emit_Static_Proof_Result
              (Source,
               VC_UC_No_Holes,
               Is_Valid_Bitpattern_No_Holes (Src_Ty),
               E,
               PC_Trivial);
            Emit_Static_Proof_Result
              (Target,
               VC_UC_No_Holes,
               Is_Valid_Bitpattern_No_Holes (Tar_Ty),
               E,
               PC_Trivial);
            Emit_Static_Proof_Result
              (E,
               VC_UC_Same_Size,
               Types_Have_Same_Known_Esize (Src_Ty, Tar_Ty),
               E,
               PC_Trivial);
         end;
      end if;
   end Generate_VCs_For_Subprogram;

   --------------------------------
   -- Generate_VCs_For_Task_Type --
   --------------------------------

   procedure Generate_VCs_For_Task_Type
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Name   : constant String  := Full_Name (E);
      Body_N : constant Node_Id := Task_Body (E);
      Params : Transformation_Params;

      Why_Body   : W_Prog_Id;
      Priv_Decls : constant List_Id := Private_Declarations_Of_Task_Type (E);
      Vis_Decls  : constant List_Id := Visible_Declarations_Of_Task_Type (E);

   begin
      --  We open a new theory, so that the context is fresh for this task

      Open_Theory (File,
                   New_Module
                     (Name => Name & "__task_body",
                      File => No_Symbol),
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
                 Gen_Marker  => GM_None,
                 Ref_Allowed => True,
                 Old_Policy  => Use_Map);

      --  Reset the toplevel exceptions for exit paths

      Clear_Exceptions;

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      --  Translate declarations and statements in the task body, if there
      --  is one.

      if Entity_Body_In_SPARK (E) then
         Why_Body :=
           Transform_Statements_And_Declarations
             (Statements (Handled_Statement_Sequence (Body_N)));

         Why_Body :=
           Transform_Declarations_Block (Declarations (Body_N), Why_Body);

         --  We check that the call graph starting from this task respects the
         --  ceiling priority protocol.

         Why_Body :=
           Sequence
             (Check_Ceiling_Protocol (Params, E),
              Why_Body);
      else
         Why_Body := +Void;
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

      --  We assume that objects used in the program are in range, if
      --  they are of a dynamic type.

      Why_Body :=
        Sequence
          (Compute_Dynamic_Property_For_Inputs (Params => Params,
                                                E      => E),
           Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Body, E, Params);

      --  Declare the toplevel exceptions for exit paths

      Declare_Exceptions (File);

      declare
         Post : W_Pred_Id;
      begin
         if Entity_Body_In_SPARK (E) then
            Post :=
              +New_VC_Expr (Ada_Node   => E,
                            Expr       => +False_Pred,
                            Reason     => VC_Task_Termination,
                            Domain     => EW_Pred);
         else
            Post := Why_Empty;
         end if;
         Emit (File,
               Why.Gen.Binders.New_Function_Decl
                 (Domain   => EW_Prog,
                  Name     => Def_Name,
                  Binders  => (1 => Unit_Param),
                  Location => Safe_First_Sloc (E),
                  Labels   => Symbol_Sets.To_Set (Cur_Subp_Sloc),
                  Post     => Post,
                  Def      => +Why_Body));
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      Close_Theory (File,
                    Kind => VC_Generation_Theory);

   end Generate_VCs_For_Task_Type;

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

      --  Use this variable to temporarily store current theory.
      --  Initial value is never used. Add it to remove CodePeer warning.
      Save_Theory   : W_Theory_Declaration_Id := Why_Empty;

   begin
      Params :=
        (File        => File,
         Phase       => Generate_Logic,
         Gen_Marker  => GM_None,
         Ref_Allowed => False,
         Old_Policy  => Ignore);

      if Ekind (E) = E_Function then
         Why_Type := Type_Of_Node (E);
      end if;

      --  Do not generate an axiom for the postcondition of:
      --    * potentially non-returning functions as the axiom could be
      --      unsound,
      --    * volatile functions and protected subprograms.

      if Ekind (E) in E_Procedure | Entry_Kind
        or else Has_Pragma_Volatile_Function (E)
        or else (Is_Potentially_Nonreturning (E)
                 and then (not Is_Scalar_Type (Etype (E))
                           or else not Use_Split_Form_For_Type (Etype (E))))
      then
         return;

      --  We generate an axiom for the return type of a recursive or
      --  non-terminating function if it is a (non empty) static scalar type as
      --  their range property is always sound. For dynamic scalar types, we
      --  assume the bounds of their first static ancestor.

      elsif Is_Potentially_Nonreturning (E) then

         --  Expression functions will have their own definition axiom which
         --  may contradict the range axiom. Do not emit range axiom for them.

         if Is_Expression_Function_Or_Completion (E)
           and then Entity_Body_Compatible_With_SPARK (E)
         then
            return;
         end if;

         pragma Assert (Is_Scalar_Type (Etype (E))
                        and then Use_Split_Form_For_Type (Etype (E)));
         declare
            Logic_Why_Binders   : constant Binder_Array :=
              To_Binder_Array (Logic_Func_Binders);
            Logic_Id            : constant W_Identifier_Id :=
              To_Why_Id (E, Domain => EW_Term, Local => False);
            Dynamic_Prop_Result : constant W_Pred_Id :=
              +New_Dynamic_Property
              (Domain => EW_Pred,
               Ty     => (if Type_Is_Modeled_As_Base (Etype (E)) then
                               Get_Base_Of_Type (Etype (E))
                          else Retysp (Etype (E))),
               Expr   => +New_Result_Ident (Why_Type),
               Params => Params);
         begin
            Emit
              (File,
               New_Guarded_Axiom
                 (Ada_Node => Empty,
                  Name     => NID (Short_Name (E) & "__" & Post_Axiom),
                  Binders  => Logic_Why_Binders,
                  Triggers =>
                    New_Triggers
                      (Triggers =>
                           (1 => New_Trigger
                              (Terms =>
                                 (1 => New_Call
                                      (Domain  => EW_Term,
                                       Name    => Logic_Id,
                                       Binders => Logic_Why_Binders))))),
                  Def      =>
                    +New_Typed_Binding
                    (Ada_Node => Empty,
                     Domain   => EW_Pred,
                     Name     => +New_Result_Ident (Why_Type),
                     Def      => New_Call
                       (Domain  => EW_Term,
                        Name    => Logic_Id,
                        Binders => Logic_Why_Binders),
                     Context  => +Dynamic_Prop_Result)));
         end;
         return;
      end if;

      pragma Assert (Has_Post_Axiom (E));

      --  For recursive functions, we store the axiom in a different module,
      --  so that we can make sure that it cannot be used to prove the function
      --  itself.

      if Is_Recursive (E) then

         --  Raise a warning about missing (implicit) contract on recursive
         --  calls.

         declare
            Has_Explicit_Contracts : constant Boolean :=
              Has_Contracts (E, Pragma_Postcondition)
              or else Has_Contracts (E, Pragma_Contract_Cases);
            Has_Implicit_Contracts : constant Boolean :=
              Type_Needs_Dynamic_Invariant (Etype (E));
         begin

            if Debug.Debug_Flag_Underscore_F
              and then (Has_Implicit_Contracts or else Has_Explicit_Contracts)
            then
               declare
                  String_For_Implicit : constant String :=
                    (if Has_Explicit_Contracts then ""
                     else "implicit ");
               begin
                  Error_Msg_N
                    ("info: ?" & String_For_Implicit
                     & "function contract might not be available on "
                     & "recursive calls", E);
               end;
            end if;
         end;

         Save_Theory := Why_Sections (File).Cur_Theory;
         Why_Sections (File).Cur_Theory := Why_Empty;
         Open_Theory (File, E_Rec_Axiom_Module (E),
                      Comment =>
                        "Module for declaring an axiom for the post condition"
                      & " of the recursive function"
                      & """" & Get_Name_String (Chars (E)) & """"
                      & (if Sloc (E) > 0 then
                           " defined at " & Build_Location_String (Sloc (E))
                        else "")
                      & ", created in " & GNAT.Source_Info.Enclosing_Entity);
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
        (Left   =>
           +Compute_Spec (Params, E, Pragma_Postcondition, EW_Pred),
         Right  => +Compute_Contract_Cases_Postcondition (Params, E),
         Domain => EW_Pred);

      if Is_Visible_Dispatching_Operation (E) then
         Dispatch_Pre :=
           Get_Dispatching_Call_Contract (Params, E, Pragma_Precondition);
         Dispatch_Post :=
           Get_Dispatching_Call_Contract (Params, E, Pragma_Postcondition);

         --  Classwide post serves as post if no specific postcondition is
         --  given.

         if Find_Contracts (E, Pragma_Postcondition).Is_Empty
           and then No (Get_Pragma (E, Pragma_Contract_Cases))
         then
            Post := Get_LSP_Contract (Params, E, Pragma_Postcondition);
         end if;

         --  Classwide pre serves as pre if no specific postcondition is given

         if Find_Contracts (E, Pragma_Precondition).Is_Empty then
            Pre := Get_LSP_Contract (Params, E, Pragma_Precondition);
         end if;
      end if;

      if Entity_Body_In_SPARK (E)
        and then Has_Contracts (E, Pragma_Refined_Post)
      then
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
           (Left   => +Compute_Guard_Formula (Logic_Func_Binders, Params),
            Right  => +Compute_Type_Invariants_For_Subprogram
              (E, True, Params),
            Domain => EW_Pred);
         --  Dynamic invariant / type invariants of the inputs

         Dynamic_Prop_Result : constant W_Pred_Id :=
           +New_And_Then_Expr
           (Left   => +Compute_Dynamic_Invariant
              (Expr             => +New_Result_Ident (Why_Type),
               Ty               => Etype (E),
               Only_Var         => False_Term,
               Include_Type_Inv =>
                 Include_Non_Local_Type_Inv_For_Subp (E),
               Params           => Params),
            Right  => +Compute_Type_Invariants_For_Subprogram
              (E, False, Params),
            Domain => EW_Pred);
         --  Dynamic invariant / type invariants of the result

         procedure Emit_Post_Axiom
           (Suffix    : String;
            Id        : W_Identifier_Id;
            Pred_Name : Why_Name_Enum;
            Pre, Post : W_Pred_Id;
            Dispatch  : Boolean := False);
         --  Emit the post_axiom with the given axiom_suffix, name, pre and
         --  post.

         ---------------------
         -- Emit_Post_Axiom --
         ---------------------

         procedure Emit_Post_Axiom
           (Suffix    : String;
            Id        : W_Identifier_Id;
            Pred_Name : Why_Name_Enum;
            Pre, Post : W_Pred_Id;
            Dispatch  : Boolean := False)
         is
            Result_Id     : constant W_Identifier_Id :=
              New_Result_Ident (Why_Type);
            Tag_B         : constant Binder_Array :=
              (if Dispatch then (1 => Tag_Binder)
               else (1 .. 0 => <>));
            Pred_Binders  : constant Binder_Array :=
              Binder_Type'(Ada_Node  => Empty,
                           B_Name    => +Result_Id,
                           B_Ent     => Null_Entity_Name,
                           Mutable   => False,
                           Labels    => <>)
                & Tag_B & Logic_Why_Binders;
            Tag_Comp      : constant W_Pred_Id :=
              (if Is_Tagged_Type (Retysp (Etype (E)))
               and then not Is_Class_Wide_Type (Etype (E))
               then
                 +New_Comparison
                   (Symbol => Why_Eq,
                    Left   => New_Tag_Access
                      (Domain   => EW_Term,
                       Name     => +New_Result_Ident (Why_Type),
                       Ty       => Retysp (Etype (E))),
                    Right  => (if Dispatch and then Has_Controlling_Result (E)
                               then +Tag_Binder.B_Name
                               else +E_Symb (Etype (E), WNE_Tag)),
                    Domain => EW_Pred)
               else True_Pred);
            --  For functions with tagged results, assume the value of the tag
            --  of the result.

            Complete_Post : constant W_Pred_Id :=
              +New_And_Expr
              (Conjuncts =>
                 (1 =>

                    --  If the function is a borrowing traversal function,
                    --  bind the identifier for the pledge of the result. Also
                    --  assume that the pledge holds right after the call.

                    (if Is_Borrowing_Traversal_Function (E)
                     then New_Typed_Binding
                       (Domain  => EW_Pred,
                        Name    => Result_Pledge_Id (E),
                        Def     => New_Pledge_For_Call
                          (E    => E,
                           Args => Compute_Args
                             (E, Logic_Why_Binders)),
                        Context => New_And_Then_Expr
                          (Left   => +Post,
                           Right  => New_Pledge_Call
                             (E            => E,
                              Borrowed_Arg => Transform_Identifier
                                (Expr   => First_Formal (E),
                                 Ent    => First_Formal (E),
                                 Domain => EW_Term,
                                 Params => Params),
                              Brower_Arg   => +Result_Name,
                              Ref_Allowed  => False),
                           Domain => EW_Pred))
                     else +Post),
                  2 => +Dynamic_Prop_Result,
                  3 => +Tag_Comp),
               Domain    => EW_Pred);
            Guarded_Post  : constant W_Pred_Id :=
              (if not Use_Guard_For_Function (E) then Complete_Post
               else New_Conditional
                 (Condition   => New_Call
                      (Domain  => EW_Pred,
                       Name    => E_Symb (E, Pred_Name),
                       Binders => Pred_Binders),
                  Then_Part   => +Complete_Post));
         begin
            if not Is_True_Boolean (+Complete_Post) then
               Emit
                 (File,
                  New_Guarded_Axiom
                    (Ada_Node => Empty,
                     Name     => NID (Short_Name (E) & "__" & Suffix),
                     Binders  => Tag_B & Logic_Why_Binders,
                     Triggers =>
                       New_Triggers
                         (Triggers =>
                              (1 => New_Trigger
                                 (Terms =>
                                    (1 => New_Call
                                         (Domain  => EW_Term,
                                          Name    => Id,
                                          Binders =>
                                            Tag_B & Logic_Why_Binders))))),
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
                           Binders => Tag_B & Logic_Why_Binders),
                        Context  => +Guarded_Post)));
            end if;
         end Emit_Post_Axiom;

      --  Start of processing for Generate_Axiom_For_Post

      begin
         --  Do not emit an axiom for E if it is inlined for proof

         if No (Retrieve_Inline_Annotation (E)) then
            Emit_Post_Axiom (Post_Axiom, Logic_Id, WNE_Func_Guard, Pre, Post);
         end if;

         --  ??? clean up this code duplication for dispatch and refine

         if Is_Visible_Dispatching_Operation (E) then
            pragma Assert (Present (Dispatch_Pre)
                            and then Present (Dispatch_Post));
            Emit_Post_Axiom (Post_Dispatch_Axiom,
                             Dispatch_Logic_Id,
                             WNE_Dispatch_Func_Guard,
                             Dispatch_Pre,
                             Dispatch_Post,
                             Dispatch => True);
         end if;

         if Entity_Body_In_SPARK (E)
           and then Has_Contracts (E, Pragma_Refined_Post)
         then
            pragma Assert (Present (Refined_Post));
            Emit_Post_Axiom (Post_Refine_Axiom,
                             Refine_Logic_Id,
                             WNE_Refined_Func_Guard,
                             Pre,
                             Refined_Post);
         end if;
      end;

      if Is_Recursive (E) then
         Close_Theory (File,
                       Kind           => Axiom_Theory,
                       Defined_Entity => E);
         Why_Sections (File).Cur_Theory := Save_Theory;
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
   end Generate_Axiom_For_Post;

   --------------------------------------------
   -- Generate_Dispatch_Compatibility_Axioms --
   --------------------------------------------

   procedure Generate_Dispatch_Compatibility_Axioms
     (File : W_Section_Id;
      E    : Entity_Id)
   is

      function Same_Globals (E, D : Entity_Id) return Boolean;
      --  @params D a descendant of the dispatching type of E
      --  @return True if E and D access the same set of global variables

      ------------------
      -- Same_Globals --
      ------------------

      function Same_Globals (E, D : Entity_Id) return Boolean is
         use type Flow_Types.Flow_Id_Sets.Set;

         E_Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
         D_Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
         E_Write_Ids : Flow_Types.Flow_Id_Sets.Set;
         D_Write_Ids : Flow_Types.Flow_Id_Sets.Set;
      begin
         --  Collect global variables potentially read and written

         Flow_Utility.Get_Proof_Globals (Subprogram      => E,
                                         Reads           => E_Read_Ids,
                                         Writes          => E_Write_Ids,
                                         Erase_Constants => True);

         Flow_Utility.Get_Proof_Globals (Subprogram      => D,
                                         Reads           => D_Read_Ids,
                                         Writes          => D_Write_Ids,
                                         Erase_Constants => True);

         return E_Read_Ids = D_Read_Ids and then E_Write_Ids = D_Write_Ids;
      end Same_Globals;

      Ty            : constant Entity_Id :=
        SPARK_Util.Subprograms.Find_Dispatching_Type (E);
      Descendants   : Node_Sets.Set := Get_Descendant_Set (Ty);
      Anc_Binders   : constant Binder_Array :=
        (if Ekind (E) = E_Function then
            To_Binder_Array (Compute_Binders (E, EW_Term))
         else Procedure_Logic_Binders (E));
      Dispatch_Args : W_Expr_Array (1 .. Anc_Binders'Length + 1);
      Anc_Id        : constant W_Identifier_Id :=
        (if Ekind (E) = E_Function then
              To_Why_Id (E, Domain => EW_Term, Selector => Dispatch)
         else To_Local (E_Symb (E, WNE_Specific_Post)));
      Anc_Ty        : constant W_Type_Id :=
        (if Ekind (E) = E_Function then Type_Of_Node (E)
         else EW_Bool_Type);

   begin
      --  The arguments of the dispatching call are the binders from
      --  Anc_Binders with a hole at the beginning to store the (specific)
      --  value of the tag.

      for I in Anc_Binders'Range loop
         Dispatch_Args (I + 1) := +Anc_Binders (I).B_Name;
      end loop;

      Descendants.Include (Ty);

      for Descendant of Descendants loop
         Dispatch_Args (1) := +E_Symb (Descendant, WNE_Tag);

         declare
            Descendant_E : constant Entity_Id :=
              Corresponding_Primitive (E, Descendant);
            Desc_Id      : constant W_Identifier_Id :=
              To_Why_Id (Descendant_E, Domain => EW_Term);

            Anc_Call     : constant W_Expr_Id :=
              New_Call (Domain => EW_Term,
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
            --       <E>__dispatch Descendant.tag x1 ... = <Descendant.E> x1 ..

            if Ekind (E) = E_Function then

               --  Do not generate compatibility axioms for volatile functions
               --  as they do not have any assoaciated logic function.
               --  ??? They could maybe be handled like procedures, using a
               --  specific_post predicate.

               if Has_Pragma_Volatile_Function (E) then
                  return;
               end if;

               declare
                  Desc_Ty      : constant W_Type_Id :=
                    Type_Of_Node (Descendant_E);
                  Desc_Binders : constant Binder_Array :=
                    To_Binder_Array (Compute_Binders (Descendant_E, EW_Term));
                  Desc_Args    : W_Expr_Array (1 .. Desc_Binders'Length);
                  Guard        : constant W_Pred_Id :=
                    (if not Use_Guard_For_Function (E) then True_Pred
                     else New_Call
                       (Name   => E_Symb (E, WNE_Dispatch_Func_Guard),
                        Args   => Anc_Call & Dispatch_Args,
                        Typ    => EW_Bool_Type));
                  --  The axiom is protected by the dispatching post predicate
                  --  of E.

               begin
                  pragma Assert (Anc_Binders'First = Desc_Binders'First
                                 and Anc_Binders'Last = Desc_Binders'Last);

                  --  Conversions are needed for controlling parameters

                  for I in Desc_Binders'Range loop
                     Desc_Args (I) :=
                       Insert_Simple_Conversion
                         (Domain         => EW_Term,
                          Expr           => +Anc_Binders (I).B_Name,
                          To             => Get_Typ (Desc_Binders (I).B_Name),
                          Force_No_Slide => True);
                  end loop;

                  Emit
                    (File,
                     New_Guarded_Axiom
                       (Ada_Node => Empty,
                        Name     =>
                          NID (Full_Name (Descendant) & "__" & Compat_Axiom),
                        Binders  => Anc_Binders,
                        Triggers =>
                          New_Triggers
                            (Triggers =>
                                 (1 => New_Trigger
                                    (Terms => (1 => Anc_Call)))),
                        Pre      => Guard,
                        Def      =>
                          +New_Comparison
                          (Symbol => Why_Eq,

                           --  Conversion is needed for controlling result

                           Left   => Insert_Simple_Conversion
                             (Domain         => EW_Term,
                              Expr           => New_Function_Call
                                (Domain => EW_Term,
                                 Subp   => Descendant_E,
                                 Name   => Desc_Id,
                                 Args   => Desc_Args,
                                 Typ    => Desc_Ty),
                              To             => Anc_Ty,
                              Force_No_Slide => True),
                           Right  => Anc_Call,
                           Domain => EW_Term)));
               end;

            --  If E is a procedure, emit:
            --    for all x1 ... [<E>__spec_post Descendant.tag x1 ...].
            --       <E>__spec_post Descendant.tag x1 ... ->
            --           <specific post of Descendant>

            else
               pragma Assert (Ekind (E) = E_Procedure);

               declare
                  New_Binders : Item_Array :=
                    Compute_Raw_Binders (E) &
                    Compute_Binders_For_Effects (E, Compute => False);
                  Old_Binders : Item_Array := New_Binders;
                  Desc_Params : Item_Array :=
                    Compute_Raw_Binders (Descendant_E);
                  Desc_Post   : W_Pred_Id;
                  Params      : Transformation_Params;

               begin
                  Localize_Variable_Parts (New_Binders);
                  Localize_Variable_Parts (Old_Binders, "__old");

                  Ada_Ent_To_Why.Push_Scope (Symbol_Table);

                  --  Controlling parameters may need a conversion. We need a
                  --  binder in non-split form for them. For others, we can use
                  --  the ancestor names directly.

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
                              Local => True,
                              Init  => <>,
                              Main  =>
                                (B_Name   =>
                                     New_Temp_Identifier
                                   (Base_Name => Short_Name (Ada_Node),
                                    Typ       => Typ),
                                 B_Ent    => Null_Entity_Name,
                                 Mutable  => False,
                                 Ada_Node => Ada_Node,
                                 Labels   => <>));

                           Ada_Ent_To_Why.Insert (Symbol_Table,
                                                  Ada_Node,
                                                  Desc_Params (I));
                        else
                           Ada_Ent_To_Why.Insert (Symbol_Table,
                                                  Ada_Node,
                                                  New_Binders (I));
                        end if;
                     end;
                  end loop;

                  --  Store new binders in the Symbol_Table, so that in the
                  --  Post of Descendant, we use local names of parameters and
                  --  effects, instead of the global names.

                  Push_Binders_To_Symbol_Table (New_Binders);

                  --  We will use the map for old to store expressions whose
                  --  values need to be computed in the pre state.

                  Reset_Map_For_Old;

                  Params :=
                    (File        => File,
                     Phase       => Generate_Logic,
                     Gen_Marker  => GM_None,
                     Ref_Allowed => False,
                     Old_Policy  => Use_Map);

                  --  Translate the specific postcondition of Descendant_E

                  if No_Return (Descendant_E) then
                     Desc_Post := False_Pred;
                  else
                     Desc_Post :=
                       +New_And_Expr
                       (Left   =>
                          +Compute_Spec
                            (Params, Descendant_E, Pragma_Postcondition,
                             EW_Pred),
                        Right  =>
                          +Compute_Contract_Cases_Postcondition
                            (Params, Descendant_E),
                        Domain => EW_Pred);

                     if Find_Contracts
                         (Descendant_E, Pragma_Postcondition).Is_Empty
                       and then
                         No (Get_Pragma (Descendant_E, Pragma_Contract_Cases))
                     then
                        Desc_Post :=
                          Get_LSP_Contract
                            (Params, Descendant_E, Pragma_Postcondition);
                     end if;
                  end if;

                  Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

                  Ada_Ent_To_Why.Push_Scope (Symbol_Table);

                  --  Insert bindings for contolling parameters of Descendant_E
                  --  and update entities which should be used for other
                  --  parameters.

                  for I in Desc_Params'Range loop
                     declare
                        Ada_Node : constant Node_Id :=
                          Get_Ada_Node_From_Item (Desc_Params (I));
                        Typ      : constant W_Type_Id :=
                          Get_Why_Type_From_Item (Desc_Params (I));

                     begin
                        if Get_Ada_Node (+Typ) = Descendant then
                           Desc_Post := +New_Typed_Binding
                             (Domain   => EW_Pred,
                              Name     => Desc_Params (I).Main.B_Name,
                              Def      => Insert_Simple_Conversion
                                (Domain         => EW_Term,
                                 Expr           =>
                                   Reconstruct_Item
                                     (New_Binders (I), Ref_Allowed => False),
                                 To             =>
                                   Get_Typ (Desc_Params (I).Main.B_Name),
                                 Force_No_Slide => True),
                              Context  => +Desc_Post);
                           Ada_Ent_To_Why.Insert (Symbol_Table,
                                                  Ada_Node,
                                                  Desc_Params (I));
                        else
                           Ada_Ent_To_Why.Insert (Symbol_Table,
                                                  Ada_Node,
                                                  Old_Binders (I));
                        end if;
                     end;
                  end loop;

                  --  To translate expressions used in old attributes, we need
                  --  to store values in the pre state in the symbol table.

                  Push_Binders_To_Symbol_Table (Old_Binders);

                  --  Inner references to Old should be ignored

                  Params :=
                    (File        => File,
                     Phase       => Generate_Logic,
                     Gen_Marker  => GM_None,
                     Ref_Allowed => False,
                     Old_Policy  => Ignore);

                  --  Insert let bindings for old expressions

                  for C in Map_For_Old.Iterate loop
                     declare
                        Name : constant W_Identifier_Id :=
                          Ada_To_Why_Ident.Element (C);
                        Expr : constant Node_Id := Ada_To_Why_Ident.Key (C);
                        Def  : constant W_Expr_Id :=
                          Insert_Simple_Conversion
                            (Domain         => EW_Term,
                             Expr           =>
                               (if Nkind (Expr) = N_Defining_Identifier then
                                     Transform_Identifier
                                        (Params, Expr, Expr, EW_Term)
                                else Transform_Expr (Expr, EW_Term, Params)),
                             To             => Get_Typ (Name),
                             Force_No_Slide => True);
                     begin
                        Desc_Post := +New_Typed_Binding
                          (Domain   => EW_Pred,
                           Name     => Name,
                           Def      => Def,
                           Context  => +Desc_Post);
                     end;
                  end loop;

                  --  Insert bindings for contolling parameters of Descendant_E

                  for I in Desc_Params'Range loop
                     declare
                        Typ      : constant W_Type_Id :=
                          Get_Why_Type_From_Item (Desc_Params (I));

                     begin
                        if Get_Ada_Node (+Typ) = Descendant then
                           Desc_Post := +New_Typed_Binding
                             (Domain   => EW_Pred,
                              Name     => Desc_Params (I).Main.B_Name,
                              Def      => Insert_Simple_Conversion
                                (Domain         => EW_Term,
                                 Expr           =>
                                   Reconstruct_Item
                                     (Old_Binders (I), Ref_Allowed => False),
                                 To             =>
                                   Get_Typ (Desc_Params (I).Main.B_Name),
                                 Force_No_Slide => True),
                              Context  => +Desc_Post);
                        end if;
                     end;
                  end loop;

                  Reset_Map_For_Old;
                  Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

                  Emit
                    (File,
                     New_Guarded_Axiom
                       (Ada_Node => Empty,
                        Name     =>
                          NID (Full_Name (Descendant) & "__" & Compat_Axiom),
                        Binders  => Anc_Binders,
                        Triggers =>
                          New_Triggers
                            (Triggers =>
                                 (1 => New_Trigger
                                    (Terms => (1 => Anc_Call)))),
                        Pre      => +Anc_Call,
                        Def      => Desc_Post));
               end;
            end if;
         end;
      end loop;
   end Generate_Dispatch_Compatibility_Axioms;

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

      declare
         Use_Result_Name : constant Boolean := Ekind (E) = E_Function;
         --  Store the result identifier in Result_Name
      begin
         if Use_Result_Name then
            Result_Name := New_Result_Ident (Type_Of_Node (E));
            Result_Is_Mutable := False;
         end if;

         if Within_Protected_Type (E) then
            Self_Name :=
              Concurrent_Self_Ident (Containing_Protected_Type (E));
            Self_Is_Mutable := Ekind (E) /= E_Function;
         end if;

         Generate_Subprogram_Program_Fun (File, E);

         Generate_Axiom_For_Post (File, E);

         if Is_Visible_Dispatching_Operation (E)
           and then not Is_Predicate_Function (E)
         then
            Generate_Dispatch_Compatibility_Axioms (File, E);
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

      Close_Theory (File,
                    Kind => Axiom_Theory,
                    Defined_Entity => E);
   end Generate_Subprogram_Completion;

   -------------------------------------
   -- Generate_Subprogram_Program_Fun --
   -------------------------------------

   procedure Generate_Subprogram_Program_Fun
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Func_Binders     : constant Item_Array := Compute_Binders (E, EW_Prog);
      Func_Why_Binders : constant Binder_Array :=
        To_Binder_Array (Func_Binders);
      Params           : Transformation_Params;
      Effects          : W_Effects_Id;
      Pre              : W_Pred_Id;
      Post             : W_Pred_Id;
      Dispatch_Pre     : W_Pred_Id := Why_Empty;
      Dispatch_Post    : W_Pred_Id := Why_Empty;
      Refined_Post     : W_Pred_Id := Why_Empty;
      Prog_Id          : constant W_Identifier_Id :=
        To_Why_Id (E, Domain => EW_Prog, Local => True);
      Why_Type         : W_Type_Id := Why_Empty;

   begin
      Params :=
        (File        => File,
         Phase       => Generate_Logic,
         Gen_Marker  => GM_None,
         Ref_Allowed => True,
         Old_Policy  => As_Old);

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

      if Is_Visible_Dispatching_Operation (E) then
         Dispatch_Pre :=
           Get_Dispatching_Call_Contract (Params, E, Pragma_Precondition);
      end if;

      --  For a procedure annotated with No_Return, the postcondition at call
      --  site should be "False", so that it is known in the caller that the
      --  call does not return.

      if No_Return (E) then
         Post := False_Pred;

         if Is_Visible_Dispatching_Operation (E) then
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
            Right  => +Compute_Contract_Cases_Postcondition (Params, E),
            Domain => EW_Pred);

         if Is_Visible_Dispatching_Operation (E) then
            Dispatch_Post :=
              Get_Dispatching_Call_Contract (Params, E, Pragma_Postcondition);

            if Find_Contracts (E, Pragma_Postcondition).Is_Empty
              and then No (Get_Pragma (E, Pragma_Contract_Cases))
            then
               Post := Get_LSP_Contract (Params, E, Pragma_Postcondition);
            end if;
         end if;

         if Entity_Body_In_SPARK (E)
           and then Has_Contracts (E, Pragma_Refined_Post)
         then
            Refined_Post :=
              Get_Static_Call_Contract (Params, E, Pragma_Refined_Post);
         end if;
      end if;

      if Ekind (E) = E_Function then

         Why_Type := Type_Of_Node (E);

         declare
            Logic_Func_Args     : constant W_Expr_Array :=
              Compute_Args (E, Func_Why_Binders);
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
                 (Expr             => +New_Result_Ident (Why_Type),
                  Ty               => Etype (E),
                  Only_Var         => False_Term,
                  Include_Type_Inv => Include_Non_Local_Type_Inv_For_Subp (E),
                  Params           => Params),
               Right  => +Compute_Type_Invariants_For_Subprogram
                 (E, False, Params),
               Domain => EW_Pred);
            --  Dynamic invariant and type invariant of the result

            Volatile_State  : constant W_Identifier_Id :=
              New_Identifier
                (Domain => EW_Term,
                 Name   => "volatile__effect");

            function Create_Function_Decl
              (Logic_Id  : W_Identifier_Id;
               Prog_Id   : W_Identifier_Id;
               Pred_Name : Why_Name_Enum;
               Pre       : W_Pred_Id;
               Post      : W_Pred_Id;
               Effects   : W_Effects_Id;
               Dispatch  : Boolean := False) return W_Declaration_Id;
            --  create the function declaration with the given Logic_Id,
            --  Prog_Id, Pre and Post.

            --------------------------
            -- Create_Function_Decl --
            --------------------------

            function Create_Function_Decl
              (Logic_Id  : W_Identifier_Id;
               Prog_Id   : W_Identifier_Id;
               Pred_Name : Why_Name_Enum;
               Pre       : W_Pred_Id;
               Post      : W_Pred_Id;
               Effects   : W_Effects_Id;
               Dispatch  : Boolean := False) return W_Declaration_Id
            is
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
                     then New_Typed_Binding
                       (Domain  => EW_Pred,
                        Name    => Result_Pledge_Id (E),
                        Def     => New_Pledge_For_Call
                          (E    => E,
                           Args => Logic_Func_Args),
                        Context => New_And_Then_Expr
                          (Left   => +Post,
                           Right  => New_Pledge_Call
                             (E            => E,
                              Borrowed_Arg => Transform_Identifier
                                (Expr   => First_Formal (E),
                                 Ent    => First_Formal (E),
                                 Domain => EW_Term,
                                 Params => Params),
                              Brower_Arg   => +Result_Name,
                              Ref_Allowed  => False),
                           Domain => EW_Pred))
                     else +Post),
                  Domain => EW_Pred);
               Tag_Arg    : constant W_Expr_Array :=
                 (if Dispatch then (1 => +Tag_Binder.B_Name)
                  else (1 .. 0 => <>));
               Tag_B      : constant Binder_Array :=
                 (if Dispatch then (1 => Tag_Binder)
                  else (1 .. 0 => <>));
               Result_Id  : constant W_Identifier_Id :=
                 New_Result_Ident (Why_Type);
               Pred_Args  : constant W_Expr_Array :=
                 +Result_Id & Tag_Arg & Logic_Func_Args;

            begin

               --  A volatile function has an effect, and should not have the
               --  special postcondition which says it's result is equal to the
               --  logic function.

               if not Has_Pragma_Volatile_Function (E) then
                  Param_Post :=
                    +New_And_Expr
                    (Domain    => EW_Pred,
                     Conjuncts =>
                       (1 => New_Call
                         (Name   => Why_Eq,
                          Domain => EW_Pred,
                          Typ    => EW_Bool_Type,
                          Args   => (+Result_Id,
                                     New_Call
                                       (Domain => EW_Term,
                                        Name   => Logic_Id,
                                        Args   => Tag_Arg & Logic_Func_Args))),
                        2 => (if Use_Guard_For_Function (E) then
                                 New_Call
                                   (Domain => EW_Term,
                                    Name   => E_Symb (E, Pred_Name),
                                    Args   => Pred_Args)
                              else +True_Pred),
                        3 => +Param_Post));
               end if;

               return New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Id,
                  Binders     => Tag_B & Func_Why_Binders,
                  Return_Type => Type_Of_Node (E),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => Param_Post);
            end Create_Function_Decl;

         begin
            --  If E is an expression function, add its body to its
            --  postcondition.

            if Is_Expression_Function_Or_Completion (E)
              and then Entity_Body_Compatible_With_SPARK (E)
              and then not Has_Pragma_Volatile_Function (E)
            then
               declare
                  Domain    : constant EW_Domain :=
                    (if Is_Standard_Boolean_Type (Etype (E)) then EW_Pred
                     else EW_Term);
                  Expr_Fun_N : constant Node_Id :=
                    Get_Expression_Function (E);
                  Expr_Body : constant W_Expr_Id :=
                    Transform_Expr (Expression (Expr_Fun_N),
                                    Expected_Type => Why_Type,
                                    Domain        => Domain,
                                    Params        => Params);
                  Res_Expr  : constant W_Expr_Id :=
                    +New_Result_Ident (Why_Type);
                  Eq_Expr   : constant W_Pred_Id :=
                    (if Is_Standard_Boolean_Type (Etype (E))
                     then New_Equal_Bool (+Res_Expr, +Expr_Body)
                     else New_Call (Name => Why_Eq,
                                    Args => (Res_Expr, Expr_Body),
                                    Typ  => EW_Bool_Type));
               begin
                  if Entity_Body_In_SPARK (E)
                    and then Has_Contracts (E, Pragma_Refined_Post)
                  then
                     Refined_Post :=
                       +New_And_Expr (+Eq_Expr, +Refined_Post, EW_Pred);
                  else
                     Post := +New_And_Expr (+Eq_Expr, +Post, EW_Pred);
                  end if;
               end;
            end if;

            --  For a volatile function that is not protected, we need to
            --  generate a dummy effect. Protected functions are OK, they
            --  already have their own state (the protected object).

            if Has_Pragma_Volatile_Function (E) then
               Effects_Append_To_Writes (Effects, Volatile_State);

               Emit
                 (File,
                  New_Global_Ref_Declaration
                    (Ada_Node => E,
                     Labels   => Symbol_Sets.Empty_Set,
                     Location => No_Location,
                     Name     => Volatile_State,
                     Ref_Type => EW_Private_Type));
            end if;

            Emit
              (File,
               Create_Function_Decl (Logic_Id  => Logic_Id,
                                     Prog_Id   => Prog_Id,
                                     Pred_Name => WNE_Func_Guard,
                                     Pre       => Pre,
                                     Post      => Post,
                                     Effects   => Effects));

            if Is_Visible_Dispatching_Operation (E) then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name         => NID (To_String (WNE_Dispatch_Module)),
                     Declarations =>
                       (1 => Create_Function_Decl
                            (Logic_Id  => Dispatch_Logic_Id,
                             Prog_Id   => Prog_Id,
                             Pred_Name => WNE_Dispatch_Func_Guard,
                             Pre       => Dispatch_Pre,
                             Post      => Dispatch_Post,
                             Effects   => Effects,
                             Dispatch  => True))));
            end if;

            if Entity_Body_In_SPARK (E)
              and then Has_Contracts (E, Pragma_Refined_Post)
            then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => Create_Function_Decl
                            (Logic_Id  => Refine_Logic_Id,
                             Prog_Id   => Prog_Id,
                             Pred_Name => WNE_Refined_Func_Guard,
                             Pre       => Pre,
                             Post      => Refined_Post,
                             Effects   => Effects))));
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
            Post := +New_And_Expr (Left   => +Post,
                                   Right  => +Dynamic_Prop_Effects,
                                   Domain => EW_Pred);

            --  If a procedure might not return, its postcondition is only
            --  valid in those cases where it returns:
            --
            --    if no__return = false then post

            if Has_Might_Not_Return_Annotation (E) then
               Post := New_Conditional
                 (Condition =>
                    New_Comparison
                      (Symbol => M_Integer.Bool_Eq,
                       Left   => New_Deref (Right => +M_Main.No_Return,
                                            Typ   => EW_Bool_Type),
                       Right  => +False_Term,
                       Domain => EW_Pred),
                  Then_Part => +Post);
            end if;

            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Id,
                  Binders     => Func_Why_Binders,
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Unit_Type,
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => Post));

            if Is_Visible_Dispatching_Operation (E) then

               --  For dispatching procedure, declare a new predicate symbol
               --  standing for the specific postcondition which applies to the
               --  dispatching tag and add it to the dispatching postcondition
               --  of E.

               declare
                  Spec_Post_Id   : constant W_Identifier_Id :=
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
                     Logic_Binders   : constant Item_Array :=
                       Compute_Raw_Binders (E) &
                       Compute_Binders_For_Effects (E, Compute => False);
                     --  Binders for parameters and effects of E

                     Dispatch_Param  : constant Entity_Id :=
                       Find_Dispatching_Parameter (E);
                     Dispatch_Binder : constant Item_Type :=
                       Ada_Ent_To_Why.Element
                         (Symbol_Table, Dispatch_Param);
                     Dispatch_Typ    : constant W_Type_Id :=
                       Get_Why_Type_From_Item (Dispatch_Binder);
                     Tag_Arg         : constant W_Expr_Id :=
                       (case Dispatch_Binder.Kind is
                           when Regular =>
                              New_Tag_Access
                          (Domain => EW_Term,
                           Name   =>
                             (if Dispatch_Binder.Main.Mutable then
                                   New_Deref
                                (Right => Dispatch_Binder.Main.B_Name,
                                 Typ   => Dispatch_Typ)
                              else +Dispatch_Binder.Main.B_Name),
                           Ty     =>
                              Get_Ada_Node (+Dispatch_Typ)),
                           when DRecord => +Dispatch_Binder.Tag.Id,
                           when others  => raise Program_Error);
                     --  Tag used for dispatching in calls to E

                     Logic_Args      : W_Expr_Array :=
                       Tag_Arg &
                       Get_Args_From_Binders
                       (To_Binder_Array
                          (Logic_Binders, Keep_Local => True) &
                          To_Binder_Array
                          (Logic_Binders, Keep_Local => False),
                        Ref_Allowed => True);
                     --  Arguments of the predicate function for E's
                     --  specific post:
                     --    - the specific tag
                     --    - values of parameters and binders after the call
                     --    - old values of mutable parts of binders

                     First_Old       : constant Natural :=
                       2 + Item_Array_Length
                         (Logic_Binders, Keep_Local => True);

                  begin
                     --  Insert calls to old on expressions for the old
                     --  values of parameters and global variables.

                     for I in First_Old .. Logic_Args'Last loop
                        Logic_Args (I) := New_Old (Logic_Args (I), EW_Term);
                     end loop;

                     Spec_Post_Call := New_Call
                       (Name   => Spec_Post_Id,
                        Args   => Logic_Args,
                        Typ    => EW_Bool_Type);
                  end;

                  Emit
                    (File,
                     New_Namespace_Declaration
                       (Name         => NID (To_String (WNE_Dispatch_Module)),
                        Declarations =>
                          (1 => New_Function_Decl
                               (Domain      => EW_Pred,
                                Name        => Spec_Post_Id,
                                Binders     =>
                                  Tag_Binder & Procedure_Logic_Binders (E),
                                Location    => No_Location,
                                Labels      => Symbol_Sets.Empty_Set,
                                Return_Type => EW_Bool_Type),
                           2 => New_Function_Decl
                               (Domain      => EW_Prog,
                                Name        => Prog_Id,
                                Binders     => Func_Why_Binders,
                                Location    => No_Location,
                                Labels      => Symbol_Sets.Empty_Set,
                                Return_Type => EW_Unit_Type,
                                Effects     => Effects,
                                Pre         => Dispatch_Pre,
                                Post        => +New_And_Expr
                                  (Conjuncts =>
                                       (1 => +Dispatch_Post,
                                        2 => +Dynamic_Prop_Effects,
                                        3 => +Spec_Post_Call),
                                   Domain => EW_Pred)))));
               end;
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
                    (Name         => NID (To_String (WNE_No_Return_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Location    => No_Location,
                             Labels      => Symbol_Sets.Empty_Set,
                             Return_Type => EW_Unit_Type,
                             Effects     => Effects,
                             Pre         => False_Pred,
                             Post        => False_Pred))));
            end if;

            if Entity_Body_In_SPARK (E)
              and then Has_Contracts (E, Pragma_Refined_Post)
            then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name         => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Location    => No_Location,
                             Labels      => Symbol_Sets.Empty_Set,
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
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => EW_Unit_Type,
                  Pre         => Inv_Checks,
                  Post        => Inv_Checks));
         end if;
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
   end Generate_Subprogram_Program_Fun;

   --------------------
   -- Get_Logic_Args --
   --------------------

   function Get_Logic_Args
     (E           : Entity_Id;
      Ref_Allowed : Boolean) return W_Expr_Array
   is
      Effect_Binders : constant Item_Array :=
        Compute_Binders_For_Effects (E, Compute => False);
      Logic_Binders  : constant Binder_Array :=
        To_Binder_Array (Effect_Binders);

   begin
      return Get_Args_From_Binders (Logic_Binders, Ref_Allowed);
   end Get_Logic_Args;

   ----------------------
   -- Insert_Exception --
   ----------------------

   procedure Insert_Exception (Exc : W_Name_Id) is
   begin
      Subprogram_Exceptions.Insert (+Exc);
   end Insert_Exception;

   -----------------------------
   -- Procedure_Logic_Binders --
   -----------------------------

   function Procedure_Logic_Binders (E : Entity_Id) return Binder_Array is
      Logic_Binders     : constant Item_Array :=
        Compute_Raw_Binders (E) &
        Compute_Binders_For_Effects (E, Compute => False);
      New_Binders       : Item_Array := Logic_Binders;
      Old_Binders       : Item_Array := Logic_Binders;
   begin
      Localize_Variable_Parts (New_Binders);
      Localize_Variable_Parts (Old_Binders, "__old");
      return To_Binder_Array (New_Binders, Keep_Local => True) &
        To_Binder_Array (Old_Binders, Keep_Local => False);
   end Procedure_Logic_Binders;

   ----------------------------------------
   -- Translate_Expression_Function_Body --
   ----------------------------------------

   procedure Translate_Expression_Function_Body
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Expr_Fun_N         : constant Node_Id := Get_Expression_Function (E);

      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Flat_Binders       : constant Binder_Array :=
        To_Binder_Array (Logic_Func_Binders);

      Use_Refined_Post : constant Boolean :=
        Entity_Body_In_SPARK (E)
        and then Has_Contracts (E, Pragma_Refined_Post);

      Logic_Id           : constant W_Identifier_Id :=
        To_Why_Id (E, Domain => EW_Term, Local => False,
                   Selector => (if Use_Refined_Post
                                then Refine
                                else Why.Inter.Standard));
      Pred_Name          : constant Why_Name_Enum :=
        (if Use_Refined_Post
         then WNE_Refined_Func_Guard
         else WNE_Func_Guard);
      Result_Id          : constant W_Identifier_Id :=
         New_Result_Ident (Type_Of_Node (E));
      Pred_Binders       : constant Binder_Array :=
         Binder_Type'(Ada_Node  => Empty,
                      B_Name    => +Result_Id,
                      B_Ent     => Null_Entity_Name,
                      Mutable   => False,
                      Labels    => <>)
           & Flat_Binders;
      Func_Guard         : constant W_Pred_Id :=
        (if not Use_Guard_For_Function (E)
         or else not Is_Recursive (E)
         then True_Pred
         else +New_Typed_Binding
           (Domain   => EW_Pred,
            Name     => Result_Id,
            Def      => New_Call (Domain  => EW_Pred,
                                  Name    => Logic_Id,
                                  Binders => Flat_Binders,
                                  Typ     => EW_Bool_Type),
            Context  => +New_Call (Domain  => EW_Pred,
                                   Name    => E_Symb (E, Pred_Name),
                                   Binders => Pred_Binders,
                                   Typ     => EW_Bool_Type)));

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

      --  Store an appropriate value for the result identifier in Result_Name.

      Result_Name := New_Result_Ident (Type_Of_Node (E));
      Result_Is_Mutable := False;

      if Within_Protected_Type (E) then
         Self_Name :=
           Concurrent_Self_Ident (Containing_Protected_Type (E));
         Self_Is_Mutable := False;
      end if;

      Generate_Subprogram_Program_Fun (File, E);

      Generate_Axiom_For_Post (File, E);

      if Is_Visible_Dispatching_Operation (E) then
         Generate_Dispatch_Compatibility_Axioms (File, E);
      end if;

      --  If the entity's body is not in SPARK,
      --  if it is inlined for proof
      --  if it is recursive and may not terminate
      --  or if the function does not return, do not generate axiom.

      --  We do not generate axioms for body of expression function which do
      --  not terminate because these axioms could be unsound.
      --  If the function does not terminate but is not recursive, then it
      --  must be because either it is itself not in part with SPARK_Mode On or
      --  because it calls a non-terminating function. These reasons should not
      --  make the axiom unsound.
      --  If the function is recursive but has a terminating annotation, then
      --  the axiom should not be incorrect, so that is not a problem that it
      --  is used to prove itself.

      if not Entity_Body_Compatible_With_SPARK (E)
        or else Present (Retrieve_Inline_Annotation (E))
        or else Has_Pragma_Volatile_Function (E)
        or else (Is_Recursive (E) and then Is_Potentially_Nonreturning (E))
      then
         Close_Theory (File,
                       Kind => Definition_Theory);
         Result_Name := Why_Empty;
         Result_Is_Mutable := False;
         return;
      end if;

      Params :=
        (File        => File,
         Phase       => Generate_Logic,
         Gen_Marker  => GM_None,
         Ref_Allowed => False,
         Old_Policy  => Ignore);

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Push_Binders_To_Symbol_Table (Logic_Func_Binders);

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
               Pre      => Func_Guard,
               Def      => +Transform_Expr (Expression (Expr_Fun_N),
                                            EW_Pred,
                                            Params)));

      else
         pragma Assert (not Has_Scalar_Type (Etype (E))
                        or else Use_Split_Form_For_Type (Etype (E)));

         declare
            Equ_Ty  : constant W_Type_Id := Type_Of_Node (E);
            Guard   : constant W_Pred_Id :=
              +New_And_Then_Expr
              (Left   => +Compute_Guard_Formula
                 (Logic_Func_Binders, Params),
               Right  => +Func_Guard,
               Domain => EW_Pred);
         begin
            Emit
              (File,
               New_Defining_Axiom
                 (Ada_Node    => E,
                  Name        => Logic_Id,
                  Binders     => Flat_Binders,
                  Pre         => Guard,
                  Def         => +Transform_Expr
                    (Expression (Expr_Fun_N),
                     Expected_Type => Equ_Ty,
                     Domain        => EW_Term,
                     Params        => Params)));
         end;
      end if;

      if Is_Borrowing_Traversal_Function (E) then
         declare
            Guard       : constant W_Pred_Id :=
              +New_And_Then_Expr
              (Left   => +Compute_Guard_Formula
                 (Logic_Func_Binders, Params),
               Right  => +Func_Guard,
               Domain => EW_Pred);
            Borrowed_Id : W_Identifier_Id;
            Brower_Id   : W_Identifier_Id;
            Def         : constant W_Term_Id := New_Pledge_Def_From_Expression
              (Brower      => E,
               Borrowed_Id => Borrowed_Id,
               Brower_Id   => Brower_Id,
               Path        => Expression (Expr_Fun_N));
         begin
            Emit
              (File,
               New_Guarded_Axiom
                 (Ada_Node => E,
                  Name     => NID (Short_Name (E) & "__" & Pledge_Axiom),
                  Binders  => Flat_Binders,
                  Pre      => Guard,
                  Def      => New_Pledge_Def
                    (E           => E,
                     Name        => +New_Pledge_For_Call
                       (E    => E,
                        Args => Get_Args_From_Binders
                          (Flat_Binders, Ref_Allowed => False)),
                     Borrowed_Id => Borrowed_Id,
                     Brower_Id   => Brower_Id,
                     Def         => Def)));
         end;
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      if Within_Protected_Type (E) then
         Self_Name := Why_Empty;
         Self_Is_Mutable := False;
      end if;

      Result_Name := Why_Empty;
      Result_Is_Mutable := False;

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

      --  No logic function is created for volatile functions. The function's
      --  effects are modelled by an effect on the program function.

      if Ekind (E) = E_Function
        and then not Has_Pragma_Volatile_Function (E)
      then
         Why_Type := Type_Of_Node (E);

         declare
            Logic_Why_Binders : constant Binder_Array :=
              To_Binder_Array (Logic_Func_Binders);
            Logic_Id          : constant W_Identifier_Id :=
              To_Why_Id (E, Domain => EW_Term, Local => True);
            Result_Id         : constant W_Identifier_Id :=
              New_Temp_Identifier (Base_Name => "result", Typ => Why_Type);
            Pred_Binders      : constant Binder_Array :=
              Binder_Type'(Ada_Node  => Empty,
                           B_Name    => +Result_Id,
                           B_Ent     => Null_Entity_Name,
                           Mutable   => False,
                           Labels    => <>)
                & Logic_Why_Binders;
            Pred_Id           : constant W_Identifier_Id :=
              New_Identifier
                (Domain => EW_Pred,
                 Symb   => NID (Short_Name (E) & "__" & Function_Guard),
                 Typ    => EW_Bool_Type);
            Params            : constant Transformation_Params :=
              (File        => File,
               Phase       => Generate_Logic,
               Gen_Marker  => GM_None,
               Ref_Allowed => False,
               Old_Policy  => Ignore);
            Def               : constant W_Expr_Id :=
              Compute_Inlined_Expr
                (E, Logic_Func_Binders, Why_Type, Params);
         begin
            --  Generate a logic function

            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => Logic_Id,
                  Binders     => Logic_Why_Binders,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Def         => Def,
                  Return_Type => Why_Type));

            --  Generate the guard for the postcondition of the function

            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Pred,
                  Name        => Pred_Id,
                  Binders     => Pred_Binders,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => EW_Bool_Type));

            --  Generate logic functions and guards for dispatching and
            --  refined versions of the function.

            if Is_Visible_Dispatching_Operation (E) then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name         => NID (To_String (WNE_Dispatch_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Pterm,
                             Name        => Logic_Id,
                             Binders     => Tag_Binder & Logic_Why_Binders,
                             Location    => No_Location,
                             Labels      => Symbol_Sets.Empty_Set,
                             Return_Type => Why_Type),
                        2 => New_Function_Decl
                            (Domain      => EW_Pred,
                             Name        => Pred_Id,
                             Binders     =>
                               Pred_Binders (1) & Tag_Binder &
                               Pred_Binders (2 .. Pred_Binders'Length),
                             Labels      => Symbol_Sets.Empty_Set,
                             Location    => No_Location,
                             Return_Type => EW_Bool_Type))));
            end if;

            if Entity_Body_In_SPARK (E)
              and then Has_Contracts (E, Pragma_Refined_Post)
            then
               Emit
                 (File,
                  New_Namespace_Declaration
                    (Name         => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Pterm,
                             Name        => Logic_Id,
                             Binders     => Logic_Why_Binders,
                             Labels      => Symbol_Sets.Empty_Set,
                             Location    => No_Location,
                             Return_Type => Why_Type),
                        2 => New_Function_Decl
                            (Domain      => EW_Pred,
                             Name        => Pred_Id,
                             Binders     => Pred_Binders,
                             Labels      => Symbol_Sets.Empty_Set,
                             Location    => No_Location,
                             Return_Type => EW_Bool_Type))));
            end if;

            --  Generate a function return the pledge of a traversal function.
            --  We don't need anything specific for dispatching functions as
            --  tagged types cannot be deep.

            if Is_Borrowing_Traversal_Function (E) then
               Declare_Pledge_Function (File, E, Logic_Why_Binders);
            end if;
         end;
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
