------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
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

with Checked_Types;             use Checked_Types;
with Common_Containers;         use Common_Containers;
with Flow_Types;                use Flow_Types;
with GNATCOLL.Symbols;          use GNATCOLL.Symbols;
with Gnat2Why.Util;             use Gnat2Why.Util;
with SPARK_Atree;               use SPARK_Atree;
with SPARK_Atree.Entities;      use SPARK_Atree.Entities;
with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;
with Types;                     use Types;
with Why.Conversions;           use Why.Conversions;
with Why.Gen.Binders;           use Why.Gen.Binders;
with Why.Gen.Expr;              use Why.Gen.Expr;
with Why.Gen.Terms;             use Why.Gen.Terms;
with Why.Ids;                   use Why.Ids;
with Why.Sinfo;                 use Why.Sinfo;

package Gnat2Why.Subprograms is

   --  This package deals with the translation of GNAT functions and
   --  statements to Why declarations.

   --  Subprograms are translated to Why programs with pre- and postconditions
   --  (contracts). These assertions have to be self-guarded to enforce the
   --  same semantics as if these assertions were executed. For example, an
   --  array access like
   --     X (I) = 0
   --  must be protected by a condition:
   --     I in X'First .. X'Last and then X (I) = 0.
   --  This is checked by generating, for all assertions, equivalent programs
   --  that must be runtime error free.
   --
   --  Subprogram contracts may contain calls to expression functions. As we
   --  have translated these functions to Why logic functions, nothing special
   --  needs to be done.
   --
   --  For a Subprogram *declaration*, we generate a Why parameter
   --  declaration, with the full argument list and the translation of the
   --  contract, if any.
   --
   --  For a Subprogram *body*, we generate a Why program function *without*
   --  parameters (expect a unit parameter); all Ada parameters and local
   --  variables of subprograms, as well as local subprograms, are put at the
   --  global toplevel in Why.
   --
   --  More specific documentation is given at the beginning of each function
   --  in this package.

   Current_Subp : Entity_Id := Empty;

   function Compute_Outputs_With_Allocated_Parts
     (E : Callable_Kind_Id)
      return Entity_Sets.Set
   with Pre => Ekind (E) /= E_Function;
   --  Compute the set of outputs with allocated parts for a procedure or
   --  entry E, which consist in output parameters and globals of mode Output.

   procedure Generate_VCs_For_Subprogram (E : Callable_Kind_Id);
   --  Generate Why code from which Why VC generator will generate all VCs
   --  related to the absence of run-time errors in E.

   procedure Generate_VCs_For_Subprogram
     (E                      : Callable_Kind_Id;
      Th                     : Theory_UC;
      Prog_Name              : W_Identifier_Id;
      Is_Access_Subp_Wrapper : Boolean := False);
   --  Same as above except that it does not create its own theory but uses an
   --  existing one. Is_Access_Subp_Wrapper should be True for wrappers of
   --  access-to-subprogram types so a feasibility check is generated on
   --  functions.

   procedure Generate_VCs_For_Package_Elaboration (E : E_Package_Id);
   --  Generate Why code from which Why VC generator will generate all VCs
   --  related to the Initial_Condition of E and the absence of run-time
   --  errors in the declarations and body statements of E.

   procedure Generate_VCs_For_LSP (E : Subprogram_Kind_Id);
   --  Generate Why code from which Why VC generator will generate all VCs
   --  related to the verification of LSP for dispatching subprogram E.

   procedure Generate_VCs_For_Task_Type (E : E_Task_Type_Id);
   --  @param File the file and section in which the VCs should be generated
   --  @param E the task entity to be translated

   procedure Generate_VCs_For_Protected_Type (E : E_Protected_Type_Id);

   procedure Translate_Subprogram_Spec (E : Callable_Kind_Id) with
     Pre => Ekind (E) in E_Entry | E_Function | E_Procedure;
   --  Generate a Why logic declaration that corresponds to an Ada subprogram

   function Get_Logic_Args
     (E           : Entity_Id;
      Ref_Allowed : Boolean;
      More_Reads  : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return W_Expr_Array;
   --  Get the expressions to use in a function call for an additional logic
   --  binders.
   --  More_Reads is a set of globals that should be considered as read by
   --  the subprogram in addition to its actual inputs. It is used to handle
   --  calls with higher order specialization.

   procedure Generate_Subprogram_Completion (E : Callable_Kind_Id) with
     Pre => Ekind (E) in E_Entry | E_Function | E_Procedure;
   --  Generate a Why program declaration and potentially a defining axiom for
   --  an Ada subprogram.

   procedure Translate_Expression_Function_Body (E : E_Function_Id)
   with Pre => Is_Expression_Function_Or_Completion (E);
   --  If subprogram E's body is in SPARK, generate a Why axiom that, given a
   --  function F with expression E, states that: "for all <args> => F(<args>)
   --  = E". Also generate a program function for E.

   function Compute_Subprogram_Parameters
     (E          : Callable_Kind_Id;
      Domain     : EW_Domain;
      More_Reads : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return Item_Array;
   --  Return Why binders for the parameters of subprogram E.
   --  More_Reads is a set of globals that should be considered as read by
   --  the subprogram in addition to its actual inputs. It is used to handle
   --  calls with higher order specialization.
   --  If Domain is EW_Term also generates binders for E's read effects.

   procedure Update_Symbol_Table_For_Inherited_Contracts
     (E : Callable_Kind_Id);
   --  The inherited precondition and postcondition for E is expressed wrt the
   --  overridden's subprogram parameters. Make sure these are mapped in the
   --  symbol table to the current subprogram'ms parameters. The result symbol
   --  is always mapped to the current result.

   procedure Insert_Exception (Exc : W_Name_Id);
   --  Add a new exception that should be declared before the unit

   function Need_Self_Binder (E : Callable_Kind_Id) return Boolean;
   --  Return True on entries and subprograms located within a protected object

private

   procedure Declare_Logic_Functions
     (Th                    : Theory_UC;
      Dispatch_Th           : Theory_UC := Empty_Theory;
      E                     : Callable_Kind_Id;
      Spec_Binders          : Binder_Array := Binder_Array'(1 .. 0 => <>);
      Specialization_Module : Symbol := No_Symbol;
      More_Reads            : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set);
   --  @param Th theory in which the logic functions should be declared
   --  @param Dispatch_Th if E is a dispatching operation, specific theory for
   --    its dispatch functions.
   --  @param E entry or subprogram or subprogram type entity
   --  @param Spec_Binders special binders to be used in addition to normal
   --    binders for the subprogram.
   --  @param Specialization_Module name of the specialization module in
   --    which the symbols are generated. It is empty if we are not generating
   --    code for a subprogram annotated with higher order specialization.
   --  @param More_Reads is a set of globals that should be considered as read
   --  by the subprogram in addition to its actual inputs. It is used to handle
   --  calls with higher order specialization.
   --  Declare a logic function and a guard predicate for E. If needed,
   --  generate a namespace for the dispatching/refined variants.

   procedure Generate_Axiom_For_Lemma
     (E                     : E_Procedure_Id;
      Specialization_Module : Symbol := No_Symbol;
      More_Reads            : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
   with Pre => Has_Automatic_Instantiation_Annotation (E);
   --  @param E a lemma procedure
   --  @param Specialization_Module name of the specialization module in
   --    which the symbols are generated. It is empty if we are not generating
   --    code for a subprogram annotated with higher order specialization.
   --  @param More_Reads is a set of globals that should be considered as read
   --  by the subprogram in addition to its actual inputs. It is used to handle
   --  calls with higher order specialization.
   --  Emit an axiom for the postcondition of E.

   procedure Generate_Subprogram_Program_Fun
     (Th                     : Theory_UC;
      Dispatch_Th            : Theory_UC := Empty_Theory;
      E                      : Callable_Kind_Id;
      Prog_Id                : W_Identifier_Id;
      Spec_Binders           : Binder_Array := Binder_Array'(1 .. 0 => <>);
      Is_Access_Subp_Wrapper : Boolean := False;
      Specialization_Module  : Symbol := No_Symbol;
      More_Reads             : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set);
   --  @param Th theory in which the program functions should be declared
   --  @param Dispatch_Th if E is a dispatching operation, specific theory for
   --    its dispatch functions.
   --  @param E entry or subprogram or subprogram type entity
   --  @param Prog_Id name of the program function
   --  @param Spec_Binders special binders to be used in addition to normal
   --    binders for the subprogram.
   --  @param Is_Access_Subp_Wrapper true if we are generating a function for
   --    an access-to-subprogram type through its wrapper.
   --  @param Specialization_Module name of the specialization module in
   --    which the symbols are generated. It is empty if we are not generating
   --    code for a subprogram annotated with higher order specialization.
   --  @param More_Reads is a set of globals that should be considered as read
   --  by the subprogram in addition to its actual inputs. It is used to handle
   --  calls with higher order specialization.
   --  Generate a why program function for E. Also generate a program function
   --  that performs invariant checks for global / parameters of E. It should
   --  be called before calling E's program function.

   procedure Generate_Axiom_For_Post
     (Th                     : Theory_UC;
      Dispatch_Th            : Theory_UC := Empty_Theory;
      E                      : Callable_Kind_Id;
      Spec_Binders           : Binder_Array := (1 .. 0 => <>);
      Spec_Guard             : W_Pred_Id := True_Pred;
      Is_Access_Subp_Wrapper : Boolean := False;
      Specialization_Module  : Symbol := No_Symbol;
      More_Reads             : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
   with Pre => Is_Access_Subp_Wrapper
     or else Ekind (E) = E_Subprogram_Type
     or else (Is_True_Boolean (+Spec_Guard) and Spec_Binders'Length = 0);
   --  @param Th theory in which the axioms should be generated
   --  @param Dispatch_Th if E is a dispatching operation, specific theory for
   --    its dispatch axioms.
   --  @param E entry or subprogram or subprogram type entity
   --  @param Ent_For_Name entity to use to get the name of the logic Id for
   --    E. It maybe different from E for subprogram types for which the
   --    frontend introduces a wrapper if they have contracts.
   --  @param Spec_Binders specialized binders to be used in addition to normal
   --    binders for the subprogram.
   --  @param Spec_Guard specialized predicate which should be equivalent to
   --    the post of E. In the general case, this predicate is just True and
   --    the axiom states that the post always holds.
   --  @param Is_Access_Subp_Wrapper true if we are generating axioms for
   --    an access-to-subprogram type through its wrapper.
   --  @param Specialization_Module name of the specialization module in
   --    which the symbols are generated. It is empty if we are not generating
   --    code for a function annotated with higher order specialization.
   --  @param More_Reads is a set of globals that should be considered as read
   --  by the subprogram in addition to its actual inputs. It is used to handle
   --  calls with higher order specialization.
   --  If E is a function, generate an axiom stating that postcondition of E
   --  is equivalent to Spec_Guard.

   function Compute_Dynamic_Property_For_Inputs
     (E              : Unit_Kind_Id;
      Params         : Transformation_Params;
      Pred_Fun_Param : Entity_Id := Empty)
      return W_Prog_Id
   with
       Pre => Ekind (E) in E_Procedure |
                           E_Function  |
                           E_Package   |
                           E_Task_Type |
                           E_Entry     |
                           E_Subprogram_Type;
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

   function Compute_Binders_For_Effects
     (E          : Callable_Kind_Id;
      More_Reads : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set)
      return Item_Array;
   --  @param E an enity for a subprogram
   --  @param More_Reads Set of globals that should be considered as read by
   --     the subprogram in addition to its actual inputs. It is used to handle
   --     calls with higher order specialization.
   --  @result an array containing an Item per global variable read / written
   --          by E.

   function Compute_Call_Effects
     (Params : Transformation_Params;
      E      : Callable_Kind_Id)
      return W_Prog_Id;
   --  Generate a Why3 program simulating the effects of a call of the
   --  subprogram.

   function Same_Globals (Subp_1, Subp_2 : Callable_Kind_Id) return Boolean;
   --  Return True if Subp_1 and Sup2 access the same set of global variables

   function Compute_Contract_Cases_Postcondition
     (Params : Transformation_Params;
      E      : Callable_Kind_Id)
      return W_Pred_Id;
   --  Returns the postcondition corresponding to the Contract_Cases pragma for
   --  subprogram E (if any), to be used in the postcondition of the program
   --  function.

   procedure Collect_Old_For_Subprogram
     (E                 :        Callable_Kind_Id;
      Old_Parts         : in out Node_Sets.Set;
      Exclude_Classwide :        Boolean := True;
      Exclude_CC        :        Boolean := False);
   --  Collects the set of old attributes occuring in the postcondition of E.
   --  If Exclude_CC is False, also collects old attributes and guards from
   --  the contract case if any.
   --  If Exclude_Classwide is False, defaults to the classwide postcondition
   --  if no contract cases/specific postconditions are present.

end Gnat2Why.Subprograms;
