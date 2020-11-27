------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
--                                                                          --
--                                 S p e c                                  --
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

with Common_Containers;      use Common_Containers;
with Gnat2Why.Util;          use Gnat2Why.Util;
with SPARK_Atree;            use SPARK_Atree;
with SPARK_Atree.Entities;   use SPARK_Atree.Entities;
with Types;                  use Types;
with Why.Conversions;        use Why.Conversions;
with Why.Gen.Binders;        use Why.Gen.Binders;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Preds;          use Why.Gen.Preds;
with Why.Ids;                use Why.Ids;
with Why.Sinfo;              use Why.Sinfo;

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

   function Compute_Deep_Outputs (E : Entity_Id) return Entity_Sets.Set
     with Pre => Ekind (E) in E_Entry | E_Procedure | E_Subprogram_Type;
   --  Compute the set of deep outputs for a procedure or entry E, which
   --  consist in output parameters and globals of mode Output.

   procedure Generate_VCs_For_Subprogram (E : Entity_Id)
     with Pre =>
       Ekind (E) in E_Entry | E_Function | E_Procedure | E_Subprogram_Type;
   --  Generate Why code from which Why VC generator will generate all VCs
   --  related to the absence of run-time errors in E.

   procedure Generate_VCs_For_Package_Elaboration (E : Entity_Id) with
     Pre => Ekind (E) = E_Package;
   --  Generate Why code from which Why VC generator will generate all VCs
   --  related to the Initial_Condition of E and the absence of run-time
   --  errors in the declarations and body statements of E.

   procedure Generate_VCs_For_LSP (E : Entity_Id) with
     Pre => Ekind (E) in E_Function | E_Procedure;
   --  Generate Why code from which Why VC generator will generate all VCs
   --  related to the verification of LSP for dispatching subprogram E.

   procedure Generate_VCs_For_Task_Type (E : Entity_Id)
   with Pre => Ekind (E) = E_Task_Type;
   --  @param File the file and section in which the VCs should be generated
   --  @param E the task entity to be translated

   procedure Generate_VCs_For_Protected_Type (E : Entity_Id)
   with Pre => Ekind (E) = E_Protected_Type;

   procedure Translate_Subprogram_Spec (E : Entity_Id) with
     Pre => Ekind (E) in E_Entry | E_Function | E_Procedure;
   --  Generate a Why logic declaration that corresponds to an Ada subprogram

   function Get_Logic_Args
     (E           : Entity_Id;
      Ref_Allowed : Boolean) return W_Expr_Array;
   --  Get the expressions to use in a function call for an additional logic
   --  binders.

   procedure Generate_Subprogram_Completion (E : Entity_Id) with
     Pre => Ekind (E) in E_Entry | E_Function | E_Procedure;
   --  Generate a Why program declaration and potentially a defining axiom for
   --  an Ada subprogram.

   procedure Translate_Expression_Function_Body (E : Entity_Id)
   with Pre => Is_Expression_Function_Or_Completion (E);
   --  If subprogram E's body is in SPARK, generate a Why axiom that, given a
   --  function F with expression E, states that: "for all <args> => F(<args>)
   --  = E". Also generate a program function for E.

   function Compute_Subprogram_Parameters
     (E      : Entity_Id;
      Domain : EW_Domain) return Item_Array;
   --  Return Why binders for the parameters of subprogram E.
   --  If Domain is EW_Term also generates binders for E's read effects.

   procedure Update_Symbol_Table_For_Inherited_Contracts (E : Entity_Id);
   --  The inherited precondition and postcondition for E is expressed wrt the
   --  overridden's subprogram parameters. Make sure these are mapped in the
   --  symbol table to the current subprogram'ms parameters. The result symbol
   --  is always mapped to the current result.

   procedure Insert_Exception (Exc : W_Name_Id);
   --  Add a new exception that should be declared before the unit

   function Need_Self_Binder (E : Entity_Id) return Boolean;
   --  Return True on entries and subprograms located within a protected object

private

   procedure Declare_Logic_Functions
     (Th           : Theory_UC;
      E            : Entity_Id;
      Spec_Binders : Binder_Array := Binder_Array'(1 .. 0 => <>));
   --  @param File section in which the expression should be translated
   --  @param E entry or subprogram or subprogram type entity
   --  @param Spec_Binders special binders to be used in addition to normal
   --    binders for the subprogram.
   --  Declare a logic function and a guard predicate for E. If needed,
   --  generate a namespace for the dispatching/refined variants.

   procedure Generate_Subprogram_Program_Fun
     (Th                     : Theory_UC;
      E                      : Entity_Id;
      Prog_Id                : W_Identifier_Id;
      Spec_Binders           : Binder_Array := Binder_Array'(1 .. 0 => <>);
      Is_Access_Subp_Wrapper : Boolean := False);
   --  @param File section in which the expression should be translated
   --  @param E entry or subprogram or subprogram type entity
   --  @param Prog_Id name of the program function
   --  @param Spec_Binders special binders to be used in addition to normal
   --    binders for the subprogram.
   --  @param Is_Access_Subp_Wrapper true if we are generating a function for
   --    an access-to-subprogram type through its wrapper.
   --  Generate a why program function for E. Also generate a program function
   --  that performs invariant checks for global / parameters of E. It should
   --  be called before calling E's program function.

   procedure Generate_Axiom_For_Post
     (Th                     : Theory_UC;
      E                      : Entity_Id;
      Spec_Binders           : Binder_Array := (1 .. 0 => <>);
      Spec_Guard             : W_Pred_Id := True_Pred;
      Is_Access_Subp_Wrapper : Boolean := False)
   with Pre => Is_Access_Subp_Wrapper
     or else Ekind (E) = E_Subprogram_Type
     or else (Is_True_Boolean (+Spec_Guard) and Spec_Binders'Length = 0);
   --  @param File section in which the expression should be translated
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
   --  If E is a function, generate an axiom stating that postcondition of E
   --  is equivalent to Spec_Guard.

   function Compute_Dynamic_Property_For_Inputs
     (E              : Entity_Id;
      Params         : Transformation_Params;
      Pred_Fun_Param : Entity_Id := Empty) return W_Prog_Id
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
     (E       : Entity_Id;
      Compute : Boolean) return Item_Array
   with Pre => Ekind (E) in Subprogram_Kind | E_Entry | E_Subprogram_Type;
   --  @param E an enity for a subprogram
   --  @param Compute True if binders should be created when not in the
   --    symbol table.
   --  @result an array containing an Item per global variable read / written
   --          by E.

   function Compute_Call_Effects
     (Params : Transformation_Params;
      E      : Entity_Id)
      return W_Prog_Id;
   --  Generate a Why3 program simulating the effects of a call of the
   --  subprogram.

   function Same_Globals (Subp_1, Subp_2 : Entity_Id) return Boolean with
     Pre => Ekind (Subp_1) in Subprogram_Kind | E_Entry | E_Subprogram_Type
        and Ekind (Subp_2) in Subprogram_Kind | E_Entry | E_Subprogram_Type;
   --  Return True if Subp_1 and Sup2 access the same set of global variables

   function Compute_Contract_Cases_Postcondition
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Pred_Id;
   --  Returns the postcondition corresponding to the Contract_Cases pragma for
   --  subprogram E (if any), to be used in the postcondition of the program
   --  function.

   procedure Collect_Old_For_Subprogram
     (E                 : Entity_Id;
      Old_Parts         : in out Node_Sets.Set;
      Exclude_Classwide : Boolean := True;
      Exclude_CC        : Boolean := False);
   --  Collects the set of old attributes occuring in the postcondition of E.
   --  If Exclude_CC is False, also collects old attributes and guards from
   --  the contract case if any.
   --  If Exclude_Classwide is False, defaults to the classwide postcondition
   --  if no contract cases/specific postconditions are present.

end Gnat2Why.Subprograms;
