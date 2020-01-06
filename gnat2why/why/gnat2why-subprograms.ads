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

with SPARK_Atree;            use SPARK_Atree;
with SPARK_Atree.Entities;   use SPARK_Atree.Entities;
with Gnat2Why.Util;          use Gnat2Why.Util;
with Types;                  use Types;
with Why.Gen.Binders;        use Why.Gen.Binders;
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

   procedure Generate_VCs_For_Subprogram
     (File : W_Section_Id;
      E    : Entity_Id)
     with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure;
   --  Generate Why code from which Why VC generator will generate all VCs
   --  related to the absence of run-time errors in E.

   procedure Generate_VCs_For_Package_Elaboration
     (File : W_Section_Id;
      E    : Entity_Id) with
     Pre => Ekind (E) = E_Package;
   --  Generate Why code from which Why VC generator will generate all VCs
   --  related to the Initial_Condition of E and the absence of run-time
   --  errors in the declarations and body statements of E.

   procedure Generate_VCs_For_LSP
     (File : W_Section_Id;
      E    : Entity_Id) with
     Pre => Ekind (E) in E_Function | E_Procedure;
   --  Generate Why code from which Why VC generator will generate all VCs
   --  related to the verification of LSP for dispatching subprogram E.

   procedure Generate_VCs_For_Task_Type
     (File : W_Section_Id;
      E    : Entity_Id)
   with Pre => Ekind (E) = E_Task_Type;
   --  @param File the file and section in which the VCs should be generated
   --  @param E the task entity to be translated

   procedure Generate_VCs_For_Protected_Type
     (File : W_Section_Id;
      E    : Entity_Id)
   with Pre => Ekind (E) = E_Protected_Type;

   procedure Translate_Subprogram_Spec
     (File : W_Section_Id;
      E    : Entity_Id) with
     Pre => Ekind (E) in E_Entry | E_Function | E_Procedure;
   --  Generate a Why logic declaration that corresponds to an Ada subprogram

   function Get_Logic_Args
     (E           : Entity_Id;
      Ref_Allowed : Boolean) return W_Expr_Array;
   --  Get the expressions to use in a function call for an additional logic
   --  binders.

   procedure Generate_Subprogram_Completion
     (File : W_Section_Id;
      E    : Entity_Id) with
     Pre => Ekind (E) in E_Entry | E_Function | E_Procedure;
   --  Generate a Why program declaration and potentially a defining axiom for
   --  an Ada subprogram.

   procedure Translate_Expression_Function_Body
     (File : W_Section_Id;
      E    : Entity_Id);
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

end Gnat2Why.Subprograms;
