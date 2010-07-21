------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            W H Y - A T R E E                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Types;  use Types;
with Namet;  use Namet;
with Uintp;  use Uintp;
with Urealp; use Urealp;

with Why.Sinfo; use Why.Sinfo;
with Why.Types; use Why.Types;
with Why.Ids;   use Why.Ids;

package Why.Atree is
   --  This package defines the format of the abstract syntax tree to
   --  represent a Why program.

   --  The basic structure of this tree relies on type Why_Node.
   --  This variant record sticks quite closely to the syntax given
   --  in Why's reference manual and in package Why.Sinfo. This
   --  would have the advantage to allow some code generation from
   --  this spec. To allow that, we will have to enforce the following
   --  rules:
   --
   --  * each field may either be a subtype of Node_Id or of Node_Id_List
   --  (with the exception of real/int constants and identifier names);
   --
   --  * a field which may have no value should be initialized to
   --  Empty/Empty_List by default; on the contrary, a field which
   --  should always be present (or a list which shall not be empty)
   --  shall not have any default initialization;
   --
   --  * singleton nodes are exactly the ones that have a null variant part;
   --
   --  * each field name in the variant part consists in two parts:
   --  a header in uppercase, related to the kind of this node;
   --  a general field name, which tells what this field actually represents;
   --
   --  * the field name header is arbitrary; it may just be the first letters
   --  of the node kind; we shall just make sure to avoid name clashes;
   --
   --  * the general field name shall be thought with overriding in mind;
   --  e.g. named entities should have a field whose general field name is
   --  Name; defining entities should have a field whose general field name is
   --  Def. For these, general setters/getters will be generated. Among
   --  overridden fields, we have Return_Type, Binders, Left, Right, Op,
   --  Then, Else, Parameters...

   --  Although none should be needed to generate Why code, this tree
   --  will also contain some minimal semantic information; this would
   --  be enclosed in the field Entity of kind Identifier. It is not
   --  clear yet if this information will have any utility.

   type Why_Node (Kind : Why_Node_Kind := W_Unused_At_Start) is record
      --  Basic type for nodes in the abstract syntax tree. Each non-documented
      --  field of this structure should be explicited in the syntax given
      --  in Why.Sinfo.

      Ada_Node : Node_Id;
      --  Id of the corresponding node in the Ada tree, if any.
      --  The type is Sinfo.Node_Id.

      Link : Why_Node_Id;
      --  For a node, points to the Parent. For a list, points
      --  to the list header.

      case Kind is
         when W_Unused_At_Start =>
            null;

         when W_Identifier =>
            Symbol : Name_Id;
            Entity : Why_Node_Id := Why_Empty;

         when W_Type_Prop .. W_Type_Unit =>
            null;

         when W_Abstract_Type =>
            AT_Name : W_Identifier_Id;

         when W_Generic_Formal_Type =>
            GFT_Name : W_Identifier_Id;

         when W_Generic_Actual_Type_Chain =>
            GATC_Type_Chain : W_Primitive_Type_List;
            GATC_Name       : W_Identifier_Id;

         when W_Array_Type =>
            AT_Component_Type : W_Primitive_Type_Id;

         when W_Ref_Type =>
            RT_Aliased_Type : W_Primitive_Type_Id;

         when W_Protected_Value_Type =>
            PVT_Value_Type : W_Value_Type_Id;

         when W_Anonymous_Arrow_Type =>
            AAT_Left  : W_Simple_Value_Type_Id;
            AAT_Right : W_Computation_Type_Id;

         when W_Named_Arrow_Type =>
            NA_Name  : W_Identifier_Id;
            NA_Left  : W_Simple_Value_Type_Id;
            NA_Right : W_Computation_Type_Id;

         when W_Computation_Spec =>
            CS_Precondition  : W_Precondition_Id := Why_Empty;
            CS_Result_Name   : W_Identifier_Id := Why_Empty;
            CS_Return_Type   : W_Value_Type_Id;
            CS_Effects       : W_Effects_Id;
            CS_Postcondition : W_Postcondition_Id := Why_Empty;

         when W_Integer_Constant =>
            IC_Uint : Uint;

         when W_Real_Constant =>
            IC_Ureal : Ureal;

         when W_True_Literal .. W_Void_Literal =>
            null;

         when W_Arith_Operation =>
            AO_Left  : W_Term_Id;
            AO_Op    : W_Arith_Op_Id;
            AO_Right : W_Term_Id;

         when W_Negative_Term =>
            NT_Operand : W_Term_Id;

         when W_Label_Identifier =>
            TI_Name  : W_Identifier_Id;
            TI_Label : W_Identifier_Id := Why_Empty;

         when W_Operation =>
            O_Name       : W_Identifier_Id;
            O_Parameters : W_Term_List;

         when W_Named_Term =>
            NT_Name : W_Label_Identifier_Id;
            NT_Term : W_Term_Id;

         when W_Conditional_Term =>
            CT_Condition : W_Term_Id;
            CT_Then      : W_Term_Id;
            CT_Else      : W_Term_Id;

         when W_Binding_Term =>
            BT_Name    : W_Identifier_Id;
            BT_Def     : W_Term_Id;
            BT_Context : W_Term_Id;

         when W_Protected_Term =>
            BT_Term : W_Term_Id;

         when W_Op_Add .. W_Op_Modulo =>
            null;

         when W_True_Literal_Pred .. W_False_Literal_Pred =>
            null;

         when W_Predicate_Identifier =>
            PID_Name : W_Identifier_Id;

         when W_Predicate_Instance =>
            PIN_Name       : W_Identifier_Id;
            PIN_Parameters : W_Term_List;

         when W_Related_Terms =>
            RT_Left   : W_Term_Id;
            RT_Op     : W_Relation_Id;
            RT_Right  : W_Term_Id;
            RT_Op2    : W_Relation_Id := Why_Empty;
            RT_Right2 : W_Term_Id := Why_Empty;

         when W_Implication .. W_Conjonction =>
            ITOC_Left  : W_Predicate_Id;
            ITOC_Right : W_Predicate_Id;

         when W_Negation =>
            N_Operand : W_Predicate_Id;

         when W_Conditional_Pred =>
            CPD_Condition : W_Term_Id;
            CPD_Then      : W_Predicate_Id;
            CPD_Else      : W_Predicate_Id;

         when W_Binding_Pred =>
            BPD_Name    : W_Identifier_Id;
            BPD_Def     : W_Term_Id;
            BPD_Context : W_Predicate_Id;

         when W_Universal_Quantif =>
            UQ_Variables : W_Identifier_List;
            UQ_Var_Type  : W_Primitive_Type_Id;
            UQ_Triggers  : W_Triggers_List := Why_Empty_List;
            UQ_Pred      : W_Predicate_Id;

         when W_Existential_Quantif =>
            EQ_Variables : W_Identifier_List;
            EQ_Var_Type  : W_Primitive_Type_Id;
            EQ_Pred      : W_Predicate_Id;

         when W_Named_Predicate =>
            NP_Name : W_Identifier_Id;
            NP_Pred : W_Predicate_Id;

         when W_Protected_Predicate =>
            PP_Pred : W_Predicate_Id;

         when W_Triggers =>
            TRS_Triggers : W_Trigger_List;

         when W_Trigger =>
            TRI_Terms : W_Term_List;

         when W_Rel_Eq .. W_Rel_Ge =>
            null;

         when W_Type =>
            T_External        : W_External_Id := Why_Empty;
            T_Type_Parameters : W_Identifier_List := Why_Empty_List;
            T_Name            : W_Identifier_Id;

         when W_Logic =>
            L_External : W_External_Id := Why_Empty;
            L_Names    : W_Identifier_List;
            L_Type     : W_Logic_Type_Id;

         when W_Function =>
            F_Name        : W_Identifier_Id;
            F_Binders     : W_Logic_Binder_List;
            F_Return_Type : W_Primitive_Type_Id;
            F_Def         : W_Term_Id;

         when W_Predicate_Definition =>
            P_Name    : W_Identifier_Id;
            P_Binders : W_Logic_Binder_List;
            P_Def     : W_Predicate_Id;

         when W_Inductive =>
            I_Name : W_Identifier_Id;
            I_Type : W_Logic_Type_Id;
            I_Def  : W_Inductive_Case_List;

         when W_Axiom =>
            AX_Name : W_Identifier_Id;
            AX_Def  : W_Predicate_Id;

         when W_Goal =>
            G_Name : W_Identifier_Id;
            G_Def  : W_Predicate_Id;

         when W_External =>
            null;

         when W_Logic_Type =>
            LT_Arg_Types   : W_Logic_Arg_Type_List;
            LT_Return_Type : W_Logic_Return_Type_List;

         when W_Logic_Binder =>
            LB_Name : W_Identifier_Id;
            LB_Type : W_Primitive_Type_Id;

         when W_Inductive_Case =>
            IC_Name : W_Identifier_Id;
            IC_Pred : W_Predicate_Id;

         when W_Effects =>
            E_Reads  : W_Identifier_List := Why_Empty_List;
            E_Writes : W_Identifier_List := Why_Empty_List;
            E_Raises : W_Identifier_List := Why_Empty_List;

         when W_Precondition =>
            PRE_Assertion : W_Assertion_Id;

         when W_Postcondition =>
            POST_Assertion : W_Assertion_Id;
            POST_Handlers  : W_Exn_Condition_List := Why_Empty_List;

         when W_Exn_Condition =>
            EC_Exception : W_Identifier_Id;
            EC_Assertion : W_Assertion_Id;

         when W_Assertion =>
            A_Pred : W_Predicate_Id;
            A_As   : W_Identifier_Id := Why_Empty;

         when W_Prog_Constant =>
            PC_Def : W_Constant_Id;

         when W_Prog_Identifier =>
            PI_Def : W_Identifier_Id;

         when W_Deref =>
            D_Ref : W_Identifier_Id;

         when W_Assignment =>
            A_Name  : W_Identifier_Id;
            A_Value : W_Prog_Id;

         when W_Array_Access =>
            AA_Name  : W_Identifier_Id;
            AA_Index : W_Prog_Id;

         when W_Array_Update =>
            AU_Name  : W_Identifier_Id;
            AU_Index : W_Prog_Id;
            AU_Value : W_Prog_Id;

         when W_Infix_Call =>
            IC_Left  : W_Prog_Id;
            IC_Infix : W_Infix_Id;
            IC_Right : W_Prog_Id;

         when W_Prefix_Call =>
            PC_Prefix   : W_Prefix_Id;
            PC_Operand  : W_Prog_Id;

         when W_Binding_Prog .. W_Binding_Ref =>
            BPG_Name    : W_Identifier_Id;
            BPG_Def     : W_Prog_Id;
            BPG_Context : W_Prog_Id;

         when W_Conditional_Prog =>
            CPG_Condition : W_Prog_Id;
            CPG_Then      : W_Prog_Id;
            CPG_Else      : W_Prog_Id := Why_Empty;

         when W_While_Loop =>
            WL_Condition  : W_Prog_Id;
            WL_Annotation : W_Loop_Annot_Id;
            WL_Loop       : W_Prog_Id;

         when W_Statement_Sequence =>
            SS_Statements : W_Prog_List;

         when W_Label =>
            L_Name : W_Identifier_Id;
            L_Def  : W_Prog_Id;

         when W_Assert =>
            AS_Assertions : W_Assertion_List;
            AS_Prog       : W_Prog_Id;

         when W_Post_Assertion .. W_Opaque_Assertion =>
            PA_Prog : W_Prog_Id;
            PA_Post : W_Postcondition_Id;

         when W_Fun_Def =>
            FD_Binders : W_Binders_Id;
            FD_Return  : W_Prog_Id;

         when W_Binding_Fun =>
            BF_Name    : W_Identifier_Id;
            BF_Binders : W_Binders_Id;
            BF_Def     : W_Prog_Id;
            BF_Context : W_Prog_Id;

         when W_Binding_Rec =>
            BR_Recfun  : W_Recfun_Id;
            BR_Context : W_Prog_Id;

         when W_Prog_Sequence =>
            PS_Progs : W_Prog_List;

         when W_Raise_Statement =>
            RS_Name : W_Identifier_Id;
            RS_Type : W_Value_Type_Id := Why_Empty;

         when W_Raise_Statement_With_Parameters =>
            RSWP_Name      : W_Identifier_Id;
            RSWP_Parameter : W_Term_Id;
            RSWP_Type      : W_Value_Type_Id := Why_Empty;

         when W_Try_Block =>
            TB_Prog    : W_Prog_Id;
            TB_Handler : W_Handler_List;

         when W_Unreachable_Code =>
            UC_Type : W_Value_Type_Id := Why_Empty;

         when W_Begin_Block .. W_Protected_Prog =>
            BB_Prog : W_Prog_Id;

         when W_Op_Add_Prog .. W_Op_Not_Prog =>
            null;

         when W_Binders =>
            BS_Binders : W_Binders_List;

         when W_Binder =>
            B_Names : W_Identifier_List;
            B_Type  : W_Value_Type_Id;

         when W_Recfun =>
            RF_Name        : W_Identifier_Id;
            RF_Binders     : W_Binders_Id;
            RF_Return_Type : W_Prog_Id;
            RF_Variant     : W_Wf_Arg_Id;
            RF_Def         : W_Prog_Id;

         when W_Loop_Annot =>
            LA_Invariant : W_Assertion_Id := Why_Empty;
            LA_Variant   : W_Wf_Arg_Id := Why_Empty;

         when W_Wf_Arg =>
            WA_Def : W_Term_Id;
            WA_For : W_Identifier_Id := Why_Empty;

         when W_Handler =>
            H_Name      : W_Identifier_Id;
            H_Parameter : W_Prog_Id := Why_Empty;
            H_Def       : W_Prog_Id;

         when W_File =>
            F_Declarations : W_Declaration_List := Why_Empty_List;

         when W_Global_Binding =>
            GB_Name    : W_Identifier_Id;
            GB_Binders : W_Binders_Id := Why_Empty;
            GB_Def     : W_Prog_Id;

         when W_Global_Rec_Binding =>
            GRB_Name : W_Recfun_Id;

         when W_Parameter_Declaration =>
            PD_External : W_External_Id;
            PD_Names    : W_Identifier_List;
            PD_Type     : W_Value_Type_List;

         when W_Exception_Declaration =>
            ED_Name      : W_Identifier_Id;
            ED_Parameter : W_Primitive_Type_Id := Why_Empty;

         when W_Logic_Declaration =>
            LD_Decl : W_Logic_Id;

      end case;
   end record;

end Why.Atree;
