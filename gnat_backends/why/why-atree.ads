------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            W H Y - A T R E E                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Why.Sinfo;      use Why.Sinfo;
with Why.Types;      use Why.Types;
with Why.Opaque_Ids; use Why.Opaque_Ids;

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
   --  * a field which may have no value should be of an Option Id type;
   --  on the contrary, a field which should always be present (or a list
   --  which shall not be empty) shall be of the regular Id type;
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
   --  Then_Part, Else_Part, Parameters... They should not conflict with
   --  Ada keywords.

   --  Although none should be needed to generate Why code, this tree
   --  will also contain some minimal semantic information; this would
   --  be enclosed in the field Entity of kind Identifier. It is not
   --  clear yet if this information will have any utility.

   type Why_Node (Kind : Why_Node_Kind := W_Unused_At_Start) is record
      --  Basic type for nodes in the abstract syntax tree. Each non-documented
      --  field of this structure should be explicited in the syntax given
      --  in Why.Sinfo.

      -------------------
      -- Common Fields --
      -------------------

      --  Fields that are shared amongst all node kinds

      Ada_Node : Node_Id;
      --  Id of the corresponding node in the Ada tree, if any.
      --  The type is Sinfo.Node_Id.

      --------------------
      -- Special Fields --
      --------------------

      --  Fields that have some specific in xtree; any field added here
      --  should also be added in xtree_tables. They are meant to be used
      --  for flags that records some properties on the syntax tree, and
      --  that are updated implicitely by operations on node ids (mutators,
      --  accessors, builders, traversals).

      Link : Why_Node_Set;
      --  For a node, points to the Parent. For a list, points
      --  to the list header.

      Checked : Boolean;
      --  True if the sub-tree whose root is this node represents a valid
      --  Why syntax tree.

      ------------------
      -- Variant Part --
      ------------------

      case Kind is
         when W_Unused_At_Start =>
            null;

         when W_Identifier =>
            Symbol : Name_Id;
            Entity : Why_Node_Id := Why_Empty;

         when W_Type_Prop .. W_Type_Unit =>
            null;

         when W_Abstract_Type =>
            AT_Name : W_Identifier_Opaque_Id;

         when W_Generic_Formal_Type =>
            GFT_Name : W_Identifier_Opaque_Id;

         when W_Generic_Actual_Type_Chain =>
            GATC_Type_Chain : W_Primitive_Type_Opaque_List;
            GATC_Name       : W_Identifier_Opaque_Id;

         when W_Array_Type =>
            AT_Component_Type : W_Primitive_Type_Opaque_Id;

         when W_Ref_Type =>
            RT_Aliased_Type : W_Primitive_Type_Opaque_Id;

         when W_Protected_Value_Type =>
            PVT_Value_Type : W_Value_Type_Opaque_Id;

         when W_Arrow_Type =>
            NA_Name  : W_Identifier_Opaque_OId;
            NA_Left  : W_Simple_Value_Type_Opaque_Id;
            NA_Right : W_Computation_Type_Opaque_Id;

         when W_Computation_Spec =>
            CS_Precondition  : W_Precondition_Opaque_OId;
            CS_Result_Name   : W_Identifier_Opaque_OId;
            CS_Return_Type   : W_Value_Type_Opaque_Id;
            CS_Effects       : W_Effects_Opaque_Id;
            CS_Postcondition : W_Postcondition_Opaque_OId;

         when W_Integer_Constant =>
            IC_Value : Uint;

         when W_Real_Constant =>
            RC_Value : Ureal;

         when W_True_Literal .. W_Void_Literal =>
            null;

         when W_Arith_Operation =>
            AO_Left  : W_Term_Opaque_Id;
            AO_Op    : W_Arith_Op_Opaque_Id;
            AO_Right : W_Term_Opaque_Id;

         when W_Negative_Term =>
            NT_Operand : W_Term_Opaque_Id;

         when W_Label_Identifier =>
            TI_Name  : W_Identifier_Opaque_Id;
            TI_Label : W_Identifier_Opaque_OId;

         when W_Operation =>
            O_Name       : W_Identifier_Opaque_Id;
            O_Parameters : W_Term_Opaque_List;

         when W_Named_Term =>
            NT_Name : W_Label_Identifier_Opaque_Id;
            NT_Term : W_Term_Opaque_Id;

         when W_Conditional_Term =>
            CT_Condition : W_Term_Opaque_Id;
            CT_Then_Part : W_Term_Opaque_Id;
            CT_Else_Part : W_Term_Opaque_Id;

         when W_Matching_Term =>
            MT_Term     : W_Term_Opaque_Id;
            MT_Branches : W_Match_Case_Opaque_List;

         when W_Binding_Term =>
            BT_Name    : W_Identifier_Opaque_Id;
            BT_Def     : W_Term_Opaque_Id;
            BT_Context : W_Term_Opaque_Id;

         when W_Protected_Term =>
            BT_Term : W_Term_Opaque_Id;

         when W_Op_Add .. W_Op_Modulo =>
            null;

         when W_True_Literal_Pred .. W_False_Literal_Pred =>
            null;

         when W_Predicate_Identifier =>
            PID_Name : W_Identifier_Opaque_Id;

         when W_Predicate_Instance =>
            PIN_Name       : W_Identifier_Opaque_Id;
            PIN_Parameters : W_Term_Opaque_List;

         when W_Related_Terms =>
            RT_Left   : W_Term_Opaque_Id;
            RT_Op     : W_Relation_Opaque_Id;
            RT_Right  : W_Term_Opaque_Id;
            RT_Op2    : W_Relation_Opaque_OId;
            RT_Right2 : W_Term_Opaque_OId;

         when W_Implication .. W_Conjonction =>
            ITOC_Left  : W_Predicate_Opaque_Id;
            ITOC_Right : W_Predicate_Opaque_Id;

         when W_Negation =>
            N_Operand : W_Predicate_Opaque_Id;

         when W_Conditional_Pred =>
            CPD_Condition : W_Term_Opaque_Id;
            CPD_Then_Part : W_Predicate_Opaque_Id;
            CPD_Else_Part : W_Predicate_Opaque_Id;

         when W_Binding_Pred =>
            BPD_Name    : W_Identifier_Opaque_Id;
            BPD_Def     : W_Term_Opaque_Id;
            BPD_Context : W_Predicate_Opaque_Id;

         when W_Universal_Quantif =>
            UQ_Variables : W_Identifier_Opaque_List;
            UQ_Var_Type  : W_Primitive_Type_Opaque_Id;
            UQ_Triggers  : W_Triggers_Opaque_OId;
            UQ_Pred      : W_Predicate_Opaque_Id;

         when W_Existential_Quantif =>
            EQ_Variables : W_Identifier_Opaque_List;
            EQ_Var_Type  : W_Primitive_Type_Opaque_Id;
            EQ_Pred      : W_Predicate_Opaque_Id;

         when W_Named_Predicate =>
            NP_Name : W_Identifier_Opaque_Id;
            NP_Pred : W_Predicate_Opaque_Id;

         when W_Protected_Predicate =>
            PP_Pred : W_Predicate_Opaque_Id;

         when W_Pattern =>
            PAT_Constr : W_Identifier_Opaque_Id;
            PAT_Args   : W_Identifier_Opaque_OList;

         when W_Match_Case =>
            MC_Pattern : W_Pattern_Opaque_Id;
            MC_Term    : W_Term_Opaque_Id;

         when W_Triggers =>
            TRS_Triggers : W_Trigger_Opaque_List;

         when W_Trigger =>
            TRI_Terms : W_Term_Opaque_List;

         when W_Rel_Eq .. W_Rel_Ge =>
            null;

         when W_Type =>
            T_External        : W_External_Opaque_OId;
            T_Type_Parameters : W_Identifier_Opaque_OList;
            T_Name            : W_Identifier_Opaque_Id;
            T_Definition      : W_Type_Definition_Opaque_OId;

         when W_Logic =>
            L_External   : W_External_Opaque_OId;
            L_Names      : W_Identifier_Opaque_List;
            L_Logic_Type : W_Logic_Type_Opaque_Id;

         when W_Function =>
            F_Name        : W_Identifier_Opaque_Id;
            F_Binders     : W_Logic_Binder_Opaque_List;
            F_Return_Type : W_Primitive_Type_Opaque_Id;
            F_Def         : W_Term_Opaque_Id;

         when W_Predicate_Definition =>
            P_Name    : W_Identifier_Opaque_Id;
            P_Binders : W_Logic_Binder_Opaque_List;
            P_Def     : W_Predicate_Opaque_Id;

         when W_Inductive =>
            I_Name       : W_Identifier_Opaque_Id;
            I_Logic_Type : W_Logic_Type_Opaque_Id;
            I_Def        : W_Inductive_Case_Opaque_List;

         when W_Axiom =>
            AX_Name : W_Identifier_Opaque_Id;
            AX_Def  : W_Predicate_Opaque_Id;

         when W_Goal =>
            G_Name : W_Identifier_Opaque_Id;
            G_Def  : W_Predicate_Opaque_Id;

         when W_External =>
            null;

         when W_Logic_Type =>
            LT_Arg_Types   : W_Logic_Arg_Type_Opaque_List;
            LT_Return_Type : W_Logic_Return_Type_Opaque_Id;

         when W_Logic_Binder =>
            LB_Name       : W_Identifier_Opaque_Id;
            LB_Param_Type : W_Primitive_Type_Opaque_Id;

         when W_Inductive_Case =>
            IC_Name : W_Identifier_Opaque_Id;
            IC_Pred : W_Predicate_Opaque_Id;

         when W_Transparent_Type_Definition =>
            Tr_Type_Definition : W_Primitive_Type_Opaque_Id;

         when W_Adt_Definition =>
            Adt_Constructors : W_Constr_Decl_Opaque_List;

         when W_Constr_Decl =>
            C_Name     : W_Identifier_Opaque_Id;
            C_Arg_List : W_Primitive_Type_Opaque_OList;

         when W_Effects =>
            E_Reads  : W_Identifier_Opaque_OList;
            E_Writes : W_Identifier_Opaque_OList;
            E_Raises : W_Identifier_Opaque_OList;

         when W_Precondition =>
            PRE_Assertion : W_Assertion_Opaque_Id;

         when W_Postcondition =>
            POST_Assertion : W_Assertion_Opaque_Id;
            POST_Handlers  : W_Exn_Condition_Opaque_OList;

         when W_Exn_Condition =>
            EC_Exn_Case  : W_Identifier_Opaque_Id;
            EC_Assertion : W_Assertion_Opaque_Id;

         when W_Assertion =>
            A_Pred : W_Predicate_Opaque_Id;
            A_As   : W_Identifier_Opaque_OId;

         when W_Prog_Constant =>
            PC_Def : W_Constant_Opaque_Id;

         when W_Prog_Identifier =>
            PI_Def : W_Identifier_Opaque_Id;

         when W_Deref =>
            D_Ref : W_Identifier_Opaque_Id;

         when W_Assignment =>
            A_Name  : W_Identifier_Opaque_Id;
            A_Value : W_Prog_Opaque_Id;

         when W_Array_Access =>
            AA_Name  : W_Identifier_Opaque_Id;
            AA_Index : W_Prog_Opaque_Id;

         when W_Array_Update =>
            AU_Name  : W_Identifier_Opaque_Id;
            AU_Index : W_Prog_Opaque_Id;
            AU_Value : W_Prog_Opaque_Id;

         when W_Infix_Call =>
            IC_Left  : W_Prog_Opaque_Id;
            IC_Infix : W_Infix_Opaque_Id;
            IC_Right : W_Prog_Opaque_Id;

         when W_Prefix_Call =>
            PC_Prefix   : W_Prefix_Opaque_Id;
            PC_Operand  : W_Prog_Opaque_Id;

         when W_Binding_Prog .. W_Binding_Ref =>
            BPG_Name    : W_Identifier_Opaque_Id;
            BPG_Def     : W_Prog_Opaque_Id;
            BPG_Context : W_Prog_Opaque_Id;

         when W_Conditional_Prog =>
            CPG_Condition : W_Prog_Opaque_Id;
            CPG_Then_Part : W_Prog_Opaque_Id;
            CPG_Else_Part : W_Prog_Opaque_OId;

         when W_While_Loop =>
            WL_Condition    : W_Prog_Opaque_Id;
            WL_Annotation   : W_Loop_Annot_Opaque_Id;
            WL_Loop_Content : W_Prog_Opaque_Id;

         when W_Statement_Sequence =>
            SS_Statements : W_Prog_Opaque_List;

         when W_Label =>
            L_Name : W_Identifier_Opaque_Id;
            L_Def  : W_Prog_Opaque_Id;

         when W_Assert =>
            AS_Assertions : W_Assertion_Opaque_List;
            AS_Prog       : W_Prog_Opaque_Id;

         when W_Post_Assertion .. W_Opaque_Assertion =>
            PA_Prog : W_Prog_Opaque_Id;
            PA_Post : W_Postcondition_Opaque_Id;

         when W_Fun_Def =>
            FD_Binders : W_Binders_Opaque_Id;
            FD_Pre     : W_Precondition_Opaque_Id;
            FD_Def     : W_Prog_Opaque_Id;

         when W_Binding_Fun =>
            BF_Name    : W_Identifier_Opaque_Id;
            BF_Binders : W_Binders_Opaque_Id;
            BF_Pre     : W_Precondition_Opaque_Id;
            BF_Def     : W_Prog_Opaque_Id;
            BF_Context : W_Prog_Opaque_Id;

         when W_Binding_Rec =>
            BR_Recfun  : W_Recfun_Opaque_Id;
            BR_Context : W_Prog_Opaque_Id;

         when W_Prog_Sequence =>
            PS_Progs : W_Prog_Opaque_List;

         when W_Raise_Statement =>
            RS_Name     : W_Identifier_Opaque_Id;
            RS_Exn_Type : W_Value_Type_Opaque_OId;

         when W_Raise_Statement_With_Parameters =>
            RSWP_Name      : W_Identifier_Opaque_Id;
            RSWP_Parameter : W_Term_Opaque_Id;
            RSWP_Exn_Type  : W_Value_Type_Opaque_OId;

         when W_Try_Block =>
            TB_Prog    : W_Prog_Opaque_Id;
            TB_Handler : W_Handler_Opaque_List;

         when W_Unreachable_Code =>
            UC_Exn_Type : W_Value_Type_Opaque_OId;

         when W_Begin_Block .. W_Protected_Prog =>
            BB_Prog : W_Prog_Opaque_Id;

         when W_Op_Add_Prog .. W_Op_Not_Prog =>
            null;

         when W_Binders =>
            BS_Binders : W_Binder_Opaque_List;

         when W_Binder =>
            B_Names     : W_Identifier_Opaque_List;
            B_Arg_Type  : W_Value_Type_Opaque_Id;

         when W_Recfun =>
            RF_Name        : W_Identifier_Opaque_Id;
            RF_Binders     : W_Binders_Opaque_Id;
            RF_Return_Type : W_Prog_Opaque_Id;
            RF_Variant     : W_Wf_Arg_Opaque_Id;
            RF_Pre         : W_Precondition_Opaque_Id;
            RF_Def         : W_Prog_Opaque_Id;

         when W_Loop_Annot =>
            LA_Invariant : W_Assertion_Opaque_OId;
            LA_Variant   : W_Wf_Arg_Opaque_OId;

         when W_Wf_Arg =>
            WA_Def    : W_Term_Opaque_Id;
            WA_For_Id : W_Identifier_Opaque_OId;

         when W_Handler =>
            H_Name      : W_Identifier_Opaque_Id;
            H_Parameter : W_Prog_Opaque_OId;
            H_Def       : W_Prog_Opaque_Id;

         when W_File =>
            F_Declarations : W_Declaration_Opaque_OList;

         when W_Global_Binding =>
            GB_Name    : W_Identifier_Opaque_Id;
            GB_Binders : W_Binders_Opaque_OId;
            GB_Pre     : W_Precondition_Opaque_Id;
            GB_Def     : W_Prog_Opaque_Id;

         when W_Global_Rec_Binding =>
            GRB_Name : W_Recfun_Opaque_Id;

         when W_Parameter_Declaration =>
            PD_External       : W_External_Opaque_Id;
            PD_Names          : W_Identifier_Opaque_List;
            PD_Parameter_Type : W_Value_Type_Opaque_Id;

         when W_Exception_Declaration =>
            ED_Name      : W_Identifier_Opaque_Id;
            ED_Parameter : W_Primitive_Type_Opaque_OId;

         when W_Logic_Declaration =>
            LD_Decl : W_Logic_Declaration_Class_Opaque_Id;

      end case;
   end record;

end Why.Atree;
