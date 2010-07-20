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
   --  * each field may either be a Node_Id or a Node_Id_List (with
   --  the exception of real/int constants and identifier names);
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
   --
   --  * Each field of type Why_Node_Id shall be followed by a comment
   --  which contains the kind or class of the corresponding node.
   --  Each field of type Why_Node_List shall have the same kind of comment
   --  with the kind or node class of each of its elements. This should be
   --  the only comment before the next entity.

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
            Entity : Why_Node_Id := Why_Empty; --  Why_Node_Id

         when W_Type_Prop .. W_Type_Unit =>
            null;

         when W_Abstract_Type =>
            AT_Name : Why_Node_Id; --  W_Identifier

         when W_Generic_Formal_Type =>
            GFT_Name : Why_Node_Id; --  W_Identifier

         when W_Generic_Actual_Type_Chain =>
            GATC_Type_Chain : Why_Node_List; --  W_Primitive_Type
            GATC_Name       : Why_Node_Id;   --  W_Identifier

         when W_Array_Type =>
            AT_Component_Type : Why_Node_Id; --  W_Primitive_Type

         when W_Ref_Type =>
            RT_Aliased_Type : Why_Node_Id; --  W_Primitive_Type

         when W_Protected_Value_Type =>
            PVT_Value_Type : Why_Node_Id; --  W_Value_Type

         when W_Anonymous_Arrow_Type =>
            AAT_Left  : Why_Node_Id; --  W_Simple_Value_Type
            AAT_Right : Why_Node_Id; --  W_Computation_Type

         when W_Named_Arrow_Type =>
            NA_Name  : Why_Node_Id; --  W_Identifier
            NA_Left  : Why_Node_Id; --  W_Simple_Value_Type
            NA_Right : Why_Node_Id; --  W_Computation_Type

         when W_Computation_Spec =>
            CS_Precondition  : Why_Node_Id := Why_Empty; --  W_Precondition
            CS_Result_Name   : Why_Node_Id := Why_Empty; --  W_Identifier
            CS_Return_Type   : Why_Node_Id;              --  W_Value_Type
            CS_Effects       : Why_Node_Id;              --  W_Effects
            CS_Postcondition : Why_Node_Id := Why_Empty; --  W_Postcondition

         when W_Integer_Constant =>
            IC_Uint : Uint;

         when W_Real_Constant =>
            IC_Ureal : Ureal;

         when W_True_Literal .. W_Void_Literal =>
            null;

         when W_Arith_Operation =>
            AO_Left  : Why_Node_Id; --  W_Term
            AO_Op    : Why_Node_Id; --  W_Arith_Op
            AO_Right : Why_Node_Id; --  W_Term

         when W_Negative_Term =>
            NT_Operand : Why_Node_Id; --  W_Term

         when W_Label_Identifier =>
            TI_Name  : Why_Node_Id;              --  W_Identifier
            TI_Label : Why_Node_Id := Why_Empty; --  W_Identifier

         when W_Operation =>
            O_Name       : Why_Node_Id;   --  W_Identifier
            O_Parameters : Why_Node_List; --  W_Term

         when W_Named_Term =>
            NT_Name : Why_Node_Id; --  W_Label_Identifier
            NT_Term : Why_Node_Id; --  W_Term

         when W_Conditional_Term =>
            CT_Condition : Why_Node_Id; --  W_Term
            CT_Then      : Why_Node_Id; --  W_Term
            CT_Else      : Why_Node_Id; --  W_Term

         when W_Binding_Term =>
            BT_Name    : Why_Node_Id; --  W_Identifier
            BT_Def     : Why_Node_Id; --  W_Term
            BT_Context : Why_Node_Id; --  W_Term

         when W_Protected_Term =>
            BT_Term : Why_Node_Id; --  W_Term

         when W_Op_Add .. W_Op_Modulo =>
            null;

         when W_True_Literal_Pred .. W_False_Literal_Pred =>
            null;

         when W_Predicate_Identifier =>
            PID_Name : Why_Node_Id; --  W_Identifier

         when W_Predicate_Instance =>
            PIN_Name       : Why_Node_Id;   --  W_Identifier
            PIN_Parameters : Why_Node_List; --  W_Term

         when W_Related_Terms =>
            RT_Left   : Why_Node_Id;               --  W_Term
            RT_Op     : Why_Node_Id;               --  W_Relation
            RT_Right  : Why_Node_Id;               --  W_Term
            RT_Op2    : Why_Node_Id := Why_Empty;  --  W_Relation
            RT_Right2 : Why_Node_Id := Why_Empty;  --  W_Term

         when W_Implication .. W_Conjonction =>
            ITOC_Left  : Why_Node_Id; --  W_Predicate
            ITOC_Right : Why_Node_Id; --  W_Predicate

         when W_Negation =>
            N_Operand : Why_Node_Id; --  W_Predicate

         when W_Conditional_Pred =>
            CPD_Condition : Why_Node_Id; --  W_Term
            CPD_Then      : Why_Node_Id; --  W_Predicate
            CPD_Else      : Why_Node_Id; --  W_Predicate

         when W_Binding_Pred =>
            BPD_Name    : Why_Node_Id; --  W_Identifier
            BPD_Def     : Why_Node_Id; --  W_Term
            BPD_Context : Why_Node_Id; --  W_Predicate

         when W_Universal_Quantif =>
            UQ_Variables : Why_Node_List; --  W_Identifier
            UQ_Var_Type  : Why_Node_Id;   --  W_Primitive_Type
            UQ_Triggers  : Why_Node_List := Why_Empty_List; --  W_Triggers
            UQ_Pred      : Why_Node_Id;   --  W_Predicate

         when W_Existential_Quantif =>
            EQ_Variables : Why_Node_List; --  W_Identifier
            EQ_Var_Type  : Why_Node_Id;   --  W_Primitive_Type
            EQ_Pred      : Why_Node_Id;   --  W_Predicate

         when W_Named_Predicate =>
            NP_Name : Why_Node_Id; --  W_Identifier
            NP_Pred : Why_Node_Id; --  W_Predicate

         when W_Protected_Predicate =>
            PP_Pred : Why_Node_Id; --  W_Predicate

         when W_Triggers =>
            TRS_Triggers : Why_Node_List; --  W_Trigger

         when W_Trigger =>
            TRI_Terms : Why_Node_List; -- W_Term

         when W_Rel_Eq .. W_Rel_Ge =>
            null;

         when W_Type =>
            T_External        : Why_Node_Id := Why_Empty; --  W_External
            T_Type_Parameters : Why_Node_List
              := Why_Empty_List;                          --  W_Identifier
            T_Name            : Why_Node_Id;              --  W_Identifier

         when W_Logic =>
            L_External : Why_Node_Id := Why_Empty; --  W_External
            L_Names    : Why_Node_List;            --  W_Identifier
            L_Type     : Why_Node_Id;              --  W_Logic_Type

         when W_Function =>
            F_Name        : Why_Node_Id;   --  W_Identifier
            F_Binders     : Why_Node_List; --  W_Logic_Binder
            F_Return_Type : Why_Node_Id;   --  W_Primitive_Type
            F_Def         : Why_Node_Id;   --  W_Term

         when W_Predicate_Definition =>
            P_Name    : Why_Node_Id;   --  W_Identifier
            P_Binders : Why_Node_List; --  W_Logic_Binder
            P_Def     : Why_Node_Id;   --  W_Predicate

         when W_Inductive =>
            I_Name : Why_Node_Id;   --  W_Identifier
            I_Type : Why_Node_Id;   --  W_Logic_Type
            I_Def  : Why_Node_List; --  W_Inductive_Case

         when W_Axiom =>
            AX_Name : Why_Node_Id; --  W_Identifier
            AX_Def  : Why_Node_Id; --  W_Predicate

         when W_Goal =>
            G_Name : Why_Node_Id; --  W_Identifier
            G_Def  : Why_Node_Id; --  W_Predicate

         when W_External =>
            null;

         when W_Logic_Type =>
            LT_Arg_Types   : Why_Node_List; --  W_Logic_Arg_Type
            LT_Return_Type : Why_Node_List; --  W_Logic_Return_Type

         when W_Logic_Binder =>
            LB_Name : Why_Node_Id; --  W_Identifier
            LB_Type : Why_Node_Id; --  W_Primitive_Type

         when W_Inductive_Case =>
            IC_Name : Why_Node_Id; --  W_Identifier
            IC_Pred : Why_Node_Id; --  W_Predicate

         when W_Effects =>
            E_Reads  : Why_Node_List := Why_Empty_List; --  W_Identifier
            E_Writes : Why_Node_List := Why_Empty_List; --  W_Identifier
            E_Raises : Why_Node_List := Why_Empty_List; --  W_Identifier

         when W_Precondition =>
            PRE_Assertion : Why_Node_Id; --  W_Assertion

         when W_Postcondition =>
            POST_Assertion : Why_Node_Id; -- W_Assertion
            POST_Handlers  : Why_Node_List
              := Why_Empty_List;          -- W_Exn_Condition

         when W_Exn_Condition =>
            EC_Exception : Why_Node_Id; --  W_Identifier
            EC_Assertion : Why_Node_Id; --  W_Assertion

         when W_Assertion =>
            A_Pred : Why_Node_Id;              --  W_Predicate
            A_As   : Why_Node_Id := Why_Empty; --  W_Identifier

         when W_Prog_Constant =>
            PC_Def : Why_Node_Id; --  W_Constant

         when W_Prog_Identifier =>
            PI_Def : Why_Node_Id; --  W_Identifier

         when W_Deref =>
            D_Ref : Why_Node_Id; --  W_Identifier

         when W_Assignment =>
            A_Name  : Why_Node_Id; --  W_Identifier
            A_Value : Why_Node_Id; --  W_Prog

         when W_Array_Access =>
            AA_Name  : Why_Node_Id; --  W_Identifier
            AA_Index : Why_Node_Id; --  W_Prog

         when W_Array_Update =>
            AU_Name  : Why_Node_Id; --  W_Identifier
            AU_Index : Why_Node_Id; --  W_Prog
            AU_Value : Why_Node_Id; --  W_Prog

         when W_Infix_Call =>
            IC_Left  : Why_Node_Id; --  W_Prog
            IC_Infix : Why_Node_Id; --  W_Infix
            IC_Right : Why_Node_Id; --  W_Prog

         when W_Prefix_Call =>
            PC_Prefix   : Why_Node_Id; --  W_Prefix
            PC_Operand  : Why_Node_Id; --  W_Prog

         when W_Binding_Prog .. W_Binding_Ref =>
            BPG_Name    : Why_Node_Id; --  W_Identifier
            BPG_Def     : Why_Node_Id; --  W_Prog
            BPG_Context : Why_Node_Id; --  W_Prog

         when W_Conditional_Prog =>
            CPG_Condition : Why_Node_Id;              --  W_Prog
            CPG_Then      : Why_Node_Id;              --  W_Prog
            CPG_Else      : Why_Node_Id := Why_Empty; --  W_Prog

         when W_While_Loop =>
            WL_Condition  : Why_Node_Id; --  W_Prog
            WL_Annotation : Why_Node_Id; --  W_Loop_Annot
            WL_Loop       : Why_Node_Id; --  W_Prog

         when W_Statement_Sequence =>
            SS_Statements : Why_Node_List; -- W_Prog

         when W_Label =>
            L_Name : Why_Node_Id; --  W_Identifier
            L_Def  : Why_Node_Id; --  W_Prog

         when W_Assert =>
            AS_Assertions : Why_Node_List; --  W_Assertion
            AS_Prog       : Why_Node_Id;   --  W_Prog

         when W_Post_Assertion .. W_Opaque_Assertion =>
            PA_Prog : Why_Node_Id; --  W_Prog
            PA_Post : Why_Node_Id; --  W_Postcondition

         when W_Fun_Def =>
            FD_Binders : Why_Node_Id; --  W_Binders
            FD_Return  : Why_Node_Id; --  W_Prog

         when W_Binding_Fun =>
            BF_Name    : Why_Node_Id; --  W_Identifier
            BF_Binders : Why_Node_Id; --  W_Binders
            BF_Def     : Why_Node_Id; --  W_Prog
            BF_Context : Why_Node_Id; --  W_Prog

         when W_Binding_Rec =>
            BR_Recfun  : Why_Node_Id; --  W_Recfun
            BR_Context : Why_Node_Id; --  W_Prog

         when W_Prog_Sequence =>
            PS_Progs : Why_Node_List; --  W_Prog

         when W_Raise_Statement =>
            RS_Name : Why_Node_Id;              --  W_Identifier
            RS_Type : Why_Node_Id := Why_Empty; --  W_Value_Type

         when W_Raise_Statement_With_Parameters =>
            RSWP_Name      : Why_Node_Id;              --  W_Identifier
            RSWP_Parameter : Why_Node_Id;              --  W_Term
            RSWP_Type      : Why_Node_Id := Why_Empty; --  W_Value_Type

         when W_Try_Block =>
            TB_Prog    : Why_Node_Id;   --  W_Prog
            TB_Handler : Why_Node_List; --  W_Handler

         when W_Unreachable_Code =>
            UC_Type : Why_Node_Id := Why_Empty; --  W_Value_Type

         when W_Begin_Block .. W_Protected_Prog =>
            BB_Prog : Why_Node_Id; --  W_Prog

         when W_Op_Add_Prog .. W_Op_Not_Prog =>
            null;

         when W_Binders =>
            BS_Binders : Why_Node_List; --  W_Binders

         when W_Binder =>
            B_Names : Why_Node_List; --  W_Identifier
            B_Type  : Why_Node_Id;   --  W_Value_Type

         when W_Recfun =>
            RF_Name        : Why_Node_Id; --  W_Identifier
            RF_Binders     : Why_Node_Id; --  W_Binders
            RF_Return_Type : Why_Node_Id; --  W_Prog
            RF_Variant     : Why_Node_Id; --  W_Wf_Arg
            RF_Def         : Why_Node_Id; --  W_Prog

         when W_Loop_Annot =>
            LA_Invariant : Why_Node_Id := Why_Empty; --  W_Assertion
            LA_Variant   : Why_Node_Id := Why_Empty; --  W_Wf_Arg

         when W_Wf_Arg =>
            WA_Def : Why_Node_Id;              --  W_Term
            WA_For : Why_Node_Id := Why_Empty; --  W_Identifier

         when W_Handler =>
            H_Name      : Why_Node_Id;              --  W_Identifier
            H_Parameter : Why_Node_Id := Why_Empty; --  W_Prog
            H_Def       : Why_Node_Id;              --  W_Prog

         when W_File =>
            F_Declarations : Why_Node_List := Why_Empty_List; --  W_Declaration

         when W_Global_Binding =>
            GB_Name    : Why_Node_Id;              --  W_Identifier
            GB_Binders : Why_Node_Id := Why_Empty; --  W_Binders
            GB_Def     : Why_Node_Id;              --  W_Prog

         when W_Global_Rec_Binding =>
            GRB_Name : Why_Node_Id; -- W_Recfun

         when W_Parameter_Declaration =>
            PD_External : Why_Node_Id;   --  W_External
            PD_Names    : Why_Node_List; --  W_Identifier
            PD_Type     : Why_Node_List; --  W_Value_Type

         when W_Exception_Declaration =>
            ED_Name      : Why_Node_Id;              --  W_Identifier
            ED_Parameter : Why_Node_Id := Why_Empty; --  W_Primitive_Type

         when W_Logic_Declaration =>
            LD_Decl : Why_Node_Id; -- W_Logic

      end case;
   end record;

end Why.Atree;
