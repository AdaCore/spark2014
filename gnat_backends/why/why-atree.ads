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

with Ada.Unchecked_Conversion;
with Ada.Containers.Vectors;
with Ada.Containers.Doubly_Linked_Lists;

with Types;  use Types;
with Namet;  use Namet;
with Uintp;  use Uintp;
with Urealp; use Urealp;

with Why.Sinfo; use Why.Sinfo;
with Why.Types; use Why.Types;

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
   --  Empty/Empty_List by default; at the contrary, a field which
   --  should always be present (or a list which shall not be empty)
   --  shall not have any default initialization;
   --
   --  * singleton nodes are exactly the ones that have a null variant part;
   --
   --  * each field name in the variant part consist in two parts:
   --  a header in uppercase, related to the kind of this node;
   --  a general field name, that tells what this field actually represent;
   --
   --  * the field name header is arbitrary; it may just be the first letters
   --  of the node kind; we shall just make sure to avoid name clashes;
   --
   --  * the general field name shall be thought with overidding in mind;
   --  e.g. named entities should have a field whose general field name is
   --  Name; defining entities should have a field whose general field name is
   --  Def. For these, general setters/getters will be generated. Among
   --  overriden fields, we have Return_Type, Binders, Left, Right, Op,
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
            Name   : Name_Id;
            Entity : Why_Node_Id := Why_Empty;

         when W_Type_Prop .. W_Type_Unit =>
            null;

         when W_Abstract_Type =>
            AT_Name : Why_Node_Id;

         when W_Generic_Formal_Type =>
            GFT_Name : Why_Node_Id;

         when W_Generic_Actual_Type_Chain =>
            GATC_Type_Chain : Why_Node_List;
            GATC_Name       : Why_Node_Id;

         when W_Array_Type =>
            AT_Component_Type : Why_Node_Id;

         when W_Ref_Type =>
            RT_Aliased_Type : Why_Node_Id;

         when W_Protected_Value_Type =>
            PVT_Value_Type : Why_Node_Id;

         when W_Anonymous_Arrow_Type =>
            AAT_Left  : Why_Node_Id;
            AAT_Right : Why_Node_Id;

         when W_Named_Arrow_Type =>
            NA_Name  : Why_Node_Id;
            NA_Left  : Why_Node_Id;
            NA_Right : Why_Node_Id;

         when W_Computation_Spec =>
            CS_Precondition  : Why_Node_Id := Why_Empty;
            CS_Result_Name   : Why_Node_Id := Why_Empty;
            CS_Return_Type   : Why_Node_Id;
            CS_Effects       : Why_Node_Id;
            CS_Postcondition : Why_Node_Id := Why_Empty;

         when W_Integer_Constant =>
            IC_Uint : Uint;

         when W_Real_Constant =>
            IC_Ureal : Ureal;

         when W_True_Litteral .. W_Void_Litteral =>
            null;

         when W_Arith_Operation =>
            AO_Left  : Why_Node_Id;
            AO_Op    : Why_Node_Id;
            AO_Right : Why_Node_Id;

         when W_Negative_Term =>
            NT_Operand : Why_Node_Id;

         when W_Label_Identifier =>
            TI_Name  : Why_Node_Id;
            TI_Label : Why_Node_Id := Why_Empty;

         when W_Operation =>
            O_Name       : Why_Node_Id;
            O_Parameters : Why_Node_List;

         when W_Named_Term =>
            NT_Name : Why_Node_Id;
            NT_Term : Why_Node_Id;

         when W_Conditional_Term =>
            CT_Condition : Why_Node_Id;
            CT_Then      : Why_Node_Id;
            CT_Else      : Why_Node_Id;

         when W_Binding_Term =>
            BT_Name    : Why_Node_Id;
            BT_Def     : Why_Node_Id;
            BT_Context : Why_Node_Id;

         when W_Protected_Term =>
            BT_Term : Why_Node_Id;

         when W_Op_Add .. W_Op_Modulo =>
            null;

         when W_True_Litteral_Pred .. W_False_Litteral_Pred =>
            null;

         when W_Predicate_Identifier =>
            PID_Name : Why_Node_Id;

         when W_Predicate_Instance =>
            PIN_Name       : Why_Node_Id;
            PIN_Parameters : Why_Node_List;

         when W_Related_Terms =>
            RT_Left   : Why_Node_Id;
            RT_Op     : Why_Node_Id;
            RT_Right  : Why_Node_Id;
            RT_Op2    : Why_Node_Id := Why_Empty;
            RT_Right2 : Why_Node_Id := Why_Empty;

         when W_Implication .. W_Conjonction =>
            ITOC_Left  : Why_Node_Id;
            ITOC_Right : Why_Node_Id;

         when W_Negation =>
            N_Operand : Why_Node_Id;

         when W_Conditional_Pred =>
            CPD_Condition : Why_Node_Id;
            CPD_Then      : Why_Node_Id;
            CPD_Else      : Why_Node_Id;

         when W_Binding_Pred =>
            BPD_Name    : Why_Node_Id;
            BPD_Def     : Why_Node_Id;
            BPD_Context : Why_Node_Id;

         when W_Universal_Quantif =>
            UQ_Variables : Why_Node_Id;
            UQ_Var_Type  : Why_Node_Id;
            UQ_Triggers  : Why_Node_List := Why_Empty_List;
            UQ_Pred      : Why_Node_List;

         when W_Existencial_Quantif =>
            EQ_Variables : Why_Node_Id;
            EQ_Var_Type  : Why_Node_Id;
            EQ_Pred      : Why_Node_List;

         when W_Named_Predicate =>
            NP_Name : Why_Node_Id;
            NP_Pred : Why_Node_Id;

         when W_Protected_Predicate =>
            PP_Pred : Why_Node_Id;

         when W_Triggers =>
            TRS_Triggers : Why_Node_List;

         when W_Trigger =>
            TRI_Terms : Why_Node_List;

         when W_Rel_Eq .. W_Rel_Ge =>
            null;

         when W_Type =>
            T_External        : Why_Node_Id := Why_Empty;
            T_Type_Parameters : Why_Node_List := Why_Empty_List;
            T_Name            : Why_Node_Id;

         when W_Logic =>
            L_External : Why_Node_Id := Why_Empty;
            L_Names    : Why_Node_List;
            L_Type     : Why_Node_Id;

         when W_Function =>
            F_Name        : Why_Node_Id;
            F_Binders     : Why_Node_List;
            F_Return_Type : Why_Node_Id;
            F_Def         : Why_Node_Id;

         when W_Predicate_Definition =>
            P_Name    : Why_Node_Id;
            P_Binders : Why_Node_List;
            P_Def     : Why_Node_Id;

         when W_Inductive =>
            I_Name : Why_Node_Id;
            I_Type : Why_Node_Id;
            I_Def  : Why_Node_List;

         when W_Axiom =>
            AX_Name : Why_Node_Id;
            AX_Def  : Why_Node_Id;

         when W_Goal =>
            G_Name : Why_Node_Id;
            G_Def  : Why_Node_Id;

         when W_External =>
            null;

         when W_Logic_Type =>
            LT_Arg_Types   : Why_Node_List;
            LT_Return_Type : Why_Node_List;

         when W_Logic_Binder =>
            LB_Name : Why_Node_Id;
            LB_Type : Why_Node_Id;

         when W_Effects =>
            E_Reads  : Why_Node_List := Why_Empty_List;
            E_Writes : Why_Node_List := Why_Empty_List;
            E_Raises : Why_Node_List := Why_Empty_List;

         when W_Precondition =>
            PRE_Assertion : Why_Node_Id;

         when W_Postcondition =>
            POST_Assertion : Why_Node_Id;
            POST_Handlers  : Why_Node_List := Why_Empty_List;

         when W_Exn_Condition =>
            EC_Exception : Why_Node_Id;
            EC_Assertion : Why_Node_Id;

         when W_Assertion =>
            A_Pred : Why_Node_Id;
            A_As   : Why_Node_Id := Why_Empty;

         when W_Prog_Constant =>
            PC_Def : Why_Node_Id;

         when W_Prog_Identifier =>
            PI_Def : Why_Node_Id;

         when W_Deref =>
            D_Ref : Why_Node_Id;

         when W_Assignment =>
            A_Name  : Why_Node_Id;
            A_Value : Why_Node_Id;

         when W_Array_Access =>
            AA_Name  : Why_Node_Id;
            AA_Index : Why_Node_Id;

         when W_Array_Update =>
            AU_Name  : Why_Node_Id;
            AU_Index : Why_Node_Id;
            AU_Value : Why_Node_Id;

         when W_Infix_Call =>
            IC_Left  : Why_Node_Id;
            IC_Infix : Why_Node_Id;
            IC_Right : Why_Node_Id;

         when W_Prefix_Call =>
            PC_Prefix   : Why_Node_Id;
            PC_Operand  : Why_Node_Id;

         when W_Binding_Prog .. W_Binding_Ref =>
            BPG_Name    : Why_Node_Id;
            BPG_Def     : Why_Node_Id;
            BPG_Context : Why_Node_Id;

         when W_Conditional_Prog =>
            CPG_Condition : Why_Node_Id;
            CPG_Then      : Why_Node_Id;
            CPG_Else      : Why_Node_Id := Why_Empty;

         when W_While_Loop =>
            WL_Condition  : Why_Node_Id;
            WL_Annotation : Why_Node_Id;
            WL_Loop       : Why_Node_Id;

         when W_Statement_Sequence =>
            SS_Statements : Why_Node_List;

         when W_Label =>
            L_Name : Why_Node_Id;
            L_Def  : Why_Node_Id;

         when W_Assert =>
            AS_Assertions : Why_Node_List;
            AS_Prog       : Why_Node_Id;

         when W_Post_Assertion .. W_Opaque_Assertion =>
            PA_Prog : Why_Node_Id;
            PA_Post : Why_Node_Id;

         when W_Fun_Def =>
            FD_Binders : Why_Node_Id;
            FD_Return  : Why_Node_Id;

         when W_Binding_Fun =>
            BF_Name    : Why_Node_Id;
            BF_Binders : Why_Node_Id;
            BF_Def     : Why_Node_Id;
            BF_Context : Why_Node_Id;

         when W_Binding_Rec =>
            BR_Recfun  : Why_Node_Id;
            BR_Context : Why_Node_Id;

         when W_Prog_Sequence =>
            PS_Progs : Why_Node_List;

         when W_Raise_Statement =>
            RS_Name : Why_Node_Id;
            RS_Type : Why_Node_Id := Why_Empty;

         when W_Raise_Statement_With_Parameters =>
            RSWP_Name      : Why_Node_Id;
            RSWP_Parameter : Why_Node_Id;
            RSWP_Type      : Why_Node_Id := Why_Empty;

         when W_Try_Block =>
            TB_Prog    : Why_Node_Id;
            TB_Handler : Why_Node_Id;

         when W_Unreachable_Code =>
            UC_Type : Why_Node_Id := Why_Empty;

         when W_Begin_Block .. W_Protected_Prog =>
            BB_Prog : Why_Node_Id;

         when W_Op_Add_Prog .. W_Op_Not_Prog =>
            null;

         when W_Binders =>
            BS_Binders : Why_Node_List;

         when W_Binder =>
            B_Names : Why_Node_List;
            B_Type  : Why_Node_Id;

         when W_Recfun =>
            RF_Name        : Why_Node_Id;
            RF_Binders     : Why_Node_Id;
            RF_Return_Type : Why_Node_Id;
            RF_Variant     : Why_Node_Id;
            RF_Def         : Why_Node_Id;

         when W_Loop_Annot =>
            LA_Invariant : Why_Node_Id := Why_Empty;
            LA_Variant   : Why_Node_Id := Why_Empty;

         when W_Wf_Arg =>
            WA_Def : Why_Node_Id;
            WA_For : Why_Node_Id := Why_Empty;

         when W_Handler =>
            H_Name      : Why_Node_Id;
            H_Parameter : Why_Node_Id := Why_Empty;
            H_Def       : Why_Node_Id;

         when W_File =>
            F_Declarations : Why_Node_List := Why_Empty_List;

         when W_Global_Binding =>
            GB_Name    : Why_Node_Id;
            GB_Binders : Why_Node_Id := Why_Empty;
            GB_Def     : Why_Node_Id;

         when W_Global_Rec_Binding =>
            GRB_Name : Why_Node_Id;

         when W_Parameter_Declaration =>
            PD_External : Why_Node_Id;
            PD_Names    : Why_Node_List;
            PD_Type     : Why_Node_List;

         when W_Exception_Declaration =>
            ED_Name      : Why_Node_Id;
            ED_Parameter : Why_Node_Id := Why_Empty;

         when W_Logic_Declaration =>
            LD_Decl : Why_Node_Id;

      end case;
   end record;

   ------------
   -- Tables --
   ------------

   package Tables is

      --  These tables are used as storage pools for nodes and lists.
      --  They could ultimately be implemented using the containers
      --  that will be defined in the context of Hi-Lite; for now,
      --  use Standard Ada 05 containers, in the hope that Hi-Lite
      --  containers will be similar enough.

      package Node_Tables is
         new Ada.Containers.Vectors (Index_Type   => Why_Node_Id,
                                  Element_Type => Why_Node,
                                  "=" => "=");

      Node_Table : Node_Tables.Vector;

      package Node_Lists is
         new Ada.Containers.Doubly_Linked_Lists (Element_Type => Why_Node_Id,
                                                 "=" => "=");

      function "=" (Left, Right : Node_Lists.List) return Boolean;
      --  Return True if Left and Right have the same extension

      package Node_List_Tables is
         new Ada.Containers.Vectors (Index_Type => Why_Node_List,
                                     Element_Type => Node_Lists.List,
                                     "=" => "=");

      function Get_Node (Node_Id : Why_Node_Id) return Why_Node is
         (Node_Tables.Element (Node_Table, Node_Id));

      function Get_Kind (Node_Id : Why_Node_Id) return Why_Node_Kind is
         (Get_Node (Node_Id).Kind);

      function New_Why_Node_Id (Node : Why_Node) return Why_Node_Id;
      pragma Precondition (Node.Kind /= W_Unused_At_Start);
      pragma Postcondition (Get_Node (New_Why_Node_Id'Result) = Node);
      pragma Inline (New_Why_Node_Id);
      --  Allocate a new Why node in table, and return its Id

   end Tables;

   function Get_Node (Node_Id : Why_Node_Id) return Why_Node
     renames Tables.Get_Node;

   function Get_Kind (Node_Id : Why_Node_Id) return Why_Node_Kind
     renames Tables.Get_Kind;

   function Option
      (Node : Why_Node_Id;
       Value : Why_Node_Kind)
      return Boolean is
      (Node = Why_Empty or else Get_Kind (Node) = Value);

end Why.Atree;
