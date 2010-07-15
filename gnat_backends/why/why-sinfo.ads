------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            W H Y - S I N F O                             --
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

package Why.Sinfo is
   pragma Pure;

   --  This package defines the structure of the abstract syntax tree. It
   --  follows closely the syntax defined in the Why RM.

   --  As a minor difference with the Why RM, primitive types are
   --  defined outside of the two spaces (program/logic); they are
   --  used in both spaces with some local differences on which one is
   --  accepted where, it is practical to define independantly and
   --  define subtypes (node classes) on them to discriminate between
   --  those that are accepted in each context.


   type Why_Node_Kind is
     (
      W_Unused_At_Start,

      --  Identifiers

      W_Identifier,
      --   <identifier> ::= <letter> (<letter> | 0..9 | _ | ')*

      ---------------------------------------------
      -- Primitive types, props, arrays and refs --
      ---------------------------------------------

      --  Some of these nodes are used both in the program space and
      --  in the logic space; so they declared here to allow proper
      --  definition of subtypes for the corresponding node classes.


      --  0.1. Purely logic, return type only:
      ----------------------------------------

      WT_Type_Prop,
      --  <type_prop> ::= 'prop'


      --  0.2. Primitive types, both valid in logic/program space:
      ------------------------------------------------------------

      WT_Type_Int,
      --  <type_int> ::= 'int'

      WT_Type_Bool,
      --  <type_bool> ::= 'bool'

      WT_Type_Real,
      --  <type_real> ::= 'real'

      WT_Type_Unit,
      --  <type_unit> ::= 'unit'

      WT_Abstract_Type,
      --  <abstract_type> ::= <identifier>

      WT_Generic_Formal_Type,
      --  <generic_formal_type> ::= "'" <identifier>

      WT_Generic_Actual_Type_Chain,
      --  <generic_actual_type_chain> ::=
      --     <primitive_type> (<primitive_type>, )* <identifier>


      --  0.3. Only valid in program space:
      -------------------------------------

      WT_Array_Type,
      --  <array_type> ::= <primitive_type> array

      WT_Ref_Type,
      --  <ref_type> ::= <primitive_type> 'ref'

      WT_Protected_Value_Type,
      --  <protected_value_type> ::= '(' <value_type> ')'

      WT_Anonymous_Arrow_Type,
      --  <anonymous_arrow> ::= <simple_value_type> '->' <computation_type>

      WT_Named_Arrow_Type,
      --  <named_arrow_type> ::= <identifier> ':' <simple_value_type>
      --                          '->' <computation_type>

      WT_Computation_Spec,
      --  <computation_spec> ::=
      --       '{' [ <precondition> ] '}'
      --       [ 'returns' <identifier> ':' ] <value_type> <effects>
      --       '{' [ <postcondition> ] '}'


      ------------------
      --  Logic space --
      ------------------

      --  1.1. Terms:
      ---------------

      --  <term> ::= <constant>
      --             | <arith_operation>
      --             | <negative_term>
      --             | <label_identifier>
      --             | <operation>
      --             | <named_term>
      --             | <conditional_term>
      --             | <binding_term>
      --             | <protected_term>

      --  <constant> ::= <integer_constant>
      --                 | <real_constant>
      --                 | <true_litteral>
      --                 | <false_litteral>
      --                 | <void_litteral>

      WLT_Integer_Constant,

      WLT_Real_Constant,

      WLT_True_Litteral,
      --  <true_litteral> ::= 'true'

      WLT_False_Litteral,
      --  <false_litteral> ::= 'false'

      WLT_Void_Litteral,
      --  <void_litteral> ::= 'void'

      WLT_Arith_Operation,
      --  <operation> ::= <term> <arith_op> <term>

      WLT_Negative_Term,
      --  <negative_term> ::= '-' <term>

      WLT_Label_Identifier,
      --  <label_identifier> ::= <identifier> [ @ [ <identifier> ] ]

      WLT_Operation,
      --  <operation> ::= <identifier> '(' <term>+ ')'

      WLT_Named_Term,
      --  <named_term> ::= <label_identifier> '[' <term> ']'

      WLT_Conditional_Term,
      --  <logic_conditional_term> ::= 'if' <term> 'then' <term> 'else' <term>

      WLT_Binding_Term,
      --  <logic_binding> ::= 'let' <identifier> '=' <term> 'in' <term>

      WLT_Protected_Term,
      --  <protected_term> ::= '(' <term> ')'

      --  <arith_op> ::= <op_add>
      --                 | <op_substract>
      --                 | <op_multiply>
      --                 | <op_divide>
      --                 | <op_modulo>

      WLT_Op_Add,
      --  <op_add> ::= '+'

      WLT_Op_Substract,
      --  <op_substract> ::= '-'

      WLT_Op_Multiply,
      --  <op_multiply> ::= '*'

      WLT_Op_Divide,
      --  <op_divide> ::= '/'

      WLT_Op_Modulo,
      --  <op_modulo> ::= '%'

      --  1.2. Predicates:
      --------------------

      -- <predicate> ::= <true_litteral>
      --                 | <false_litteral>
      --                 | <predicate_identifier>
      --                 | <predicate_instance>
      --                 | <related_terms>
      --                 | <implication>
      --                 | <equivalence>
      --                 | <disjunction>
      --                 | <conjonction>
      --                 | <negation>
      --                 | <conditional_pred>
      --                 | <binding_pred>
      --                 | <universal_quantif>
      --                 | <existencial_quantif>
      --                 | <named_predicate>
      --                 | <protected_predicate>

      WLP_True_Litteral,
      --  <true_litteral> ::= 'true'

      WLP_False_Litteral,
      --  <false_litteral> ::= 'false'

      WLP_Predicate_Identifier,
      --  <predicate_identifier> ::= <identifier>

      WLP_Predicate_Instance,
      --  <predicate_instance> ::= <identifier> '(' <term>+ ')'

      WLP_Related_Terms,
      --  <relation_site> ::= <term> <relation> <term> [ <relation> <term> ]

      WLP_Implication,
      --  <implication> ::= <predicate> '->' <predicate>

      WLP_Equivalence,
      --  <predicate> '<->' <predicate>

      WLP_Disjonction,
      --  <disjonction> ::= <predicate> 'or' <predicate>

      WLP_Conjonction,
      --  <conjonction> ::= <predicate> 'and' <predicate>

      WLP_Negation,
      --  <negation> ::= 'not' <predicate>

      WLP_Conditional_Pred,
      --  <conditional_pred> ::= if <term> then <predicate> else <predicate>

      WLP_Binding_Pred,
      --  <binding_pred> ::= let <identifier> = <term> in <predicate>

      WLP_Universal_Quantif,
      -- <universal_quantif> ::=
      --    'forall' <identifier> + ':' <primitive_type>
      --       [ <triggers> ] '.' <predicate>

      WLP_Existencial_Quantif,
      --  <existencial_quantif> ::=
      --     'exists' <identifier>+ ':' <primitive_type> '.' <predicate>

      WLP_Named_Predicate,
      --  ( <identifier> | <string> ) ':' <predicate>

      WLP_Protected_Predicate,
      --  <protected_predicate> ::= '(' <predicate> ')'

      WLP_Triggers,
      --  <triggers> ::= '[' <trigger> ('|' <trigger>) * ']'

      WLP_Trigger,
      --  <trigger> ::= <term> (',' <term>) *

      --  <primitive_type> ::= <type_int>
      --                       | <type_bool>
      --                       | <type_real>
      --                       | <type_unit>
      --                       | <abstract_type>
      --                       | <generic_formal_type>
      --                       | <generic_actual_type_chain>

      --  <relation> ::= <rel_eq>
      --                 | <rel_ne>
      --                 | <rel_lt>
      --                 | <rel_le>
      --                 | <rel_gt>
      --                 | <rel_ge>

      WLP_Rel_Eq,
      --  <rel_eq> ::= '='

      WLP_Rel_Ne,
      --  <rel_ne> ::= '<>'

      WLP_Rel_Lt,
      --  <rel_lt> ::= '<'

      WLP_Rel_Le,
      --  <rel_le> ::= '<='

      WLP_Rel_Gt,
      --  <rel_gt> ::= '>'

      WLP_Rel_Ge,
      -- <rel_ge> ::= '>='

      --  1.3. Logic declarations:
      ----------------------------

      --  <logic_declaration> ::= <type>
      --                          | <logic>
      --                          | <function>
      --                          | <predicate_definition>
      --                          | <inductive_definition>
      --                          | <axiom>
      --                          | <goal>

      WLD_Type,
      --  <type> ::= [ <external> ] 'type' [ <type_parameters> ] <identifier>

      --  <type_parameters> ::=
      --  "'" <identifier> | '(' "'" <identifier> (',' "'" <identifier>)+ ')'

      WLD_Logic,
      --  <logic> ::=
      --  [ <external> ] 'logic' <identifier> [',' <identifier>]*
      --               ':' <logic_type>

      WLD_Function,
      --  <function> ::=
      --  'function' <identifier> '(' <logic_binder> [',' <logic_binder>]* ')'
      --                          ':' <primitive_type>
      --  '=' <term>

      WLD_Predicate,
      --  <predicate> ::=
      --  'predicate' <identifier> '(' <logic_binder> [',' <logic_binder>]* ')'
      --  '=' <predicate>

      WLD_Inductive,
      --  <inductive> ::= 'inductive' <identifier> ':' <logic_type> '='
      --        ('|' <identifier> : <predicate>) +

      WLD_Axiom,
      --  <axiom> ::= 'axiom' <identifier> ':' <predicate>

      WLD_Goal,
      --  <goal> ::= 'goal' <identifier> ':' <predicate>

      WLD_External,
      --  <external> ::= 'external'

      WLD_Logic_Type,
      --  <logic_type> ::=
      --  <logic_arg_type> (',' logic_arg_type)* '->' <logic_return_type>

      --  <logic_arg_type> ::= <primitive_type> | <array_type>

      --  <logic_return_type> ::= <type_prop> | <primitive_type>

      WLD_Logic_Binder,
      --  <logic_binder> ::= <identifier> ':' <primitive_type>


      -------------------
      -- Program space --
      -------------------

      --  2.1. types:
      ---------------

      --  <simple_value_type> ::= <primitive_type>
      --                          | <ref_type>
      --                          | <array_type>
      --                          | <protected_value_type>

      --  <value_type> ::= <simple_value_type>
      --                   | <anonymous_arrow_type>
      --                   | <named_arrow_type>

      --  <computation_type> ::= <computation_spec> | <value_type>

      WPT_Effects,
      --  <effects> ::= [ 'reads' <identifier> (',' <identifier>)* ]
      --                [ 'writes' <identifier> (',' <identifier>)* ]
      --                [ 'raises' <identifier> (',' <identifier>)* ]

      WPT_Precondition,
      --  <precondition> ::= <assertion>

      WPT_Postcondition,
      --  <postcondition> ::= <assertion> <exn_condition>*

      WPT_Exn_Condition,
      --  <exn_condition> ::= '|' <identifier> '=>' <assertion>

      WPT_Assertion,
      --  <assertion> ::= <predicate> [ 'as' <identifier> ]

      --  2.2. Annotated programs:
      ----------------------------

      -- <prog> ::= <prog_constant>
      --            | <prog_identifier>
      --            | <deref>
      --            | <assignment>
      --            | <array_access>
      --            | <array_update>
      --            | <infix_call>
      --            | <prefix_call>
      --            | <binding_prog>
      --            | <binding_ref>
      --            | <conditional_prog>
      --            | <while_loop>
      --            | <statement_sequence>
      --            | <label>
      --            | <assertion>
      --            | <post_assertion>
      --            | <opaque_assertion>
      --            | <fun_def>
      --            | <binding_fun>
      --            | <binding_rec>
      --            | <prog_sequence>
      --            | <raise_statement>
      --            | <raise_statement_with_parameters>
      --            | <try_block>
      --            | <unreachable_code>
      --            | <begin_block>
      --            | <protected_prog>

      WPP_Prog_Constant,
      --  <prog_constant> ::= <constant>

      WPP_Prog_Identifier,
      --  <prog_identifier> ::= <identifier>

      WPP_Deref,
      --  <deref> ::= '!' <identifier>

      WPP_Assignment,
      --  <assignment> ::= <identifier> ':=' <prog>

      WPP_Array_Access,
      --  <array_access> ::= <identifier> '[' <prog> ']'

      WPP_Array_Update,
      --  <array_update> ::= <identifier> '[' <prog> ']' ':=' <prog>

      WPP_Infix_Call,
      --  <infix_call> ::= <prog> <infix> <prog>

      WPP_Prefix_Call,
      --  <prefix_call> ::= <prefix> <prog>

      WPP_Binding_Prog,
      --  <binding_prog> ::= 'let' <identifier> '=' <prog> in <prog>

      WPP_Binding_Ref,
      --  <binding_ref> ::= 'let' <identifier> '=' ref <prog> in <prog>

      WPP_Conditional_Prog,
      --  <conditional_prog> ::= 'if' <prog> 'then' <prog> [ 'else' <prog>]

      WPP_While_Loop,
      --  <while_loop> ::= 'while' <prog> 'do' [ <loop_annot> ] <prog> 'done'

      WPP_Statement_Sequence,
      --  <statement_sequence> ::= <prog> (';' <prog>)+

      WPP_Label,
      --  <label> ::= <identifier> : <prog>

      WPP_Assert,
      --  <assert> ::= 'assert' ('{' <assertion> '}')+ ';' <prog>

      WPP_Post_Assertion,
      --  <post_assertion> ::= <prog> '{' <postcondition> '}'

      WPP_Opaque_Assertion,
      --  <opaque_assertion> ::= <prog> '{{' <postcondition> '}}'

      WPP_Fun_Def,
      --  <fun_def> ::= 'fun' <binders> '->' <prog>

      WPP_Binding_Fun,
      --  <binding_fun> ::= 'let' <identifier> <binders> '=' <prog> 'in' <prog>

      WPP_Binding_Rec,
      --  <binding_rec> ::= 'let' 'rec' <recfun> [ 'in' <prog> ]

      WPP_Prog_Sequence,
      --  <prog> <prog>+

      WPP_Raise_Statement,
      --  <raise_statement> ::= 'raise' <identifier> [ ':' <value_type> ]

      WPP_Raise_Statement_With_Parameters,
      --  <raise_statement_with_parameters> ::=
      --     'raise' '(' <identifier> <prog> ')' [ ':' <value_type> ]

      WPP_Try_Block,
      --  <try_block> ::= 'try' <prog> 'with' <handler> (',' <handler>)* 'end'

      WPP_Unreachable_Code,
      --  <unreachable_code> ::= 'absurd' [ ':' <value_type> ]

      WPP_Begin_Block,
      --  <begin_block> ::= begin <prog> end

      WPP_Protected_Prog,
      --  <protected_prog> ::= '(' <prog> ')'

      --  <infix> ::= <op_add>
      --              | <op_substract>
      --              | <op_multiply>
      --              | <op_divide>
      --              | <op_mod>
      --              | <op_eq>
      --              | <op_Ne>
      --              | <op_lt>
      --              | <op_le>
      --              | <op_gt>
      --              | <op_ge>
      --              | <op_or_else>
      --              | <op_and_then>

      WPP_Op_Add,
      --  <op_add> ::= '+'

      WPP_Op_Substract,
      --  <op_substract> ::= '-'

      WPP_Op_Multiply,
      --  <op_multiply> ::= '*'

      WPP_Op_Divide,
      --  <op_divide> ::= '/'

      WPP_Op_Mod,
      --  <op_mod> ::= '%'

      WPP_Op_Eq,
      --  <op_eq> ::= '='

      WPP_Op_Ne,
      --  <op_divide> ::= '<>'

      WPP_Op_Lt,
      -- <op_lt> ::= '<'

      WPP_Op_Le,
      -- <op_le> ::= '<='

      WPP_Op_Gt,
      --  <op_gt> ::= '>'

      WPP_Op_Ge,
      --  <op_ge> ::= '>='

      WPP_Op_Or_Else,
      --  <op_or_else> ::= '||'

      WPP_Op_And_Then,
      --  <op_and_then> ::= '&&'

      --  <prefix> ::= <op_minus> | <op_not>

      WPP_Op_Minus,
      --  <op_minus> ::= '-'

      WPP_Op_Not,
      -- <op_not> ::= 'not'

      WPP_Binders,
      --  <binders> ::= <binder>+

      WPP_Binder,
      --  <binder> ::=
      --     ('(' <identifier> [',' <identifier>]+ ':' <value_type> ')')

      WPP_Recfun,
      --  <recfun> ::= <identifier> <binders> ':' <value_type>
      --     '{' 'variant' <wf_arg> '}' = <prog>

      WPP_Loop_Annot,
      --  <loop_annot> ::= '{' [ 'invariant' <assertion> ]
      --                       [ 'variant' <wf_arg> ] '}'

      WPP_Wf_Arg,
      --  <wf_arg> ::= <term> [ 'for' <identifier> ]

      WPP_Handler,
      --  <handler> ::= <identifier> [<identifier>] '->' <prog>

      --  2.3. Input files:
      ---------------------

      WPF_File,
      --  <file> ::= <declaration>*

      --  <declaration> ::= <global_binding>
      --                    | <global_rec_binding>
      --                    | <parameter_declaration>
      --                    | <exception_declaration>
      --                    | <logic_declaration>

      WPF_Global_Binding,
      --  <global_binding> ::= 'let' <identifier> [ <binders> ] '=' <prog>

      WPF_Global_Rec_Binding,
      --  <global_rec_binding> ::= 'let' 'rec' <recfun>

      WPF_Parameter_Declaration,
      --  <parameter_declaration> ::=
      --     [ <external> ] parameter <identifier>,+ ':' <value_type>

      WPF_Exception_Declaration,
      --  <exception_declaration> ::=
      --     'exception' <identifier> [ 'of' <primitive_type> ]

      WPF_Logic_Declaration
      );

   ----------------------------
   -- Node Class Definitions --
   ----------------------------

   subtype WLT_Term is Why_Node_Kind range
     WLT_Integer_Constant ..
     WLT_Protected_Term;

   subtype WLT_Constant is Why_Node_Kind range
     WLT_Integer_Constant ..
     WLT_Void_Litteral;

   subtype WLT_Arith_Op is Why_Node_Kind range
     WLT_Op_Add ..
     WLT_Op_Modulo;

   subtype WLP_Predicate is Why_Node_Kind range
     WLP_True_Litteral ..
     WLP_Protected_Predicate;

   subtype WLP_Primitive_Type is Why_Node_Kind range
     WT_Type_Int ..
     WT_Generic_Actual_Type_Chain;

   subtype WLP_Relation is Why_Node_Kind range
     WLP_Rel_Eq ..
     WLP_Rel_Ge;

   subtype WLD_Logic_Declaration is Why_Node_Kind range
     WLD_Type ..
     WLD_Goal;

   subtype WLD_Logic_Return_Type is Why_Node_Kind range
     WT_Type_Prop ..
     WT_Generic_Actual_Type_Chain;

   subtype WLD_Logic_Arg_Type is Why_Node_Kind range
     WT_Type_Int ..
     WT_Array_Type;

   subtype WPT_Simple_Value_Type is Why_Node_Kind range
     WT_Type_Int ..
     WT_Protected_Value_Type;

   subtype WPT_Value_Type is Why_Node_Kind range
     WT_Type_Int ..
     WT_Named_Arrow_Type;

   subtype WPT_Computation_Type is Why_Node_Kind range
     WT_Type_Int ..
     WT_Computation_Spec;

   subtype WPP_Prog is Why_Node_Kind range
     WPP_Prog_Constant ..
     WPP_Protected_Prog;

   subtype WPP_Infix is Why_Node_Kind range
     WPP_Op_Add ..
     WPP_Op_And_Then;

   subtype WPP_Prefix is Why_Node_Kind range
     WPP_Op_Minus ..
     WPP_Op_Not;

   subtype WPF_Declaration is Why_Node_Kind range
     WPF_Global_Binding ..
     WPF_Logic_Declaration;

end Why.Sinfo;
