------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            W H Y - S I N F O                             --
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
      --  in the logic space; so they are declared here to allow proper
      --  definition of subtypes for the corresponding node classes.

      --  0.1. Purely logic, return type only:
      ----------------------------------------

      W_Type_Prop,
      --  <type_prop> ::= 'prop'

      --  0.2. Primitive types, both valid in logic/program space:
      ------------------------------------------------------------

      W_Type_Int,
      --  <type_int> ::= 'int'

      W_Type_Bool,
      --  <type_bool> ::= 'bool'

      W_Type_Real,
      --  <type_real> ::= 'real'

      W_Type_Unit,
      --  <type_unit> ::= 'unit'

      W_Abstract_Type,
      --  <abstract_type> ::= <identifier>

      W_Generic_Formal_Type,
      --  <generic_formal_type> ::= "'" <identifier>

      W_Generic_Actual_Type_Chain,
      --  <generic_actual_type_chain> ::=
      --     <primitive_type> (<primitive_type>, )* <identifier>

      --  0.3. Only valid in program space:
      -------------------------------------

      W_Array_Type,
      --  <array_type> ::= <primitive_type> 'array'

      W_Ref_Type,
      --  <ref_type> ::= <primitive_type> 'ref'

      W_Protected_Value_Type,
      --  <protected_value_type> ::= '(' <value_type> ')'

      W_Arrow_Type,
      --  <arrow_type> ::= [<identifier> ':'] <simple_value_type>
      --                          '->' <computation_type>

      W_Computation_Spec,
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
      --             | <identifier>
      --             | <label_identifier>
      --             | <operation>
      --             | <named_term>
      --             | <conditional_term>
      --             | <binding_term>
      --             | <protected_term>

      --  <constant> ::= <integer_constant>
      --                 | <real_constant>
      --                 | <true_literal>
      --                 | <false_literal>
      --                 | <void_literal>

      W_Integer_Constant,

      W_Real_Constant,

      W_True_Literal,
      --  <true_literal> ::= 'true'

      W_False_Literal,
      --  <false_literal> ::= 'false'

      W_Void_Literal,
      --  <void_literal> ::= 'void'

      W_Term_Identifier,

      W_Arith_Operation,
      --  <arith_operation> ::= <term> <arith_op> <term>

      W_Negative_Term,
      --  <negative_term> ::= '-' <term>

      W_Label_Identifier,
      --  <label_identifier> ::= <identifier> [ @ [ <identifier> ] ]

      W_Operation,
      --  <operation> ::= <identifier> '(' <term> (',' <term>)* ')'

      W_Named_Term,
      --  <named_term> ::= <label_identifier> '[' <term> ']'

      W_Conditional_Term,
      --  <logic_conditional_term> ::= 'if' <term> 'then' <term> 'else' <term>

      W_Matching_Term,
      --  <matching_term> ::=
      --    'match' <term> 'with' matchcase [ matchcase ]* 'end'

      W_Binding_Term,
      --  <logic_binding> ::= 'let' <identifier> '=' <term> 'in' <term>

      W_Protected_Term,
      --  <protected_term> ::= '(' <term> ')'

      --  <arith_op> ::= <op_add>
      --                 | <op_substract>
      --                 | <op_multiply>
      --                 | <op_divide>
      --                 | <op_modulo>

      W_Op_Add,
      --  <op_add> ::= '+'

      W_Op_Substract,
      --  <op_substract> ::= '-'

      W_Op_Multiply,
      --  <op_multiply> ::= '*'

      W_Op_Divide,
      --  <op_divide> ::= '/'

      W_Op_Modulo,
      --  <op_modulo> ::= '%'

      --  1.2. Predicates:
      --------------------

      --  <predicate> ::= <true_literal>
      --                  | <false_literal>
      --                  | <predicate_identifier>
      --                  | <predicate_instance>
      --                  | <related_terms>
      --                  | <implication>
      --                  | <equivalence>
      --                  | <disjunction>
      --                  | <conjonction>
      --                  | <negation>
      --                  | <conditional_pred>
      --                  | <binding_pred>
      --                  | <universal_quantif>
      --                  | <existential_quantif>
      --                  | <named_predicate>
      --                  | <protected_predicate>

      W_True_Literal_Pred,
      --  <true_literal> ::= 'true'

      W_False_Literal_Pred,
      --  <false_literal> ::= 'false'

      W_Predicate_Identifier,
      --  <predicate_identifier> ::= <identifier>

      W_Predicate_Instance,
      --  <predicate_instance> ::= <identifier> '(' <term>+ ')'

      W_Related_Terms,
      --  <related_terms> ::= <term> <relation> <term> [ <relation> <term> ]

      W_Implication,
      --  <implication> ::= <predicate> '->' <predicate>

      W_Equivalence,
      --  <predicate> '<->' <predicate>

      W_Disjonction,
      --  <disjonction> ::= <predicate> 'or' <predicate>

      W_Conjonction,
      --  <conjonction> ::= <predicate> 'and' <predicate>

      W_Negation,
      --  <negation> ::= 'not' <predicate>

      W_Conditional_Pred,
      --  <conditional_pred> ::= if <term> then <predicate> else <predicate>

      W_Binding_Pred,
      --  <binding_pred> ::= let <identifier> = <term> in <predicate>

      W_Universal_Quantif,
      --  <universal_quantif> ::=
      --     'forall' <identifier> (, <identifier>)* ':' <primitive_type>
      --        [ <triggers> ] '.' <predicate>

      W_Existential_Quantif,
      --  <existential_quantif> ::=
      --     'exists' <identifier> (, <identifier>*) ':' <primitive_type> '.'
      --        <predicate>

      W_Named_Predicate,
      --  ( <identifier> | <string> ) ':' <predicate>

      W_Protected_Predicate,
      --  <protected_predicate> ::= '(' <predicate> ')'

      W_Pattern,
      --  <pattern> ::= ident [ '(' ident [',' <ident> ] ')' ]

      W_Match_Case,
      --  <matchcase> ::= '|' <pattern> '->' <term>

      W_Triggers,
      --  <triggers> ::= '[' <trigger> ('|' <trigger>) * ']'

      W_Trigger,
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

      W_Rel_Eq,
      --  <rel_eq> ::= '='

      W_Rel_Ne,
      --  <rel_ne> ::= '<>'

      W_Rel_Lt,
      --  <rel_lt> ::= '<'

      W_Rel_Le,
      --  <rel_le> ::= '<='

      W_Rel_Gt,
      --  <rel_gt> ::= '>'

      W_Rel_Ge,
      --  <rel_ge> ::= '>='

      --  1.3. Logic declarations:
      ----------------------------

      --  <logic_declaration_class> ::= <type>
      --                                | <logic>
      --                                | <function>
      --                                | <predicate_definition>
      --                                | <inductive_definition>
      --                                | <axiom>
      --                                | <goal>

      W_Type,
      --  <type> ::=
      --    [ <external> ] 'type' [ <type_parameters> ] <identifier>
      --    [ = <type_definition>]

      --  <type_parameters> ::=
      --  "'" <identifier> | '(' "'" <identifier> (',' "'" <identifier>)+ ')'

      W_Logic,
      --  <logic> ::=
      --  [ <external> ] 'logic' <identifier> [',' <identifier>]*
      --               ':' <logic_type>

      W_Function,
      --  <function> ::=
      --  'function' <identifier> '(' <logic_binder> [',' <logic_binder>]* ')'
      --                          ':' <primitive_type>
      --  '=' <term>

      W_Predicate_Definition,
      --  <predicate_Definition> ::=
      --  'predicate' <identifier> '(' <logic_binder> [',' <logic_binder>]* ')'
      --  '=' <predicate>

      W_Inductive,
      --  <inductive> ::= 'inductive' <identifier> ':' <logic_type> '='
      --        <inductive_case>+

      W_Axiom,
      --  <axiom> ::= 'axiom' <identifier> ':' <predicate>

      W_Goal,
      --  <goal> ::= 'goal' <identifier> ':' <predicate>

      W_External,
      --  <external> ::= 'external'

      W_Logic_Type,
      --  <logic_type> ::=
      --  <logic_arg_type> (',' logic_arg_type)* '->' <logic_return_type>

      --  <logic_arg_type> ::= <primitive_type> | <array_type>

      --  <logic_return_type> ::= <type_prop> | <primitive_type>

      W_Logic_Binder,
      --  <logic_binder> ::= <identifier> ':' <primitive_type>

      W_Inductive_Case,
      --  <inductive_case> ::= '|' <identifier> : <predicate>

      ----------------------
      -- Type Definitions --
      ----------------------
      --  Type definitions are introduced by an extension of the Why manual:
      --  http://hal.inria.fr/docs/00/48/73/62/PDF/RR-7128.pdf
      --  <type_definition> ::= <logic_type> | <adt_definition>
      W_Transparent_Type_Definition,

      W_Adt_Definition,
      --  <adt_definition> ::=
      --    <constructor_declaration> [ constructor_declaration ]*

      W_Constr_Decl,
      --    <constructor_declaration> ::=
      --    '|' identifier
      --          [ '(' <primitive_type> [',' <primitive_type>]* ')' ]

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
      --                   | <arrow_type>

      --  <computation_type> ::= <computation_spec> | <value_type>

      W_Effects,
      --  <effects> ::= [ 'reads' <identifier> (',' <identifier>)* ]
      --                [ 'writes' <identifier> (',' <identifier>)* ]
      --                [ 'raises' <identifier> (',' <identifier>)* ]

      W_Precondition,
      --  <precondition> ::= <assertion>

      W_Postcondition,
      --  <postcondition> ::= <assertion> <exn_condition>*

      W_Exn_Condition,
      --  <exn_condition> ::= '|' <identifier> '=>' <assertion>

      W_Assertion,
      --  <assertion> ::= <predicate> [ 'as' <identifier> ]

      --  2.2. Annotated programs:
      ----------------------------

      --  <prog> ::= <prog_constant>
      --             | <prog_identifier>
      --             | <deref>
      --             | <assignment>
      --             | <array_access>
      --             | <array_update>
      --             | <infix_call>
      --             | <prefix_call>
      --             | <binding_prog>
      --             | <binding_ref>
      --             | <conditional_prog>
      --             | <while_loop>
      --             | <statement_sequence>
      --             | <label>
      --             | <assertion>
      --             | <post_assertion>
      --             | <opaque_assertion>
      --             | <fun_def>
      --             | <binding_fun>
      --             | <binding_rec>
      --             | <prog_sequence>
      --             | <raise_statement>
      --             | <raise_statement_with_parameters>
      --             | <try_block>
      --             | <unreachable_code>
      --             | <begin_block>
      --             | <protected_prog>

      W_Prog_Constant,
      --  <prog_constant> ::= <constant>

      W_Prog_Identifier,
      --  <prog_identifier> ::= <identifier>

      W_Deref,
      --  <deref> ::= '!' <identifier>

      W_Assignment,
      --  <assignment> ::= <identifier> ':=' <prog>

      W_Array_Access,
      --  <array_access> ::= <identifier> '[' <prog> ']'

      W_Array_Update,
      --  <array_update> ::= <identifier> '[' <prog> ']' ':=' <prog>

      W_Infix_Call,
      --  <infix_call> ::= <prog> <infix> <prog>

      W_Prefix_Call,
      --  <prefix_call> ::= <prefix> <prog>

      W_Binding_Prog,
      --  <binding_prog> ::= 'let' <identifier> '=' <prog> in <prog>

      W_Binding_Ref,
      --  <binding_ref> ::= 'let' <identifier> '=' ref <prog> in <prog>

      W_Conditional_Prog,
      --  <conditional_prog> ::= 'if' <prog> 'then' <prog> [ 'else' <prog>]

      W_While_Loop,
      --  <while_loop> ::= 'while' <prog> 'do' [ <loop_annot> ] <prog> 'done'

      W_Statement_Sequence,
      --  <statement_sequence> ::= <prog> (';' <prog>)+

      W_Label,
      --  <label> ::= <identifier> : <prog>

      W_Assert,
      --  <assert> ::= 'assert' ('{' <assertion> '}')+ ';' <prog>

      W_Post_Assertion,
      --  <post_assertion> ::= <prog> '{' <postcondition> '}'

      W_Opaque_Assertion,
      --  <opaque_assertion> ::= <prog> '{{' <postcondition> '}}'

      W_Fun_Def,
      --  <fun_def> ::= 'fun' <binders> '->' '{' <precondition> '}' <prog>

      W_Binding_Fun,
      --  <binding_fun> ::=
      --  'let' <identifier> <binders> '='
      --    '{' <precondition> '}' <prog> 'in' <prog>

      W_Binding_Rec,
      --  <binding_rec> ::= 'let' 'rec' <recfun> [ 'in' <prog> ]

      W_Prog_Call,
      --  <prog> <prog>+

      W_Raise_Statement,
      --  <raise_statement> ::= 'raise' <identifier> [ ':' <value_type> ]

      W_Raise_Statement_With_Parameters,
      --  <raise_statement_with_parameters> ::=
      --     'raise' '(' <identifier> <prog> ')' [ ':' <value_type> ]

      W_Try_Block,
      --  <try_block> ::= 'try' <prog> 'with' <handler> (',' <handler>)* 'end'

      W_Unreachable_Code,
      --  <unreachable_code> ::= 'absurd' [ ':' <value_type> ]

      W_Begin_Block,
      --  <begin_block> ::= begin <prog> end

      W_Protected_Prog,
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

      W_Op_Add_Prog,
      --  <op_add> ::= '+'

      W_Op_Substract_Prog,
      --  <op_substract> ::= '-'

      W_Op_Multiply_Prog,
      --  <op_multiply> ::= '*'

      W_Op_Divide_Prog,
      --  <op_divide> ::= '/'

      W_Op_Mod_Prog,
      --  <op_mod> ::= '%'

      W_Op_Eq_Prog,
      --  <op_eq> ::= '='

      W_Op_Ne_Prog,
      --  <op_divide> ::= '<>'

      W_Op_Lt_Prog,
      --  <op_lt> ::= '<'

      W_Op_Le_Prog,
      --  <op_le> ::= '<='

      W_Op_Gt_Prog,
      --  <op_gt> ::= '>'

      W_Op_Ge_Prog,
      --  <op_ge> ::= '>='

      W_Op_Or_Else_Prog,
      --  <op_or_else> ::= '||'

      W_Op_And_Then_Prog,
      --  <op_and_then> ::= '&&'

      --  <prefix> ::= <op_minus> | <op_not>

      W_Op_Minus_Prog,
      --  <op_minus> ::= '-'

      W_Op_Not_Prog,
      --  <op_not> ::= 'not'

      W_Binder,
      --  <binder> ::=
      --     '(' <identifier> [',' <identifier>]+ ':' <value_type> ')'

      W_Recfun,
      --  <recfun> ::= <identifier> <binders> ':' <value_type>
      --     '{' 'variant' <wf_arg> '}' = '{' <precondition> '}' <prog>

      W_Loop_Annot,
      --  <loop_annot> ::= '{' [ 'invariant' <assertion> ]
      --                       [ 'variant' <wf_arg> ] '}'

      W_Wf_Arg,
      --  <wf_arg> ::= <term> [ 'for' <identifier> ]

      W_Handler,
      --  <handler> ::= <identifier> [<identifier>] '->' <prog>

      --  2.3. Input files:
      ---------------------

      W_File,
      --  <file> ::= <declaration>*

      --  <declaration> ::= <global_binding>
      --                    | <global_rec_binding>
      --                    | <parameter_declaration>
      --                    | <exception_declaration>
      --                    | <logic_declaration>

      W_Global_Binding,
      --  <global_binding> ::=
      --    'let' <identifier> [ <binders> ] '=' '{' <precondition> '}' <prog>

      W_Global_Rec_Binding,
      --  <global_rec_binding> ::= 'let' 'rec' <recfun>

      W_Parameter_Declaration,
      --  <parameter_declaration> ::=
      --     [ <external> ] parameter <identifier>,+ ':' <value_type>

      W_Exception_Declaration,
      --  <exception_declaration> ::=
      --     'exception' <identifier> [ 'of' <primitive_type> ]

      W_Logic_Declaration
      );

   ----------------------------
   -- Node Class Definitions --
   ----------------------------

   subtype W_Term is Why_Node_Kind range
     W_Integer_Constant ..
     W_Protected_Term;

   subtype W_Constant is Why_Node_Kind range
     W_Integer_Constant ..
     W_Void_Literal;

   subtype W_Arith_Op is Why_Node_Kind range
     W_Op_Add ..
     W_Op_Modulo;

   subtype W_Predicate is Why_Node_Kind range
     W_True_Literal ..
     W_Protected_Predicate;

   subtype W_Primitive_Type is Why_Node_Kind range
     W_Type_Int ..
     W_Generic_Actual_Type_Chain;

   subtype W_Relation is Why_Node_Kind range
     W_Rel_Eq ..
     W_Rel_Ge;

   subtype W_Logic_Declaration_Class is Why_Node_Kind range
     W_Type ..
     W_Goal;

   subtype W_Logic_Return_Type is Why_Node_Kind range
     W_Type_Prop ..
     W_Generic_Actual_Type_Chain;

   subtype W_Logic_Arg_Type is Why_Node_Kind range
     W_Type_Int ..
     W_Array_Type;

   subtype W_Simple_Value_Type is Why_Node_Kind range
     W_Type_Int ..
     W_Protected_Value_Type;

   subtype W_Value_Type is Why_Node_Kind range
     W_Type_Int ..
     W_Arrow_Type;

   subtype W_Computation_Type is Why_Node_Kind range
     W_Type_Int ..
     W_Computation_Spec;

   subtype W_Prog is Why_Node_Kind range
     W_Prog_Constant ..
     W_Protected_Prog;

   subtype W_Infix is Why_Node_Kind range
     W_Op_Add_Prog ..
     W_Op_And_Then_Prog;

   subtype W_Prefix is Why_Node_Kind range
     W_Op_Minus_Prog ..
     W_Op_Not_Prog;

   subtype W_Declaration is Why_Node_Kind range
     W_Global_Binding ..
     W_Logic_Declaration;

   subtype W_Any_Node is Why_Node_Kind range
     W_Identifier ..
     W_Logic_Declaration;

   subtype W_Type_Definition is Why_Node_Kind range
     W_Transparent_Type_Definition ..
     W_Adt_Definition;

end Why.Sinfo;
