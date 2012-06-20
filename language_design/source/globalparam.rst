Subprogram Contracts
====================

For a subprogram, the following aspects may be defined with an aspect
specification:

 Post_Cases
     Refined postcondition expressed as a set of disjoint cases covering
     all cases
 Global_In
     The global names that are read by the subprogram
 Global_Out
     The global names that are written by the subprogram
 Global_In_Out
     The global names that are read and written by the subprogram
 Param_In
     The parameter names that are read by the subprogram
 Param_Out
     The parameter names that are written by the subprogram
 Param_In_Out
     The parameter names that are read and written by the subprogram
 Derives
     A declaration that describes the information flow of the subprogram

The definition of the Global and the Param aspects is a comma-separated list
of names, including own variables, potentially guarded by a condition.



Syntax of a Derives Aspect
--------------------------

::

   post_cases          ::= with Post_Cases => (post_case_list)
   post_case_list      ::= post_case {, post_case_list}
   post_case           ::= boolean_expression => boolean_expression
   derives_aspect      ::= with Derives => (derives_clause_list)
   derives_clause_list ::=
       derives_clause {, derives_clause_list}
     | null
   derives_clause      ::= name_list => data_expression
   name_list           ::= name | name_paren_list
   name_paren_list     ::= (inner_name_list) | null
   inner_name_list     ::= name {, inner_name_list}
   data_expression     ::=
        [+] name_list
      | (if_data_expression)
      | (case_data_expression)
   if_data_expression  ::=
     if condition then data_expression
     {elsif condition then data_expression}
     [else data_expression]
   case_data_expression ::=
      case selecting_expression is
      case_expression_alternative {,
      case_data_expression_alternative}
   case_data_expression_alternative ::=
      when discrete_choice_list => data_expression

Legality rules
--------------

.. todo::
  Should the post cases be exclusive and should the check that exactly one
  guard is true be performed at subprogram entry?

The Param aspects should refine the regular Ada 2012 parameter modes, for
example when a parameter X appears in the Param_In_Out aspect, its parameter
mode should be ``in out``. Likewise, if a parameter X appears in the Param_In
and Param_Out aspects (e.g. with different conditions), its parameter mode
should be ``in out``.

Meaning
-------

Global and Param aspects describe the set of names that is read and/or
modified by the subprogram.

A Derives aspect can be used to describe the information flow of the
subprogram, that is, from which names a modified name derives its new value. A
"+" preceding a name list means that the name derives from the given name list
and itself.

Global and Param aspects are never needed when a Derives aspect has been
given. If an implementation for the subprogram exists, the actual set of
modified names should match the set of names that is declared using these
aspects, and the information flow should be correct with respect to the
implementation.

The aspects discussed in this section do not have any dynamic semantics.

Examples
--------

.. highlight:: ada

The following example illustrates simple and advanced uses of Global and
Param aspects::

    type A is array (Integer range 1 .. 10) of Integer;

    type R is record
       F_1 : A;
       F_2 : Integer;
    end;

    G : Integer;

    --  These aspects describe that P always reads global variable G, --
    --  always reads and writes parameter I, and reads and writes the Ith cell
    --  of field F_1 of the argument R_Arg, but only when I is equal to 0.

    --  Note that the derives aspect contains the most precise information,
    --  and the Global_In and Param_In_Out are superfluous. The "else null"
    --  part is also not necessary.

    procedure P (I : in out Integer; R_Arg : in out R)
    with
      Global_In => G,
      Param_In_Out => (I, (if I = 0 then R_Arg.F_1 (I))),
      Derives =>
         (I => +G,
          R_Arg.F_1 (I) => (if I = 0 then G));


Generative and Declarative mode
-------------------------------

Global and Param aspects can be computed automatically when the
implementation for a subprogram is given. One can choose on a per-package
basis whether one wants globals to be computed automatically::

   package P
      with Globals_Unspecified
   is

In this mode, when a subprogram has a global/parameter/derives annotation, it
is checked against the actual behavior of the subprogram. If a subprogram does
not have such annotations, they are computed automatically and this
information can be used in the proofs of other parts of the programs.

If ``Globals_Unspecified`` is not given, the absence of
global/parameter/derives aspects means that the subprogram must not modify any
globals, and this is checked.
