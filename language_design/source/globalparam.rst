Subprogram Contracts
====================

Subprogram contracts may be more rigorous than in Ada.  Extra legality rules are applied to formal subprogram parameters and further restrictions may be applied to their use.  

Further aspects are provided in addition to the Ada ``Pre`` and ``Post``. ``Global``, ``Depends`` and ``Post_Cases`` facilitate an extended specification and a potentially more concise form of post condition.

Subprogram Parameter Specifications
-----------------------------------

Legality Rules
^^^^^^^^^^^^^^
#. A ``parameter_specification`` of a ``function_specification`` shall not have a mode of **out** or **in out** as a function is not allowed to have side-effects.

Further restrictions may be applied using ``Strict_Modes`` which extends the rules with:

2. A *formal parameter* of a subprogram of mode **in** or **in out** must be read directly or indirectly within the subprogram.
#. A *formal parameter* of a subprogram of mode **out** or **in out** must be updated directly or indirectly within the subprogram.


Global Aspects
--------------

A ``global_aspect`` is optional but if constructive, modular analysis or data abstraction is being used then a ``global_aspect`` may be required for every subprogram which references a ``global_item``.

A ``global_item`` denotes a *global_variable_*\ ``name`` (see Ada LRM 8.1) or a 
*data_abstraction_*\ ``name`` and may be used within in aspect definitions 
where stated in this manual. 

The global_aspect names the ``global_items`` that are read and, or, updated by the subprogram.
They are considered to have modes the same as *formal parameters*, **in**, **out** and **in out**.

The modes are specified by using specific selector names, ``Input``, ``Output`` and ``In_Out``
in a ``global_specification``.  
If one of these selector names is not given the default of ``Input`` is used. 
A ``global_aspect`` is a list of ''global_specifications``.
   
The ``global_aspect`` forms part of the specification of a subprogram explicitly stating the ``global_items`` that it references.  It is also used in the detection of illegal aliasing, preventing unintended use of a *global* variable by forgetting to declare a *local* variable, and the accidental hiding of a *global* variable buy a more *local* variable.

If none of the subprograms have a ``global_aspect``, then, for a complete program, using entire program analysis, it is possible to determine the *global* variables and check for illegal aliasing but not perform the other error preventative checks, nor the data_abstraction.

The use of ``global_aspects`` is recommended for newly written code to provide the full measure of error prevention.  If at least each subprogram declared immediately within a package or at library level has a ``global_aspect`` then for the subprograms declared within the body of another subprogram (nested), the ``global_aspect`` of the nested subprogram may be calculated from those of the enclosing subprogram.  To assist in such calculations a ``global_aspect`` may define that a subprogram does not reference any globals using a ``no_globals_specification``.

A ``global_aspect`` may be conditional.  If the ``condition`` is ``True`` then each ``global_item`` in the ``global_item_list`` following the **then** is read or updated depending on whether it is a conditional ``global_input_specification``, ``global_output_specification`` or ``global_in_out_specification``.
If the ``condition`` is ``False`` each ``global_item`` is not read or updated depending on the sort of ``global_specification``.


Syntax of a Global Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^
::

   global_aspect               ::= Global => global_specification_list
   global_specification_list   ::= global_specification
                                 | (global_specification {, global_specification})
   global_specification        ::= global_input_specification
                                 | global_output_specification
                                 | global_in_out_specification
                                 | no_globals_specification
   global_input_specification  ::= global_definition
                                 | (Input  => global_definition_list)
   global_output_specification ::= (Output => global_definition_list)
   global_in_out_specification ::= (In_Out => global_definition_list)
   no_globals_specification    ::= null
   global_definition_list      ::= global_definition
                                 | (global_definition {, global_definition})
   global_definition           ::= global_item
                                 | conditional_global
   conditional_global          ::= (if condition then global_item_list)
   global_item_list            ::= global_item
                                 | (global_item {, global_item}) 

where

   ``global_item``             ::= *global_variable_*\ ``name`` | *data_abstraction_*\ ``name``

 
Legality Rules
^^^^^^^^^^^^^^

#.  An ``aspect_specification`` of a subprogram may have at most one ``global_aspect``.
#.  There can be at most one of each of ``global_input_specification``, ``global_output_specification``, and ``global_in_out_specification`` in the same ``global_aspect``.
#.  A function subprogram may not have a ``global_output_specification`` or a ``global_in_out_specification`` in its ``global_aspect`` as a function is not permitted to have side-effects.
#.  A ``global_item`` appearing only in a ``global_input_specification`` is considered to be of mode **in**.  A ``global_item`` appearing only in a ``global_output_specification`` is considered to be of mode **out**.  A ``global_item`` which appears in both a ``global_input_specification`` and a ``global_output_specification`` or is only in a ``global_in_out_specification`` is considered to be of mode **in out**.
#.  The rules for reading or updating of a ``global_item`` of a particular mode are the same as for a *formal parameter* of the same mode including any restrictions placed on the interpretation of the modes.
#.  A ``global_item`` that appears in a ``global_in_out_specification`` may not appear in a ``global_input_specification`` or a ``global_output_specification`` within the same ``global_aspect`` except within the ``condition`` of a ``conditional_global``.
#. Other than appearing in a ``condition`` of a ``conditional_global``, a ``global_item`` may not appear more than once in the same ``global_specification``. 
#.  A ``global_item`` appearing in a ``condition`` of a ``conditional_global`` must appear in a ``global_input_specification`` or ``global_in_out_specification'' as a ``global_definition``, that is, not as a ``conditional_global``. 
#.  A ``global_item`` appearing in the ``global_aspect`` of a subprogram shall not have the same name, or be a subcomponent of an object with the same name as a formal parameter of the subprogram.
#.  A subprogram, shall not declare an entity of the same name as a ``global_item`` or the name of the object of which the ``global_item`` is a subcomponent, in its ``global_aspect`` immediately within the body of the subprogram.

Further restrictions may be applied:

8.  If the restriction ``No_Scope_Holes`` is applied then a subprogram, P, shall not declare an entity of the same name as a ``global_item`` or the name of the object of which the ``global_item`` is a subcomponent in its ``global_aspect_clause`` within a ``loop_statement`` or ``block_statement`` whose nearest enclosing program unit is P. 
#. The restriction ``Global_Variables_Are_Entire`` asserts that a ``global_item`` cannot be a subcomponent name.
#. The restriction ``No_Conditional_Globals`` prohibits the use of a ``conditional_global`` in a ``global_specification``.
#. The provision of ``global_aspects`` on all subprograms may be enforced by using the restriction ``Global_Aspects_Required``.  When this restriction is in force a subprogram which does not have an explicit ``global_aspect`` is considered to have a ``no_globals_specification``. -- ?? is this sensible or should we always insist on Global => null?? I hope not!!
#. A less stringent restriction is ``Global_Aspects_On_Non_Nested_Subprograms`` which requires a ``global_aspect`` on all subprograms not nested within another subprogram, although a ``global_aspect`` may still be placed on a nested subprogram (and require it if the body is a partial implementation.  A virtual global aspect is calculated from the body of each nested subprogram which does not have an explicit ``global_aspect``.  
 

Examples
^^^^^^^^

.. code-block:: ada

   with Global => null; -- Indicates that the subprogram does not read or update
                        -- any global items.
   with Global => V;    -- Indicates that V is a mode in global item.
   with Global => (X, Y, Z);  -- X, Y and Z are mode in global items.
   with Global => (I, (if I = 0 then (P, Q, R));  
                  -- I is a mode in global item and P, Q, and R are
                  -- conditional globals that are only read if I = 0.
   with Global => (Input => V); -- Indicates that V is a mode in global item.
   with Global => (Input => (X, Y, Z)); -- X, Y and Z are mode in global items.
   with Global => (Input => (I, (if I = 0 then (P, Q, R))); 
                   -- I is a mode in global item and P, Q, and R are 
                   -- conditional globals that are only read if I = 0.
   with Global => (Output => (A, B, C)); -- A, B and C are mode out global items.
   with Global => ((Input  => (I, J),
                   (Output => (A, B, C, I, (if I = 42 then D)))));
                  -- J is a mode in global item I is mode in out, A, B, C are mode out
                  -- and D is a conditional global that is only updated if I = 42.
   with Global =>  (In_Out => (P, Q, R, I, (if I = 42 then D)));
                  -- I, P, Q, R are global items of mode in out and D is a 
                  -- conditional global which is read and updated only if I = 42.
   with Global => ((Input  => K),
                   (Output => (A (K), R.F)));
                  -- K is a global item of mode in, A is a global array 
                  -- and only element A (K) is updated
                  -- the rest of the array is preserved.
                  -- R is a global record and only filed R.F is updated 
                  -- the remainder of the fields are preserved.
  with Global => ((Input  => (X, Y, Z)),
                  (Output => (A, B, C)),
                  (In_Out => (P, Q, R)));  
                  -- A global aspect with all types of global specification
   

Param Aspects
--------------

A ``param_aspect`` is an optional aspect used to denote that a formal parameter of a subprogram is only conditionally used or that only part of a formal parameter of a composite type is used.
Its syntax is similar to a global_aspect.

Syntax of a Param Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^
::

   param_aspect               ::= Param => param_specification_list
   param_specification_list   ::= param_specification
                                | (param_specification {, param_specification})
   param_specification        ::= param_input_specification
                                | param_output_specification
                                | param_in_out_specification
   param_input_specification  ::= global_definition
                                | (Input  => param_definition_list)
   param_output_specification ::= (Output => param_definition_list)
   param_in_out_specification ::= (In_Out => param_definition_list)
   param_definition_list      ::= param_definition
                                | (param_definition {, param_definition})
   param_definition           ::= formal_param
                                | conditional_param
   conditional_param          ::= (if condition then formal_param_list)
   formal_param_list          ::= formal_param
                                | (formal_param {, formal_param}) 
 
where

   ``formal_param``           ::= *formal parameter* as described in Ada LRM 6.1.


Legality Rules
^^^^^^^^^^^^^^

#.  An ``aspect_specification`` of a subprogram may have at most one ``param_aspect``.
#.  There can be at most one of each of ``param_input_specification``, ``param_output_specification``, and ``param_in_out_specification`` in the same ``param_aspect``.
#.  Every ``formal_param`` appearing in a ``param_aspect`` of a subprogram must be a *formal parameter* of the subprogram.
#.  A *formal parameter* which appears in a ``param_input_specification`` must be of mode **in** or mode **in out**.
#.  A *formal parameter* which appears in a ``param_output_specification`` must be of mode **out** or mode **in out**.
#.  A *formal parameter* which appears in a ``param_in_out_specification`` must be of mode **in out**.
#. Other than appearing in a ``condition`` of a ``conditional_param``, a *formal parameter* may not appear more than once in the same ``param_specification``. 
#.  A *formal parameter* appearing in a ``condition`` of a ``conditional_param`` must be of mode **in** or mode **in out**.
#.  A ``global_item`` of mode **in** or **in out** from a previous ``global_aspect`` within the same ``aspect_specification`` may appear in the ``condition`` of a ``conditional_param``.

Examples
^^^^^^^^

**To Do**


Anti-aliasing rules:
--------------------

**To Do**: the following text is copied from the SPARK 2005 LRM

The rules below prevent aliasing of variables in the execution of procedure subprograms.  See Section 6.1.2 for the definitions of imported, exported and entire variables.  (If a procedure subprogram has two procedure annotations as a consequence of refinement (c.f. Chapter 7), then in applying the rules to calls of a procedure P occurring outside the package in which P is declared, the annotation in the declaration should be employed; whereas in applying the rules to calls within the body of this package, the annotation in the procedure body or body stub should be used.)
1	If a variable V named in the global definition of a procedure P is exported, then neither V nor any of its subcomponents can occur as an actual parameter of P.
2	If a variable V occurs in the global definition of a procedure P, then neither V nor any of its subcomponents can occur as an actual parameter of P where the corresponding formal parameter is an exported variable.
3	If an entire variable V or a subcomponent of V occurs as an actual parameter in a procedure call statement, and the corresponding formal parameter is an exported variable, then neither V or an overlapping subcomponent of V can occur as another actual parameter in that statement. Two components are considered to be overlapping if they are elements of the same array or are the same component of a record (for example V.F and V.F) including subcomponents of the component (for example V.F and V.F.P). Note array elements are always considered to be overlapping and so, for example, V.A(I).P and V.A(J).Q are considered as overlapping.
Where one of these rules prohibits the occurrence of a variable V or any of its subcomponents as an actual parameter, the following constructs are also prohibited in this context:
1	a type conversion whose operand is a prohibited construct;
2	a qualified expression whose operand is a prohibited construct;
3	a prohibited construct enclosed in parentheses.



Post_Cases
----------

**To Do**
     A postcondition expressed as a set of disjoint cases covering
     all cases


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
^^^^^^^^^^^^^^

.. todo::
  Should the post cases be exclusive and should the check that exactly one
  guard is true be performed at subprogram entry?

Derives/Depends
---------------
**To Do**
     A declaration that describes the information flow of the subprogram


Syntax of a Derives Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^

**To Do**

::


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
is checked against the actual behaviour of the subprogram. If a subprogram does
not have such annotations, they are computed automatically and this
information can be used in the proofs of other parts of the programs.

If ``Globals_Unspecified`` is not given, the absence of
global/parameter/derives aspects means that the subprogram must not modify any
globals, and this is checked.
