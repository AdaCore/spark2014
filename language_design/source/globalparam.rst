Subprogram Contracts
====================

Subprogram contracts may be more rigorous than in Ada.  Extra legality rules are applied to formal subprogram parameters and further restrictions may be applied to their use.

Aspects are provided in addition to the Ada ``Pre`` and ``Post``. ``Global``, ``Depends`` and ``Post_Cases`` facilitate an extended specification and a potentially more concise form of post condition.

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

The ``global_aspect`` names the ``global_items`` that are read and, or, updated
by the subprogram.  They are considered to have modes the same as *formal
parameters*, **in**, **out** and **in out**.

A ``global_item`` denotes a *global_variable_*\ ``name`` (see Ada LRM 8.1) or a
*data_abstraction_*\ ``name`` (see :ref:`abstraction of global state`) and may
be used within aspect definitions where stated in this manual.

.. todo::
   Introduce constructive / modular analysis before this point, in the
   Language Subset section.

A ``global_aspect`` is optional but if constructive, modular analysis or data abstraction is being used then a ``global_aspect`` may be required for every subprogram which references a ``global_item``.

The modes are specified by using specific selector names, ``Input``, ``Output`` and ``In_Out``
in a ``global_specification``.
If one of these selector names is not given the default of ``Input`` is used.
A ``global_aspect`` is a list of ``global_specifications``.

The ``global_aspect`` forms part of the specification of a subprogram explicitly stating the ``global_items`` that it references.  It is also used in the detection of illegal aliasing, preventing unintended use of a *global* variable by forgetting to declare a *local* variable, and the accidental hiding of a *global* variable by a more *local* variable.

.. todo::
   The following may not belong here. It could be simpler to give the big
   picture of what is in SPARK or not, and the various profiles, in the
   Language Subset section.

If none of the subprograms have a ``global_aspect``, then, for a complete program, using entire program analysis, it is possible to determine the *global* variables and check for illegal aliasing but not perform the other error preventative checks, nor the data_abstraction.

.. todo::
   Same here. This paragraph is about tools really, not the semantics of
   global aspects.

The use of ``global_aspects`` is recommended for newly written code to provide the full measure of error prevention.  If at least each subprogram declared immediately within a package or at library level has a ``global_aspect`` then for the subprograms declared within the body of another subprogram (nested), the ``global_aspect`` of the nested subprogram may be calculated from those of the enclosing subprogram.  To assist in such calculations a ``global_aspect`` may define that a subprogram does not reference any globals using a ``no_globals_specification``.

A ``global_aspect`` may be conditional.  If the ``condition`` is ``True`` then each ``global_item`` in the ``global_item_list`` following the **then** is read or updated depending on whether it is a conditional ``global_input_specification``, ``global_output_specification`` or ``global_in_out_specification``.
If the ``condition`` is ``False`` each ``global_item`` is not read or updated depending on the sort of ``global_specification``.


Syntax of a Global Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^
::

   global_aspect               ::= Global => global_specification_list
   global_specification_list   ::= global_specification
                                 | (global_specification {, global_specification})
   global_specification        ::= mode_selector global_definition_list
                                 | no_globals_specification
   no_globals_specification    ::= null
   global_definition_list      ::= global_definition
                                 | (global_definition {, global_definition})
   global_definition           ::= global_item
                                 | conditional_global
   conditional_global          ::= (if condition then global_item_list)
   global_item_list            ::= global_item
                                 | (global_item {, global_item})
   mode_selector               ::= [Input =>] | Output => | In_Out => 

where

   ``global_item``             ::= *global_variable_*\ ``name`` | *data_abstraction_*\ ``name``

Note that ``global_specification_list``, ``no_globals_specification``, ``global_definition_list``, ``global_definition``, ``global_item``, ``conditional_global`` and ``global_item_list`` are all forms of ``expression`` and, therefore, may be parenthesised. 

Legality Rules
^^^^^^^^^^^^^^

#.  An ``aspect_specification`` of a subprogram may have at most one ``global_aspect``.
#.  A ``global_specification`` with an empty ``mode_selector`` is considered to have the selector ``Input =>``. 
#.  There can be at most one of each of a ``global_specification``, with a ``mode_selector`` of ``Input =>``, ``Output =>`` and ``In_Out =>``.
#.  An ``aspect_specification`` may only have one ``no_globals_specification`` and this excludes the use of any other ``global_specification`` within the same ``global_aspect``.
#.  A function subprogram may not have a ``mode_selector`` of ``Output =>`` or ``In_Out =>`` in its ``global_aspect`` as a function is not permitted to have side-effects.
#.  A ``global_item`` appearing in a ``global_specification`` with ``mode selector`` of ``Input =>``, is considered to be of mode **in**.  A ``global_item`` appearing in a ``global_specification`` with a ``mode selector`` of ``Output =>`` is considered to be of mode **out**.  A ``global_item`` which appears in a ``global_specification`` with a ``mode selector`` of ``In_Out =>`` is considered to be of mode **in out**.
#.  The rules for reading or updating of a ``global_item`` of a particular mode are the same as for a *formal parameter* of the same mode including any restrictions placed on the interpretation of the modes.
#.  A ``global_item`` may not appear in more than one ``global_specification`` or more than once within a single ``global_specification`` other than appearing in a ``condition`` of a ``conditional_global``. Different subcomponents of a composite object may appear more than once and, for array subcomponents, they may be the same indexed subcomponent. 
#.  The only *variables* that may appear in the ``condition`` of a ``conditional_global`` within a ``global_aspect`` of a subprogram must be either a *global_variable_*\ ``name`` which is a ``global_item`` of the subprogram or a *formal parameter* of mode **in** or **in out** of the subprogram. 
#.  A *global_variable_*\ ``name`` appearing in a ``condition`` of a ``conditional_global`` must appear as a ``global_definition`` within a ``global_specification``, that is, not as a ``conditional_global``. It must have a mode of **in** or **in out**.
#.  A ``global_item`` appearing in the ``global_aspect`` of a subprogram shall not have the same name, or be a subcomponent of an object with the same name as a formal parameter of the subprogram.
#.  A subprogram, shall not declare, immediately within its body, an entity of the same name as a ``global_item`` or the name of the object of which the ``global_item`` is a subcomponent, appearing in the ``global_aspect`` of the subprogram.

.. todo:: Further rules involving subcomponents within a global aspect. Here is a first attempt but it probably requires more thought:

13. An object and its subcomponents cannot both be mentioned in the same ``global_aspect``. This rule also applies to subcomponents of subcomponents of an object.
#. If a subcomponent name appears in a ``global_specification`` with a ``mode_selector`` of ``Output =>`` or ``In_Out =>`` then just that subcomponent is considered to be updated and the other subcomponents of the object are preserved (unchanged).  If more than one subcomponent of the same object appears in such a ``global_specification`` then all the mentioned subcomponents are considered to be updated and remaining subcomponents of the object preserved.
#. If a subcomponent name appears in a ``global_specification`` with a ``mode_selector`` of ``Input =>`` or ``In_Out =>`` then just that subcomponent is considered to be read.  If more than one subcomponent of the same object appears in such a ``global_specification`` then all the mentioned subcomponents are considered to be read.
#. If an object has subcomponents which are array elements and more than one of these elements are referenced in a ``global_aspect`` then more than one element may have the same index.  This may give rise to conflicts.  For example: Global => (Input  => A (I), Output => A (J)); if I = J then A(I) is in out.  I am sure conflicts such as these can be resolved - they just require a bit more thought.
 

Further restrictions may be applied:

17.  If the restriction ``No_Scope_Holes`` is applied then a subprogram, P, shall not declare an entity of the same name as a ``global_item`` or the name of the object of which the ``global_item`` is a subcomponent in its ``global_aspect_clause`` within a ``loop_statement`` or ``block_statement`` whose nearest enclosing program unit is P. 
#. The restriction ``Global_Variables_Are_Entire`` asserts that a ``global_item`` cannot be a subcomponent name.
#. The restriction ``No_Conditional_Globals`` prohibits the use of a ``conditional_global`` in a ``global_specification``.

.. todo:: In restriction 15, is this the assumption of no Global aspect implies Global => null sensible or should we always insist on Global => null?? I hope not!! Re-automate numbering after removing this todo.

20. The provision of ``global_aspects`` on all subprograms may be enforced by using the restriction ``Global_Aspects_Required``.  When this restriction is in force a subprogram which does not have an explicit ``global_aspect`` is considered to have a ``no_globals_specification``. 
#. A less stringent restriction is ``Global_Aspects_On_Non_Nested_Subprograms`` which requires a ``global_aspect`` on all subprograms not nested within another subprogram, although a ``global_aspect`` may still be placed on a nested subprogram (and require it if the body is a partial implementation.  A virtual global aspect is calculated from the body of each nested subprogram which does not have an explicit ``global_aspect``.  
#. The style restriction, ``No_Default_Global_Modes_On_Procedures``, disallows an empty ``mode_selector`` within a procedure ``aspect_specification``. An explicit ``Input =>`` must be given.  A function ``aspect_specification`` may have a global_specification with an empty ``mode_selector``. 
 

Examples
^^^^^^^^

.. code-block:: ada

   with Global => null; -- Indicates that the subprogram does not read or update
                        -- any global items.
   with Global => V;    -- Indicates that V is a mode in global item.
                        -- This style can only be used in a function aspect specification
   with Global => (X, Y, Z);  -- X, Y and Z are mode in global items.
                        -- This style can only be used in a function aspect specification
   with Global => (I, (if I = 0 then (P, Q, R));
                  -- I is a mode in global item and P, Q, and R are
                  -- conditional globals that are only read if I = 0.
                  -- This style can only be used in a function aspect specification
   with Global => (Input => V); -- Indicates that V is a mode in global item.
   with Global => (Input => (X, Y, Z)); -- X, Y and Z are mode in global items.
   with Global => (Input => (I, (if I = 0 then (P, Q, R)));
                   -- I is a mode in global item and P, Q, and R are
                   -- conditional globals that are only read if I = 0.
   with Global => (Output => (A, B, C)); -- A, B and C are mode out global items.
   with Global => (Input  => (I, J),
                   Output => (A, B, C, I, (if I = 42 then D))));
                  -- J is a mode in global item I is mode in out, A, B, C are mode out
                  -- and D is a conditional global that is only updated if I = 42.
   with Global =>  (In_Out => (P, Q, R, I, (if I = 42 then D)));
                  -- I, P, Q, R are global items of mode in out and D is a
                  -- conditional global which is read and updated only if I = 42.
   with Global => (Input  => K,
                   Output => (A (K), R.F));
                  -- K is a global item of mode in, A is a global array 
                  -- and only element A (K) is updated
                  -- the rest of the array is preserved.
                  -- R is a global record and only filed R.F is updated
                  -- the remainder of the fields are preserved.
  with Global => (Input  => (X, Y, Z),
                  Output => (A, B, C),
                  In_Out => (P, Q, R));  
                  -- A global aspect with all types of global specification


Param Aspects
--------------

A ``param_aspect`` is an optional aspect used to denote that a formal parameter of a subprogram is only conditionally used or that only part of a formal parameter of a composite type is used.
Its syntax is similar to a global_aspect.

Syntax of a Param Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^
::

   param_aspect               ::= Param => param_specification_list
   param_specification_list   ::= (param_specification {, param_specification})
   param_specification        ::= mode_selector param_definition_list
   param_definition_list      ::= param_definition
                                | (param_definition {, param_definition})
   param_definition           ::= formal_param
                                | conditional_param
   conditional_param          ::= (if condition then formal_param_list)
   formal_param_list          ::= formal_param
                                | (formal_param {, formal_param})

where

   ``formal_param``           ::= *formal parameter* as described in Ada LRM 6.1.

Note that ``param_specification_list``, ``param_definition_list``, ``param_definition``, ``conditional_param``, ``formal_param_list`` and ``formal_param`` are all forms of ``expression`` and so may be parenthesised. 


Legality Rules
^^^^^^^^^^^^^^

#.  An ``aspect_specification`` of a subprogram may have at most one ``param_aspect``.
#.  There can be at most one of each of ``param_specification``, with a ``mode_selector`` of ``Input =>``, ``Output =>``, and ``In_Out =>`` in the same ``param_aspect``.
#.  Every ``formal_param`` appearing in a ``param_aspect`` of a subprogram must be a *formal parameter* of the subprogram.
#.  A *formal parameter* which appears in a ``param_specification`` with a ``mode_selector`` of ``Input =>`` must be of mode **in** or mode **in out**.
#.  A *formal parameter* which appears in a ``param_specification`` with a ``mode_selector`` of ``Output =>`` must be of mode **out** or mode **in out**.
#.  A *formal parameter* which appears in a ``param_specification`` with a ``mode_selector`` of ``In_Out =>`` must be of mode **in out**.
#.  A *formal parameter* may not appear in more than one ``param_specification`` or more than once within a single ``param_specification`` other than appearing in a ``condition`` of a ``conditional_param``. Different subcomponents of a composite object may appear more than once and, for array subcomponents, they may be the same indexed subcomponent. 
#.  The only *variables* appearing in a ``condition`` of a ``conditional_param`` of a ``aspect_specification`` of a subprogram must be either be a *formal parameter* of mode **in** or mode **in out** or a *global_variable_*\ ``name`` of mode **in** or **in out** from a previous ``global_aspect`` within the same ``aspect_specification``.

Further restrictions may be applied:

9. The use of ``param_aspects`` may be excluded by the restriction ``No_Param_Aspects``.
#. The restriction ``No_Default_Param_Modes_On_Procedures`` may be used to prohibit the use of an empty ``mode_selector`` in a procedure ``aspect_specification''.

Examples
^^^^^^^^

.. code-block:: ada

   procedure P (R : in out A_Record_Type)
   with Param => (Input  => R.F,
                  Output => R.E);
   -- The Param aspect states that only field F of the record R is read
   -- and that only field E is updated; the values remainder of the 
   -- record fields are preserved. 

   procedure Q (A : in out An_Array_Type)
   with Param => (Input  => A.(I),
                  Output => A (J));
   -- The Param aspect states that only element I of the array A is read
   -- and that only element J is updated; the values remainder of the 
   -- array elements are preserved. Note: I may equal J. 

   procedure G (A : in out An_Array_Type)
   with Global => (Input  => K),
        Param  => (Input  => A.(I),
                   Output => (if K = 10 then A (J)));
   -- The Param aspect states that only element I of the array A is read
   -- and element J is only updated if the global I = 10; 
   -- the values remainder of the  array elements are preserved including
   -- A (J) if K /= 10. Note: I, J and K may all be equal. 


Dependency Aspects
------------------

Dependency aspects define a dependency relation for a procedure subprogram which may be given in the ``aspect_specification`` of the subprogram.  The dependency relation is used in information flow analysis.

.. todo:: Need to extend this description some more.

Syntax of a Dependency Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

   dependency_aspect      ::= Depends => dependency_list
   dependency_list        ::= (dependency_clause {, dependency_clause})
   dependency_clause      ::= export_list =>[+] import_list
   export_list            ::= null
                            | function_designator'Result
                            | dependency_item
                            | (dependency_item {, dependency_item})
   import_list            ::= import_item
                            | (import_item {, import_item})
                            | null
   import_item            ::= dependency_item
                            | conditional_dependency
   conditional_dependency ::= (if condition then import_list)


where
  ``dependency_item`` ::= ``global_item`` | *formal_parameter*
and
  ``function_designator`` is the name of the function which is defining the ``aspect_specification`` enclosing the ``dependency_aspect``.

Note that ``dependency_list``, ``export_list``, ``import_list``, ``import_item``, ``conditional_dependency`` and ``dependency_item`` are all forms of expression and may be parenthesised.

.. todo:: We could consider associating + with the export list rather than the arrow, e.g., Depends => (+X => (Y, Z, Z)) or Depends => (+(A, B, C) => Z).


Legality Rules
^^^^^^^^^^^^^^

#. An ``aspect_specification`` of a subprogram may have at most one ``dependency_aspect``.
#. Every ``dependency_item`` of a ``dependency_aspect`` must be a *formal parameter*, a ``global_item``, or a subcomponent thereof, of the subprogram of the enclosing ``aspect_specification``.
#. Every ``dependency_item`` in an ``export_list`` must have a mode of **in out** or **out**.
#. Every ``dependency_item`` in an ``import_list`` must have a mode of **in** or **in out**
#. A ``dependency_item`` of mode **in** shall not appear in an ``export_list``..
#. A ``dependency_item`` shall not appear more than once, other than in the ``condition`` of a ``conditional_dependency`` in a single ``import_list`` or ``export_list``.
#. Every ``dependency_item`` of a subprogram of mode **out** or **in out** shall appear in exactly one ''export_list`` of the ``dependency_aspect``.
#. Every ``dependency_item`` of a subprogram of mode **in** or **in out** shall appear in at least one ``import_list``.
#. A ``dependency_aspect`` for a function, F,  may only contain one item in its ``export_list``; the attribute F'Result.  Generally ``dependency_aspects`` are not required for functions unless it is to describe a ``conditional_dependency``.
#. A ``function_designator`` may not appear in the ``dependency_aspect``of a procedure.
#. There can be at most one export list which is a **null** symbol and if it exists it must be the ``export_list`` of the last ``dependency_clause`` in the ``dependency_aspect``

.. todo:: Further rules regarding the use of conditional dependencies and subcomponents in dependency aspects.

Further Restrictions

.. todo:: Further restrictions such as no conditional derives, no subcomponents, etc.  Mandatory derives, derives on interfaces, etc.    
 


Examples
^^^^^^^^

.. code-block:: ada

   procedure P (X, Y, Z in : Integer; Result : out Boolean)
   with Depends => (Result => (X, Y, Z));
   -- The final value of Result depends on the initial values of X, Y and Z

   procedure Q (X, Y, Z in : Integer; A, B, C, D, E : out Integer)
   with Depends => ((A, B) => (X, Y),
                     C     => (X, Z),
                     D     => Y,
                     E     => null);
   -- The final values of A and B depend on the initial values of X and Y.
   -- The final value of C depends on the initial values of X and Z.
   -- The final value of D depends on the initial value of Y.
   -- The final value of E does not depend on any input value.

   procedure R (X, Y, Z : in Integer; A, B, C, D : in out Integer)
   with Depends => ((A, B) =>+ (A, X, Y),
                     C     =>+ Z,
                     D     =>+ null);
   -- The "+" sign attached to the arrow indicates self dependency, that is
   -- the final value of A depends on the initial value of A as well as the 
   -- initial values of X and Y.
   -- Similarly, the final value of B depends on the initial value of B 
   -- as well as the initial values of A, X and Y.
   -- The final value of C depends on the initial value of C and Z.
   -- The final value of D depends only on the initial value of D.

   procedure S (X : in Integer; A : in out Integer)
   with Global  => (Input  => (X, Y, Z),
                    In_Out => (A, B, C, D)),
        Depends => ((A, B) =>+ (A, X, Y),
                     C     =>+ Y,
                     D     =>+ null);
   -- Here globals are used rather than parameters and global items may appear
   -- in the dependency aspect as well as formal parameters.

   procedure T (X : in Integer; A : in out Integer)
   with Global  => (Input  => (X, Y, Z),
                    In_Out => (A, B, C, D)),
        Depends => ((A, B) =>+ (X, if X = 7 then (A,Y)),
                     C     =>+ Y,
                     D     =>+ null);
   -- This example introduces a conditional dependency for the final values of A and B.
   -- The final value of A is dependent on the initial values of A and X and if X = 7
   -- then it is also dependent on the initial value of Y.
   -- Similarly, the final value of B is dependent on the initial values of B and X
   -- and if X = 7 then it is also dependent on the initial values of A and Y.

   function F (X, Y : Integer) return Integer
   with Global  => G,
        Depends => (F'Result => (G, X, (if G then Y)));
   -- Dependency aspects are only needed for a function to describe conditional 
   -- dependencies; otherwise they can be directly determined from
   -- its parameters and globals.
   -- In this example, the result of the function is dependent on G and X 
   -- but only on Y if G is True.

Post_Cases
----------

.. todo::
   A postcondition expressed as a set of disjoint cases covering
   all cases

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
^^^^^^^^^^^^^^

.. todo::
  Should the post cases be exclusive and should the check that exactly one
  guard is true be performed at subprogram entry?



Anti-aliasing rules:
--------------------

.. todo:: The following text is copied from the SPARK 2005 LRM

The rules below prevent aliasing of variables in the execution of procedure subprograms.  See Section 6.1.2 for the definitions of imported, exported and entire variables.  (If a procedure subprogram has two procedure annotations as a consequence of refinement (c.f. Chapter 7), then in applying the rules to calls of a procedure P occurring outside the package in which P is declared, the annotation in the declaration should be employed; whereas in applying the rules to calls within the body of this package, the annotation in the procedure body or body stub should be used.)
1	If a variable V named in the global definition of a procedure P is exported, then neither V nor any of its subcomponents can occur as an actual parameter of P.
2	If a variable V occurs in the global definition of a procedure P, then neither V nor any of its subcomponents can occur as an actual parameter of P where the corresponding formal parameter is an exported variable.
3	If an entire variable V or a subcomponent of V occurs as an actual parameter in a procedure call statement, and the corresponding formal parameter is an exported variable, then neither V or an overlapping subcomponent of V can occur as another actual parameter in that statement. Two components are considered to be overlapping if they are elements of the same array or are the same component of a record (for example V.F and V.F) including subcomponents of the component (for example V.F and V.F.P). Note array elements are always considered to be overlapping and so, for example, V.A(I).P and V.A(J).Q are considered as overlapping.
Where one of these rules prohibits the occurrence of a variable V or any of its subcomponents as an actual parameter, the following constructs are also prohibited in this context:
1	a type conversion whose operand is a prohibited construct;
2	a qualified expression whose operand is a prohibited construct;
3	a prohibited construct enclosed in parentheses.



.. todo::  The rest of this chapter.  What do we do with the rest of this stuff?

  The Param aspects should refine the regular Ada 2012 parameter modes, for
  example when a parameter X appears in the Param_In_Out aspect, its parameter
  mode should be ``in out``. Likewise, if a parameter X appears in the Param_In
  and Param_Out aspects (e.g. with different conditions), its parameter mode
  should be ``in out``.

Meaning
-------

.. todo:: Does this belong here? have we covered this already?

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
