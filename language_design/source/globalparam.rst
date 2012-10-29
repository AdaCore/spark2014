Subprogram Contracts
====================

Subprogram contracts may be more rigorous than in Ada.  Extra legality rules are applied to formal subprogram parameters and further restrictions may be applied to their use.

Aspects are provided in addition to the Ada ``Pre`` and ``Post``. ``Global``, ``Param``, ``Depends`` and ``Post_Cases`` facilitate an extended specification and a potentially more concise form of post condition.

Subprogram Parameter Specifications
-----------------------------------

The static semantics of an Ada ``parameter_specification`` have been extended as described in the next subsections.

Extended Static Semantics
^^^^^^^^^^^^^^^^^^^^^^^^^^
#. A ``parameter_specification`` of a ``function_specification`` shall not have a mode of **out** or **in out** as a function is not allowed to have side-effects.

Restrictions That May Be Applied
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. ``Strict_Modes`` requires:

   * A *formal parameter* (see Ada LRM 6.1) of a subprogram of mode **in** or **in out** must be read directly or indirectly on at least one executable path, or used in the initialization of a declaration, within the subprogram body.
   * A *formal parameter* of a subprogram of mode **out** or **in out** must be updated directly or indirectly on at least executable path, or used in the initialization of a declaration, within the subprogram body.

#. ``No_Default_Subprogram_Parameter`` prohibits the use of default subprogram parameters, that is, a ``parameter_specification`` cannot have a ``default_expression``.

Dynamic Semantics
^^^^^^^^^^^^^^^^^

There is no change to the dynamic semantics of Ada.  The extended semantics are checked by static analysis.

Mode Refinement
---------------

Mode refinement is used in the specification of both Global and Param aspects.  It allows the mode of each item read or updated by a subprogram, *formal parameters*, *global variables* (see Ada LRM 8.1) and *data abstractions*  (see :ref:`abstraction of global state`) to be more precisely specified:

 * The *global variables* and *data abstractions* of a subprogram may be identified and a mode specified for each using a ``global_aspect``.
 * Modes can be applied to independent subcomponents of an object. For instance, the array element A (I) may be designated as mode **out** where as A (J) may be designated as mode **in**.  This mode refinement may be applied to *global variables* using the ``global_aspect`` and *formal parameters* using the ``param_aspect``.
 * Both the ``global_aspect`` and the ``param_aspect`` may have conditional mode definitions.  If the ``condition`` is ``True`` then the items guarded by the ``condition`` have the modes given in the specification otherwise these items do not and may not be used in that mode.

Sometimes this manual needs to refer to an object which is not a subcomponent of a larger containing object.  Such objects are called *entire* objects.

Syntax of Mode Refinement
^^^^^^^^^^^^^^^^^^^^^^^^^
::

   mode_refinement             ::= (mode_specification {, mode_specification})
                                 | default_mode_specification
                                 | null
   mode_specification          ::= mode_selector => mode_definition_list
   default_mode_specification  ::= mode_definition_list
   mode_definition_list        ::= mode_definition
                                 | (mode_definition {, mode_definition})
   mode_definition             ::= moded_item
                                 | conditional_mode
   conditional_mode            ::= (if condition then moded_item_list)
   moded_item_list             ::= moded_item
                                 | (moded_item {, moded_item})
   mode_selector               ::= Input| Output | In_Out
   moded_item                  ::= name

.. todo:: We may make an extra mode_selector available ``Proof`` which indicates that the listed variables are only used for proof and not in the code.

.. todo:: Do we want to consider conditional_modes which have (if condition then moded_item_list {elsif condition then moded_item_list} [else moded_item_list]) ?  It might well be useful and would be consistent with an extended syntax for dependency relations where I believe it will be useful.

Static Semantics
^^^^^^^^^^^^^^^^

#.  A ``mode_refinement`` is an ``expression`` and must satisfy the Ada syntax.  The non-terminals of the ``mode_refinement`` grammar, except ``mode_specification`` and ``mode_selector``, are also ``expressions``.
#. A ``moded_item`` must be the name of a *global variable*, a *formal parameter*, a subcomponent of a *global variable* or a *formal parameter*, or a *data abstraction*
#. A ``default_mode_specification`` is considered to be a ``mode_specification`` with the ``mode_selector Input``.
#. In a single ``mode_refinement`` there can be at most one of each of a ``mode_specification`` with a ``mode_selector`` of ``Input``, ``Output`` and ``In_Out``.
#.  A ``moded_item`` or one of its subcomponents appearing in a ``mode_specification`` with a ``mode_selector`` of ``In_Out`` may not appear in any other ``mode_specification``.
#.  The ``mode_selector`` of a ``mode_specification`` determines the effective mode of the ``moded_items`` in the ``mode_definition_list``.  ``Input`` is mode **in**, ``Output`` is mode **out**, and, ``In_Out`` is mode **in out**.
#.  A ``moded_item`` appearing in a ``mode_specification`` with a ``mode_selector`` of ``Input`` and another with a ``mode_selector`` of ``Output`` has the effective mode of **in out**.
#.  The rules for reading or updating of a ``moded_item`` of a particular mode are the same as for a *formal parameter* of the same mode including any restrictions placed on the interpretation of the modes.
#. A ``moded_item may not appear more than once within a single ``mode_specification`` other than appearing in a ``condition`` of a ``conditional_mode``.
#.  A *variable* appearing in the ``condition`` of a ``conditional_mode`` must be a ``moded_item`` of mode **in** or **in out** appearing in the same ``mode_refinement`` or a *formal parameter* of the associated subprogram of mode **in** or **in out**.
#. The body of a subprogram which is constrained by a ``mode_refinement`` must satisfy the mode constraints and conditional use applied to the ``moded_items``.

.. todo:: Further rules involving subcomponents and conditions within a global aspect. Here is a first attempt but it probably requires more thought:

#.  A ``moded_item`` may be a subcomponent provided a containing object (which may itself be a subcomponent) is not a ``moded_item`` in the same ``mode_refinement``.  Provided this rule is satisfied, different subcomponents of a composite object may appear more than once and, for array subcomponents, they may be the same indexed subcomponent.
#. If a subcomponent name appears in a ``mode_specification`` with a ``mode_selector`` of ``Output`` or ``In_Out`` then just that subcomponent is considered to be updated and the other subcomponents of the object are preserved (unchanged).  If more than one subcomponent of the same object appears in such a ``moded_specification`` then all the mentioned subcomponents are considered to be updated and remaining subcomponents of the object preserved.
#. If a subcomponent name appears in a ``mode_specification`` with a ``mode_selector`` of ``Input`` or ``In_Out`` then just that subcomponent is considered to be read.  If more than one subcomponent of the same object appears in such a ``mode_specification`` then all the mentioned subcomponents are considered to be read.
#. If an object has subcomponents which are array elements and more than one of these elements are referenced in a ``mode_refinement`` then more than one element may have the same index.  This may give rise to conflicts.  For example: Global => (Input  => A (I), Output => A (J)); if I = J then A(I) is in out.  I am sure conflicts such as these can be resolved - they just require a bit more thought.
#. A ``conditional_mode`` defines ``moded_item_list`` and if the ``condition`` is ``True`` then each ``moded_item`` in the list is considered to be a ``moded_item`` of a mode determined by the ``mode_selector`` of the enclosing ``mode_specification``.  If the condition is ``False`` then the items in the defined list are not regarded as moded items of the mode determined by the enclosing ``mode_specification``.
#. If a ``moded_item``, appears in the ``mode_refinement`` of a subprogram with a mode of **in**, then it may only appear as a ``moded_item`` of mode **in** in any ``mode_refinement`` nested within the subprogram.

Restrictions That May Be Applied
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. The restriction ``Moded_Variables_Are_Entire`` asserts that a ``Moded_item`` cannot be a subcomponent name.
#. The restriction ``No_Conditional_Modes`` prohibits the use of a ``conditional_mode`` in a ``mode_specification``.

Dynamic Semantics
^^^^^^^^^^^^^^^^^

There are no dynamic semantics associated with a ``mode_refinement`` as it is used purely for static analyses purposes and is not executed.

.. todo:: We could consider executable semantics, especially for conditional modes, but I think we should only consider executing aspects which are Ada aspects such as Pre and Post.



Global Aspects
--------------

A ``global_aspect`` names the *global* items that are read and, or, updated
by a subprogram.  The *global* items are considered to have modes the same as *formal
parameters*, **in**, **out** and **in out** and the modes may be refined as described above.

A *global* item is a ``moded_item`` that denotes a *global_variable_*\ ``name`` or a *data_abstraction_*\ ``name``.

.. todo::
   Introduce constructive / modular analysis before this point, in the
   Language Subset section.

A ``global_aspect`` is optional but if constructive, modular analysis or data abstraction is being used then a ``global_aspect`` may be required for every subprogram which references a *global* item.

The ``global_aspect`` uses a ``mode_refinement`` as part of the specification of a subprogram interface explicitly stating the *global* items that it references.  It is also used in the detection of illegal aliasing, preventing unintended use of a *global* variable by forgetting to declare a *local* variable, and the accidental hiding of a *global* variable by a more *local* variable.

.. todo::
   The following may not belong here. It could be simpler to give the big
   picture of what is in SPARK or not, and the various profiles, in the
   Language Subset section.

If none of the subprograms have a ``global_aspect``, then, for a complete program, using entire program analysis, it is possible to determine the *global* variables and check for illegal aliasing but not perform the other error preventative checks, nor the data_abstraction.

.. todo::
   Same here. This paragraph is about tools really, not the semantics of
   global aspects.

The use of ``global_aspects`` is recommended for newly written code to provide the full measure of error prevention.  If at least each subprogram declared immediately within a package or at library level has a ``global_aspect`` then for the subprograms declared within the body of another subprogram (nested), the ``global_aspect`` of the nested subprogram may be calculated from those of the enclosing subprogram.  To assist in such calculations a ``global_aspect`` may define that a subprogram does not reference any globals using a ``no_globals_specification``.


Syntax of a Global Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^
::

   global_aspect               ::= Global => mode_refinement

Static Semantics
^^^^^^^^^^^^^^^^

#. A ``moded_item`` appearing in a ``global_aspect`` must be the name of a *global variable*, a subcomponent of a *global variable*, or a *data abstraction*.
#.  An ``aspect_specification`` of a subprogram may have at most one ``global_aspect``.
#.  A function subprogram may not have a ``mode_selector`` of ``Output`` or ``In_Out`` in its ``global_aspect`` as a function is not permitted to have side-effects.
#.  A subprogram with a ``global_aspect`` that has a ``mode_refinement`` of **null** is taken to mean that the subprogram does not access any ``global_items``.
#. A ``global_item`` appearing in the ``global_aspect`` of a subprogram shall not have the same name, or be a subcomponent of an object with the same name as a *formal parameter* of the subprogram.
#.  A subprogram, shall not declare, immediately within its body, an entity of the same name as a ``global_item`` or the name of the object of which the ``global_item`` is a subcomponent, appearing in the ``global_aspect`` of the subprogram.
#.  A subprogram with a ``global_aspect`` shall not access any *global variable* directly or indirectly that is not given as a ``global_item`` in its ``global_aspect``.

Restrictions That May Be Applied
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#.  If the restriction ``No_Scope_Holes`` is applied then a subprogram, P, shall not declare an entity of the same name as a ``global_item`` or the name of the object of which the ``global_item`` is a subcomponent in its ``global_aspect`` within a ``loop_statement`` or ``block_statement`` whose nearest enclosing program unit is P.

.. todo:: In the following restriction, is this the assumption of no Global aspect implies Global => null sensible or should we always insist on Global => null?? I hope not!! Re-automate numbering after removing this todo.

2. The provision of ``global_aspects`` on all subprograms may be enforced by using the restriction ``Global_Aspects_Required``.  When this restriction is in force a subprogram which does not have an explicit ``global_aspect`` is considered to have a have have one of ``Global =>`` **null**.
#. A less stringent restriction is ``Global_Aspects_On_Non_Nested_Subprograms`` which requires a ``global_aspect`` on all subprograms not nested within another subprogram, although a ``global_aspect`` may still be placed on a nested subprogram (and require it if the body is a partial implementation).  A virtual global aspect is calculated from the body of each nested subprogram which does not have an explicit ``global_aspect``.
#. The style restriction, ``No_Default_Global_Modes_On_Procedures``, disallows a ``default_mode_specification`` within a procedure ``aspect_specification``. An explicit ``Input =>`` must be given.  A function ``aspect_specification`` may have a global_specification with a ``default_mode_specification``.

Dynamic Semantics
^^^^^^^^^^^^^^^^^

There are no dynamic semantics associated with a ``global_aspect`` it is used purely for static analyses purposes and is not executed.

.. todo:: We could consider executable semantics, especially for conditional modes, but I think we should only consider executing aspects which are Ada aspects such as Pre and Post.

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

A ``param_aspect`` is an optional aspect used to denote that a formal parameter of a subprogram is only conditionally used or that only part of a formal parameter of a composite type is used. It is specified using a ``mode_refinement``.

A ``param_aspect`` should refine the regular Ada 2012 parameter modes, for
example when a *formal parameter* X appears as Param => (In_Out => X), its mode should be **in out**. Likewise, if a *formal parameter* Y appears in a ``mode_specification`` with a ``mode selector`` of ``Input`` and in another with a ``mode_selector`` of ``Output`` (e.g. with different conditions), its *formal parameter* mode should be **in out**.


Syntax of a Param Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^
::

   param_aspect               ::= Param => mode_refinement

Static Semantics
^^^^^^^^^^^^^^^^

#. A ``moded_item`` appearing in a ``param_aspect`` of a subprogram must be the name of a *formal parameter* or a subcomponent of a *formal parameter* of the subprogram.
#.  An ``aspect_specification`` of a subprogram may have at most one ``param_aspect``.
#. A ``param_aspect`` shall not have a ``mode_refinement`` of **null**.
#. A *formal parameter*, possibly as a prefix to one of its subcomponents, which appears in a ``param_aspect`` with a ``mode_selector`` of ``Output`` must be of mode **out** or mode **in out**.
#. A *formal parameter*, possibly as a prefix to one of its subcomponents,  which appears in a ``param_aspect`` with a ``mode_selector`` of ``In_Out`` must be of mode **in out**.
#. A *formal parameter*, possibly as a prefix to one of its subcomponents, which appears in a ``param_aspect`` with a ``mode_selector`` of ``Input`` must be of mode **in** or mode **in out**.

Restrictions That May Be Applied
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. The use of ``param_aspects`` may be excluded by the restriction ``No_Param_Aspects``.
#. The restriction ``No_Default_Param_Modes_On_Procedures`` may be used to prohibit the use of an empty ``mode_selector`` in a procedure ``aspect_specification``.

Dynamic Semantics
^^^^^^^^^^^^^^^^^

There are no dynamic semantics associated with a ``param_aspect`` it is used purely for static analyses purposes and is not executed.

.. todo:: We could consider executable semantics, especially for conditional modes, but I think we should only consider executing aspects which are Ada aspects such as Pre and Post.

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

A ``dependency_aspect`` defines a ``dependency_relation`` for a subprogram which may be given in the ``aspect_specification`` of the subprogram.  The ``dependency_relation`` is used in information flow analysis.

Dependency aspects are optional and are simple formal specifications.  They are ``dependency_relations`` which are given in terms of imports and exports.  An ``import`` of a subprogram is a ``moded_item`` which is read directly or indirectly by the subprogram.  Similarly an ``export`` of a subprogram is ``moded_item`` which is updated directly or indirectly by the subprogram.  A ``moded_item`` may be both an ``import`` and an ``export``.  An ``import`` must have mode **in** or mode **in out** and an ``export`` must have mode **in out** or mode **out**.  Additionally the result of a function is an ``export``.

The ``dependency_relation`` specifies for each ``export`` every ``import`` on which it depends.  The meaning of X depends on Y in this context is that the final value of ``export``, X, on the completion of the subprogram is at least partly determined from the initial value of ``import``, Y, on entry to the subprogram and is written ``X => Y``. The functional behaviour is not specified by the ``dependency_relation`` but, unlike a postcondition, the ``dependency_relation``, if it is given, has to be complete in the sense that every ``moded_item`` of the subprogram is an ``import``, ``export``, or both, and must appear in the ``dependency_relation``.

The ``dependency_relation`` is specified using a list of dependency clauses.  A ``dependency_clause`` has an ``export_list`` and an ``import_list`` separated by an arrow ``=>``. Each ``export`` in the ``export_list`` depends on every ``import`` in the ``import_list``. As in UML, the entity at the tail of the arrow depends on the entity at the head of the arrow.

A ``moded_item`` which is both an ``import`` and an ``export`` may depend on itself.  A shorthand notation is provided to indicate that each ``export`` in an ``export_list`` is self-dependent using an annotated arrow, ``=>+``, in the ``dependency_clause``.

If an `export` does not depend on any ``import`` this is designated by using a **null** as an ``import_list``.  An ``export`` may be self-dependent but not dependent on any other import.  The shorthand notation denoting self-dependence is useful here, especially if there is more than one such ``export``; ``(X, Y, Z) =>+`` **null** means that the ``export`` X, Y, and Z each depend on themselves but not on any other ``import``.

A dependency may be conditional.  Each ``export`` in an ``export_list`` which has a ``conditional_dependency`` is only dependent on every ``import`` in the ``import_list`` if the ``condition`` is ``True``.

Syntax of a Dependency Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

   dependency_aspect      ::= Depends => dependency_relation
   dependency_relation    ::= (dependency_clause {, dependency_clause})
   dependency_clause      ::= export_list =>[+] dependency_list
   export_list            ::= null
                            | export
                            | (export {, export})
   dependency_list        ::= import_item_list
   import_item_list       ::= import_item
                            | (import_item {, import_item})
   import_item            ::= import
                            | conditional_dependency
   conditional_dependency ::= (if condition then import_list)
   import_list            ::= import
                            | (import {, import})
                            | null
   import                 ::= moded_item
   export                 ::= moded_item | function_result
   function_result        ::= function_designator'Result

where
  ``function_designator`` is the name of the function which is defining the ``aspect_specification`` enclosing the ``dependency_aspect``.

.. todo:: Do we want to consider conditional_modes which have (if condition then import_list {elsif condition then import_list} [else import_list]) ? I can imagine that this will be useful.

Static Semantics
^^^^^^^^^^^^^^^^

#.  A ``dependency_relation`` is an ``expression`` and must satisfy the Ada syntax.  The non-terminals of the ``dependency_relation`` grammar, except ``dependency_clause``, are also ``expressions``.
#. An ``aspect_specification`` of a subprogram may have at most one ``dependency_aspect``.
#. Every *formal_parameter* and every ``global_item``, or a subcomponent of either, of a subprogram is an ``import``, an ``export`` or both.
#. An ``import`` must have mode **in** or mode **in out**
#. An ``export`` must have mode **in out** or mode **out**
#. A ``moded_item`` which is both an ``import`` and an ``export`` shall have mode **in out**.
#. The result of a function is considered to to be an ``export`` of the function.
#. Every ``import`` and ``export`` of a subprogram shall appear in the dependency relation.
#. Each ``export`` shall appear exactly once in a ``dependency_relation``
#. Each ``import`` shall appear at least once in a ``dependency_relation``.
#. An ``import`` shall not appear more than once in a single ``import_list``.
#. A ``dependency_relation`` for a function, F,  has only one export and this is its result.  Its result is denoted by ``F'Result`` and may only appear as the only export of a function in its ``dependency relation``.  Generally ``dependency_aspects`` are not required for functions unless it is to describe a ``conditional_dependency``.
#. A ``function_result`` may not appear in the ``dependency_relation`` of a procedure.
#. The ``+`` symbol in the syntax ``expression_list =>+ import_list`` designates that each ``export`` in the ``export-list`` has a self-dependency, that is, it is dependent on itself. The text (A, B, C) =>+ Z is shorthand for (A => (A, Z), B => (B, Z), C => (C, Z)).
#. An ``import_list`` which is **null** indicates that the final values of each ``export`` in the associated ``export_list`` does not depend on any ``import``, other than themselves, if the ``export_list =>+`` **null** self-dependency syntax is used.
#. There can be at most one ``export_list`` which is a **null** symbol and if it exists it must be the ``export_list`` of the last ``dependency_clause`` in the ``dependency_relation``.  A an ``export_list`` that is **null** represents a sink for each ``import`` in the ``import_list``.  A ``import`` which is in such a ``import_list`` may not appear in another ``import_list`` of the same ``dependency_relation``.  The purpose of a **null** ``export_list`` is to facilitate moving Ada code outside the SPARK boundary.
#. A ``mode_refinement`` of a subprogram of must be consistent with its ``dependency_relation``.  The ``

.. todo:: Further rules regarding the use of conditional dependencies and subcomponents in dependency aspects.

Restrictions That May Be Applied
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. The restriction ``Procedures_Require_Dependency_Aspects`` mandates that all procedures must have a ``dependency_aspect``.  Functions may have a ``dependency_aspect`` but they are not required.
#. A less stringent restriction is ``Procedure_Declarations_Require_Dependency_Aspects`` which only requires a ``dependency_aspect`` to be applied to a procedure declaration.
#. The restriction ``No_Conditional_Dependencies`` prohibits the use of a ``conditional_dependency`` in any ``dependency_relation``
#. ``Dependencies_Are_Entire`` prohibits the use of subcomponents in ``dependency_relations``.

Dynamic Semantics
^^^^^^^^^^^^^^^^^

There are no dynamic semantics associated with a ``dependency_aspect`` it  used purely for static analyses purposes and is not executed.

.. todo:: We could consider executable semantics, especially for conditional dependencies, but I think we should only consider executing aspects which are Ada aspects such as Pre and Post.

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

   post_cases          ::= Post_Cases => (post_case_list)
   post_case_list      ::= post_case {, post_case_list}
   post_case           ::= boolean_expression => boolean_expression

Static Semantics
^^^^^^^^^^^^^^^^
.. todo:: Presumably the static semantics of the individual cases should be equivalent to the individual branches of an if-then-elsif-else conditional expression, where the LHS of the arrow is the condition.  I do not know whether it is feasible to prove, in general, that the cases are exclusive and or exhaustive.  It would be good to indicate where we can prove that cases are not exclusive and or exhaustive.


Dynamic Semantics
^^^^^^^^^^^^^^^^^
.. todo:: Presumably the dynamic semantics of the individual cases should be equivalent to the individual branches of an if-then-elsif-else conditional expression where the LHS of the arrow is the condition. A dynamic check could be applied on subprogram exit (it is a post condition! unless it is assumed that the LHS are the 'Old values?) to show that exactly one LHS (guard) is True. If none of the guards are satisfied then the cases are not exhaustive.




.. todo::  The rest of this chapter.  What do we do with the rest of this stuff?


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


