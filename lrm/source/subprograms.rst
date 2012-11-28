Subprograms
===========

Subprogram Declaration
----------------------

We distinguish the *declaration view* introduced by a ``subprogram_declaration``
from the *implementation view* introduced by a ``subprogram_body`` or an
``expression_function_declaration``. For subprograms that are not declared by
a ``subprogram_declaration``, the ``subprogram_body`` or
``expression_function_declaration`` also introduces a declaration view which
may be in |SPARK| even if the implementation view is not.

Rules are imposed in |SPARK| to ensure that the execution of a function
call does not modify any variables declared outside of the function.
It follows as a consequence of these rules that the evaluation
of any [SPARK] expression is side-effect free.

.. centered:: **Extended Legality Rules**

#. A function declaration shall not have a ``parameter_specification``
   with a mode of **out** or **in out**. This rule also applies to
   a subprogram_body for a function for which no explicit specification
   is given.

.. centered:: **Verification Rules**

.. centered:: *Flow Analysis*

#. The Global aspect of a function (whether explicitly specified or
   implicitly synthesized from the subprogram implementation)
   shall not include a moded_choice having a mode of Output or In_Out.

.. todo::
   In the future we may be able to permit access and aliased formal parameter specs. Target: rel2+

.. todo::
   What do we do regarding null exclusion parameters? Target: D2

.. todo::
   What do we do regarding function access results and function null exclusion results? Target: D2


Preconditions and Postconditions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As indicated by the ``aspect_specification`` being part of a
``subprogram_declaration``, a subprogram is in |SPARK| only if its specific
contract expressions (introduced by ``Pre`` and ``Post``) and class-wide
contract expressions (introduced by ``Pre'Class`` and ``Post'Class``), if any,
are in |SPARK|.

.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

#. Verification conditions are generated from the program text to
   demonstrate that the implementation of the body of the subprogram
   satisfies the post condition provided the precondition is True and
   the subprogram completes normally.

.. todo:: Think about Pre'Class and Post'Class. Target: D2.

Subprogram Contracts
~~~~~~~~~~~~~~~~~~~~

|SPARK| provides extra aspects, the ``Global``, ``Param`` and ``Dependency``
aspects to strengthen a subprogram declaration so that constructive,
modular program analysis may be performed.  With the extra aspects the
body of a subprogram does not have to be implemented in order for
analysis and proof of callers of the subprogram.

A ``Contract_Cases`` aspect is also provided which provides a convenient
way of specifying formally the required functionality of a subprogram.

.. note::
 (YM) The following paragraph is redundant with the preceding ones. Which should
 be retained?

Extra aspects are provided in |SPARK|, ``Global``, ``Param``,
``Dependency`` and ``Contract_Cases`` in addition to the Ada ``Pre``
and ``Post``.  The extra aspects facilitate an extended specification
and a potentially more concise form of pre and postcondition.

|SPARK| requires that some of the extra aspects are ordered within the
``aspect_specification`` of a subprogram.

.. centered:: **Legality Rules**

#. The ``Param``, ``Global`` and ``Dependency`` aspects are all optional but, if
   present, must be the first entries in a subprogram
   ``aspect_specification`` in the order ``Param`` aspect, ``Global`` aspect
   and ``Dependency`` aspect.

.. note:: (YM) why these ordering restrictions? I don't think we should
          enforce this.


Contract Cases
~~~~~~~~~~~~~~

The ``Contract_Cases`` aspect provide a concise way to specify mutually independent
cases guarded by expressions using the initial value of **in** or **in
out** *formal parameters* or *global variables*.  Each case specifies
the final value of mode **out** or **in out** *formal parameters* or
*global variables*.  The other requirement of contract cases, given
that they are mutually exclusive, is that there is exactly one guard
which is satisfied.  The guard of the final case may be the keyword
**others** which means that if all the other guards are false this
case is taken.

Contract cases may be used in conjunction with a standard pre and
postcondition in which case the precondition is augmented with a check
that exactly one of the guards is satisfied and the postcondition is
conjoined with conditional expressions representing each of the cases.
For example:

.. code-block:: ada

 procedure P (...) with
      Pre  => General_Precondition,
      Post => General_Postcondition,
      Contract_Cases => (A1 => B1,
                         A2 => B2,
                         ...
                         An => Bn);

is short hand for

.. code-block:: ada

 procedure P (...) with
      Pre  => General_Precondition
                and then Exactly_One_Of(A1,A2...An),
      Post => General_Postcondition
                and then (if A1'Old then B1)
                and then (if A2'Old then B2)
                and then ...
                and then (if An'Old then Bn);


where

  A1 .. An are Boolean expressions involving the initial values of
  *formal parameters* and *global variables* and

  B1 .. Bn are Boolean expressions that may also use the final values of
  *formal parameters*, *global variables* and results.

The Contract Cases Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Contract_Cases" and the ``aspect_definition`` must follow
the grammar of ``contract_case_list`` given below.


.. centered:: **Syntax**

::

   contract_case_list  ::= (contract_case {, contract_case})
   contract_case       ::= contract_guard => consequence
                         | others => consequence

where

   ``contract_guard    ::=`` *Boolean_*\ ``expression``

   ``consequence ::=`` *Boolean_*\ ``expression``


.. centered:: **Legality Rules**

#. A Contract Cases aspect specification is allowed in the same
   contexts where a Pre or Post aspect specification is allowed.
#. A Contract Cases aspect may have at most one **others**
   ``contract_case`` and if it exists it must be the last one in the
   ``contract_case_list``.
#. A consequence expression is considered to be a postcondition
   expression for purposes of determining the legality of Old or
   Result attribute_references.

.. centered:: **Static Semantics**

#. A Contract Cases aspect specification is an assertion (as defined
   in RM 11.4.2(1.1/3)); its assertion expressions are as described
   below. Contract_Cases may be specified as an assertion_aspect_mark
   in an Assertion_Policy pragma.


.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

#. Each ``contract_guard`` in a Contract Cases aspect has to proven to
   be mutually exclusive, that is only one ``contract_guard`` can be
   True with any set of inputs conformant with the formal parameters
   and satisfying the specific precondition.
#. At the point of call a check that a ``contract_guard`` is True has to be
   proven.
#. For every ``contract_case``, when its ``contract_guard`` is True,
   the implementation of the body of the subprogram must be proven to
   satisfy the ``consequence`` of the ``contract_case``.


.. centered:: **Dynamic Semantics**

#. Upon a call of a subprogram or entry which is subject to an enabled
   Contract Cases aspect_specification, Contract Cases checks are
   performed as follows:

   * Immediately after the specific precondition expression is
     evaluated and checked (or, if that check is disabled, at the
     point where the check would have been performed if it were
     enabled), all of the contract_guard expressions are evaluated in
     textual order. A check is performed that exactly one (if no
     others contract_guard is provided) or at most one (if an others
     contract_guard is provided) of these conditions evaluates to
     True; Assertions.Assertion_Error is raised if this check fails.

   * Immediately after the specific postcondition expression is
     evaluated and checked (or, if that check is disabled, at the
     point where the check would have been performed if it were
     enabled), exactly one of the consequences is evaluated. The
     consequence to be evaluated is the one corresponding to the one
     contract_guard whose evaluation yielded True (if such a
     contract_guard exists), or to the others contract_guard (if every
     contract_guard's evaluation yielded False).  A check is performed
     that the evaluation of the selected consequence evaluates to
     True; Assertions.Assertion_Error is raised if this check fails.

.. _mode-specification:

Mode Specification
~~~~~~~~~~~~~~~~~~

A formal parameter or *global variable* of a subprogram, or state
abstraction (see :ref:`abstract-state`) which may be read, directly or
indirectly, by the subprogram is an *input* of the subprogram. A
formal parameter, *global variable* or state abstraction which may be
updated, directly or indirectly, by the subprogram is an *output* of
the subprogram.

A mode specification is used for the ``Global`` and ``Param`` aspects
as well as for advanced Global aspects.  It allows the mode of each
input and output of the subprogram to be specified.

.. centered:: **Syntax**

::

   mode_specification          ::= (mode_choice {, mode_choice})
                                 | default_mode_choice
                                 | null
   mode_choice                 ::= mode_selector => mode_definition_list
   default_mode_choice         ::= mode_definition_list
   mode_definition_list        ::= mode_definition
                                 | (mode_definition {, mode_definition})
   mode_definition             ::= moded_item
                                 | conditional_mode
   conditional_mode            ::= (if condition then moded_item_list
                                    {elsif condition then moded_item_list}
                                    [else moded_item_list])
   moded_item_list             ::= moded_item
                                 | (moded_item {, moded_item})
                                 | null
   mode_selector               ::= Input| Output | In_Out | Proof
   moded_item                  ::= name


.. centered:: **Static Semantics**

#. A ``default_mode_choice`` is considered to be a ``mode_choice``
   with the ``mode_selector Input``.

.. centered:: **Legality Rules**

#. Each ``mode_selector`` shall not occur more than once in a given
   ``mode_specification``.
#. A ``moded_item`` appearing in a ``mode_specification`` with a
   ``mode_selector`` of ``In_Out`` may not appear in any other
   ``mode_specification``.

.. _global-aspect:

Global Aspect
~~~~~~~~~~~~~

A *global item* is a *global variable* or a state abstraction (see
:ref:`abstract-state`).

A ``global_aspect`` of a subprogram, if present, lists the global
items that are inputs and outputs of the subprogram and assigns a mode
to each of them using a ``mode_specification``.
  
The *global* items are considered to have modes the same as *formal
parameters*, **in**, **out** and **in out** with the same meaning.

The Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Global" and the ``aspect_definition`` must
follow the grammar of ``mode_specification``
:ref:`mode-specification`.

.. centered:: **Static Semantics**

#. An object which is not a subcomponent of any containing object is
   said to be an *entire* object.

#. A subprogram with a ``global_aspect`` that has a
   ``mode_refinement`` of **null** is taken to mean that the
   subprogram does not access any global items.

#. Each global item in a Global aspect of a subprogram is an input or
   an output of the subprogram shall satisfy the following mode
   specification rules:

   * a global item that is never updated, directly or indirectly, by
     the subprogram is mode **in** and has a ``mode_selector`` of Input;
   * a global item that is never read, directly or indirectly, by the
     subprogram and is always updated on every call to the subprogram
     is mode **out** and has a ``mode_selector`` of Output; and
   * otherwise the global item is mode **in out** and has a
     ``mode_selector`` of In_Out.

#. A global aspect is *basic* if it does not have a
   ``conditional_mode`` and every global item that is a global
   variable is an entire object.
   [Basic Global aspects are checked by flow-analysis]

#. If a Global aspect is not provided in a subprogram
   aspect_specification one is synthesized from the body of the
   subprogram, if it exists.  Only baisc Global aspects are
   synthesized.

.. centered:: **Legality Rules**

#. A ``global_aspect`` may only appear in the ``aspect_specification``
   of a subprogram.
#. A function subprogram may not have a ``mode_selector`` of
   ``Output`` or ``In_Out`` in its ``global_aspect``.
#. Every ``moded_item`` occurring in a Global aspect shall be a global
   item.
#. A global item which is a state_abstraction shall occur at most
   once in a single Global aspect.
#. A global item which is an entire object shall occur at most once in
   a single Global aspect and none of its subcomponents shall be named
   in the same Global aspect.
#. A global item occuring in a Global aspect of a subprogram aspect
   specification shall not have the same direct name as a formal
   parameter of the subprogram.

.. centered:: **Verification Rules**

#. A basic Global Aspect is verified against the mode specification
   rules given in the static semantics.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Global.


.. centered:: **Examples**

.. code-block:: ada

   with Global => null; -- Indicates that the subprogram does not read or update
                        -- any global items.
   with Global => V;    -- Indicates that V is a mode in global item.
   with Global => (X, Y, Z);  -- X, Y and Z are mode in global items.
   with Global => (Input => V); -- Indicates that V is a mode in global item.
   with Global => (Input => (X, Y, Z)); -- X, Y and Z are mode in global items.
   with Global => (Output => (A, B, C)); -- A, B and C are mode out global items.
   with Global => (Input  => (X, Y, Z),
                   Output => (A, B, C),
                   In_Out => (P, Q, R));
                  -- A global aspect with all types of global specification


Param Aspects and Advanced Global Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Param Aspects and Advanced Global aspects are optional and facilitate
designating a mode to a subcomponent of an object and to define mode
behaviour that is conditional.

When subcomponents of an object or conditional modes occur in a
``mode_specification`` an *effective* mode can be determined which
would be the equivalent mode of the each ``moded_item`` if the
subcomponents were replaced by their entire containing objects and
every ``conditional_mode`` by an unconditional one.
 
The Param aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Param" and the ``aspect_definition`` must
follow the grammar of ``mode_specification``
:ref:`mode-specification`.

.. centered:: **Static Semantics**

#. A name is said to be *moded_item eligible* if:

   * it is a direct or expanded name denoting an *entire* object or a
     ``state_name``; or
   * it is a direct or expanded name denoting an object renaming
     declaration whose object name is *moded_item eligible*; or
   * it is an ``indexed_component`` or ``selected_component`` whose prefix is
     *moded_item eligible*.

#. Two *moded_item eligible* names are said to be *independent* if

   * both are direct or expanded names denoting *entire* objects and
     they denote two different objects; or
   * one is a direct or expanded name denoting an object renaming
     declaration whose object is *independent* of the other; or
   * one is a ``selected_component`` whose prefix is *independent* of the
     other; or
   * both are ``selected_components`` and their ``selector_names`` denote
     different components of the same record type; or
   * either is an indexed component

#. The *effective mode* of a ``moded_item`` with respect to a specific
   subprogram describes the way that the object is used by the
   subprogram:

   * If the ``moded_item`` is read directly or indirectly by the
     subprogram its *effective mode* is **in**.
   * If the ``moded_item`` is not read but always updated by the
     subprogram directly or indirectly then its *effective mode* is
     **out**.
   * If the body of the suboprogram neither reads nor updates the
     ``moded_item``, directly or indirectly then the *effective mode*
     is unmoded.
   * Otherwise the *effective mode* is **in out**.

#. The *effective mode* of a ``moded_item`` is determined as
   follows:

   * if a ``moded_item`` is listed in a ``mode_specification`` with a
     mode selector of ``In_Out``, the *effective  mode* is **in out**;
   * if a ``moded_item`` is listed in both a ``mode_specification``
     with a mode selector of ``Input`` and one of ``Output``, the
     *effective mode* is **in out**;
   * if a ``moded_item`` is only listed in a ``mode_specification``
     with a mode selector of ``Input``, the *effective mode* is **in**.
   * If a ``moded_item`` is only listed in a ``mode_specification``
     with a mode selector of ``Output``, the *effective mode* is
     **out**; and
   * If a ``moded_item`` is listed in a ``mode_specification`` with a
     mode selector of ``Proof``, the *effective mode* is unmoded
     and can only be used in an assertion expression (as defined in RM
     11.4.2(1.1/3)).

#. The condition(s) of a ``conditional_mode`` are ignored in
   determining the *effective mode* of a ``moded_item`` and only the
   ``mode_selector`` of the ``mode_specification`` is used as
   described above.

#. If a ``moded_item`` is a subcomponent then the *entire* object of
   which it is a part also has an *effective* mode.  The *effective*
   mode of the *entire* object is required for flow analysis
   determined as follows:

   * if all of the subcomponents in the ``mode_refinenment`` have an
     *effective* mode of unmoded then its *effective* mode is unmoded;
   * If at least one subcomponent has an *effective* mode of **in**
     but none have an *effective* mode of **in out** or **out** then
     its effective mode is **in**; and
   * if at least one of the subcomponents in the ``mode_refinement``
     has an effective mode of **out** or **in out**, then its
     effective mode is **in out**.

#. A ``conditional_mode`` is specified using an ``if_expression`` with a
   notional type of Boolean. The ``if_expression`` provides additional
   details to the ``mode_refinement``.  It defines the condition under
   which each ``moded_item`` of the ``moded_item_list``, which is the
   *dependent* expression, has to be directly or indirectly read,
   updated or both within the body of the subprogram.

#. If the ``if_expression`` does not have a final else clause and all of
   the conditions of the ``if_expression`` evaluate to False it has the
   effect of **else null**.

#. A *dependent* expression which is a **null** ``moded_item_list``
   indicates that there are no ``moded_items`` read or updated when
   the controlling condition evaluates to True.

#. If a subcomponent is designated as pariticular mode it applies to
   just that subcomponent.  For instance, for an array A indexed by I,
   (Output => A (I)) specifies that this element of the array is an
   Output.  From this ``mode_choice`` in isolation it would imply that
   all other elements of the array are unchanged.  Other
   ``mode_choices`` in the ``mode_specification`` may indicate that
   other elements of the array are used a different mode.

.. centered:: **Legality Rules**

#. Every ``moded_item`` of a Param aspect of aspect_specification of a
   subprogram shall be a formal parameter of the subprogram.

#. A *formal parameter*, possibly as a prefix to one of its
   subcomponents, which appears in a ``param_aspect`` with a
   ``mode_selector`` of ``Output`` must be of mode **out** or mode
   **in out**.

#. A *formal parameter*, possibly as a prefix to one of its
   subcomponents, which appears in a ``param_aspect`` with a
   ``mode_selector`` of ``In_Out`` must be of mode **in out**.

#. A *formal parameter*, possibly as a prefix to one of its
   subcomponents, which appears in a ``param_aspect`` with a
   ``mode_selector`` of ``Input`` must be of mode **in** or mode **in
   out**.

#. The legality rules for an advanced Global aspect include the rules
   given for a basic Global aspect and these legality rules where they
   do not apply specifically to a Param aspect.

#. A ``moded_item`` shall be *moded_item eligible*.

#. Two ``moded_item``\ s occurring in the same ``mode_refinement``
   shall be independent unless they occur within distinct
   ``conditional_mode``\ s or within distinct ``moded_item_list``\ s of
   the same ``conditional_mode``.

.. centered:: **Verification Rules**

#. Proof checks are generated to verify that each subcomponent satisfies
   its given mode.

#. Proof checks are generated for each ``conditional_mode`` to
   demonstrate when a condition is True that the ``moded_item``\ s
   dependent on the condition satisfy their mode.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with Param aspects or
advanced Global aspects.

.. centered:: **Examples**

.. code-block:: ada

   -------------
   Param Aspects
   -------------

   procedure P (R : in out A_Record_Type)
   with Param => (Input  => R.F,
                  Output => R.E);
   -- The Param aspect states that only field F of the record R is read
   -- and that only field E is updated; the values of the remainder of
   -- the record fields are preserved.

   procedure Q (A : in out An_Array_Type)
   with Param => (Input  => A (I),
                  Output => A (J));
   -- The Param aspect states that only element I of the array A is read
   -- and that only element J is updated; the values of the remainder of
   -- the array elements are preserved. Note: I may equal J.

   procedure G (A : in out An_Array_Type)
   with Global => (Input  => K),
        Param  => (Input  => A (I),
                   Output => (if K = 10 then A (J)));
   -- The Param aspect states that only element I of the array A is read
   -- and element J is only updated if the global K = 10;
   -- the values of the remainder of the array elements are preserved
   -- including A (J) if K /= 10. Note: I, J and K may all be equal.

   --------------
   Global Aspects
   --------------

   with Global => (I, (if I = 0 then (P, Q, R));
                  -- I is a mode in global item and P, Q, and R are
                  -- conditional globals that are only read if I = 0.
   with Global => (Input => (I, (if I = 0 then (P, Q, R)));
                   -- I is a mode in global item and P, Q, and R are
                   -- conditional globals that are only read if I = 0.
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
                  -- R is a global record and only field R.F is updated
                  -- the remainder of the fields are preserved.

.. todo:: We could consider executable semantics, especially for
   conditional modes, but I think we should only consider executing
   aspects which are Ada aspects such as Pre and Post. RCC agrees.
   Target: rel2+.

.. todo:: SB Comments that he does not see the explanation
   of the checking of Global and Param Aspects in their description.
   TJJ believes the correct place for the explanation is under
   subprogram bodies because it is when the body is analyzed
   that the checks and rules come into force.
   There are some rules, perhaps they are not sufficient.
   TJJ to discuss with SB when he returns from his holiday. Target: D2.


Dependency Aspects
~~~~~~~~~~~~~~~~~~

.. todo:: SB has some wording and clarification comments in Legality
   and static semantic rules.  These have only been partially included
   as yet: D2.


A ``dependency_aspect`` defines a ``dependency_relation`` for a
subprogram which may be given in the ``aspect_specification`` of the
subprogram.  The ``dependency_relation`` is used in information flow
analysis.

Dependency aspects are optional and are simple formal specifications.
They are dependency relations which are given in terms of imports and
exports.  An ``export`` of a subprogram is a ``moded_item`` which is
updated directly or indirectly by the subprogram. An ``import`` of a
subprogram is a ``moded_item``, the initial value of which is used in
determining the final value of an ``export``.  A ``moded_item`` may be
both an ``import`` and an ``export``.  An ``import`` must have mode
**in** or mode **in out** and an ``export`` must have mode **in out**
or mode **out**.  Additionally the result of a function is an
``export``.

The ``dependency_relation`` specifies for each ``export`` every
``import`` on which it depends.  The meaning of X depends on Y in this
context is that the final value of ``export``, X, on the completion of
the subprogram is at least partly determined from the initial value of
``import``, Y, on entry to the subprogram and is written ``X =>
Y``. The functional behaviour is not specified by the
``dependency_relation`` but, unlike a postcondition, the
``dependency_relation``, if it is given, has to be complete in the
sense that every ``moded_item`` of the subprogram is an ``import``,
``export``, or both, and must appear in the ``dependency_relation``.
The ``dependency_relation`` of a function is assumed to be that its
result is dependent on every ``import`` of the function if an explicit
``dependency_aspect`` is not given.

The ``dependency_relation`` is specified using a list of dependency
clauses.  A ``dependency_clause`` has an ``export_list`` and an
``import_list`` separated by an arrow ``=>``. Each ``export`` in the
``export_list`` depends on every ``import`` in the ``import_list``. As
in UML, the entity at the tail of the arrow depends on the entity at
the head of the arrow.

A ``moded_item`` which is both an ``import`` and an ``export`` may
depend on itself.  A shorthand notation is provided to indicate that
each ``export`` in an ``export_list`` is self-dependent using an
annotated arrow, ``=>+``, in the ``dependency_clause``.

If an `export` does not depend on any ``import`` this is designated by
using a **null** as an ``import_list``.  An ``export`` may be
self-dependent but not dependent on any other import.  The shorthand
notation denoting self-dependence is useful here, especially if there
is more than one such ``export``; ``(X, Y, Z) =>+`` **null** means
that the ``export`` X, Y, and Z each depend on themselves but not on
any other ``import``.

A dependency may be conditional.  Each ``export`` in an
``export_list`` which has a ``conditional_dependency`` is only
dependent on every ``import`` in the ``import_list`` if the
``condition`` is ``True``.

The Dependency Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Depends" and the ``aspect_definition`` must follow
the grammar of ``dependency_relation`` given below.


.. centered:: **Syntax**

::

   dependency_relation    ::= null
                            | (dependency_clause {, dependency_clause})
   dependency_clause      ::= export_list =>[+] dependency_list
   export_list            ::= null
                            | export
                            | (export {, export})
   dependency_list        ::= import_item
                            | (import_item {, import_item})
   import_item            ::= import
                            | conditional_dependency
   conditional_dependency ::= (if condition then import_list
                               {elsif condition then import_list}
                               [else import_list])
   import_list            ::= import
                            | (import {, import})
                            | null
   import                 ::= moded_item
   export                 ::= moded_item | function_result

where

   ``function_result`` is a function Result attribute_reference.

.. todo:: Do we want to consider conditional_modes which have (if
   condition then import_list {elsif condition then import_list}
   [else import_list]) ?  I can imagine that this will be useful.
   Target: rel2+.

.. todo:: KSU have also discussed the need for a quantified dependency
   using for all.  Consider this in rel2+

.. centered:: **Legality Rules**

#. An ``import`` must have an *effective mode* of **in** or **in out**
   and an ``export`` must have an *effective mode* of **in out** or
   **out**.  Note: As a consequence ``moded_item`` which is both an
   ``import`` and an ``export`` shall have an effective mode of **in
   out**.
#. For the purposes of determining the legality of a Result
   attribute_reference, a ``dependency_relation`` is considered to be
   a postcondition of the function, if any, to which the enclosing
   ``aspect_specification`` applies.
#. There can be at most one ``export_list`` which is a **null** symbol
   and if it exists it must be the ``export_list`` of the last
   ``dependency_clause`` in the ``dependency_relation``.  An
   ``import`` which is in an ``import_list`` of a **null** export may
   not appear in another ``import_list`` of the same
   ``dependency_relation``.
#. Every ``moded_item`` in an ``export_list`` must be *independent*.
#. Every ``moded_item`` in an ``import_list`` must be *independent*.
#. Every ``export`` of the subprogram shall appear in exactly one
   ``export_list``.
#. Every ``import`` of the subprogram shall appear in at least one
   ``import_list``.
#. Every ``import`` of the subprogram shall appear at least
   of a ``dependency_relation`` shall be *independent*.
   of the ``dependency_shall appear exactly once in a
   ``dependency_relation``.  A subcomponent of a composite object V is
   sufficient to show an appearance of V but more than one distinct
   subcomponent V may appear as an ``export``

#. An ``export`` may be a subcomponent provided the containing object
   is not an ``export`` in the same ``dependency_relation``.  As long
   as this rule is satisfied, different subcomponents of a composite
   object may appear each as a distinct ``export`` and, for array
   subcomponents, a single, e.g. element A (I), cannot appear more
   than once as an ``export``, whereas elements A (I) and A (J) are
   considered as distinct and may both appear as an export even
   though I may equal J.
#. Each ``export`` shall appear exactly once in a
   ``dependency_relation``.  A subcomponent of a composite object V is
   sufficient to show an appearance of V but more than one distinct
   subcomponent V may appear as an ``export``
#. Each ``import`` shall appear at least once in a
   ``dependency_relation``.
#. An ``import`` shall not appear more than once in a single
   ``import_list`` other than appearing in a ``condition`` of a
   ``conditional_dependency``.  As different subcomponents of a
   composite object are considered to be distinct more than one these
   may appear in a single import list. The rule applies to indexed
   components in as much as an array element A (I) cannot appear more
   than once but both A (I) and A (J) may appear in the same
   ``import_list`` even though I may equal J.
#. A *variable* appearing in the condition of a
   ``conditional_dependency`` must be an ``import`` of the subprogram.


.. centered:: **Static Semantics**

#. A **null** ``dependency_relation`` indicates that there is not an
   ``import`` nor an ``export``.
#. Every *formal parameter* and *global variable* of a subprogram is a
   ``moded_item`` and is an ``import``, ``export`` or both.
#. An ``import`` or an ``export`` may be represented by itself or by
   one or of its subcomponents.
#. An ``export`` and an ``import`` is a ``moded_item`` and may be an
   *abstract state*, an *entire object* or a subcomponent of an
   *object*.
#. The result of a function F, denoted F'Result is considered to be
   an ``export`` of the function.
#. The result of a function is treated as an entire object.
   Subcomponents of a function result cannot be named in a
   ``dependency_relation``
#. A function which does not have a an explicit ``dependency_aspect``
   is assumed to have the dependency of its result on all of its
   imports.  Generally a ``dependency_aspect`` is not required for
   functions unless it is to describe a ``conditional_dependency``.
#. The ``+`` symbol in the syntax ``expression_list =>+ import_list``
   designates that each ``export`` in the ``export_list`` has a
   self-dependency, that is, it is dependent on itself. The text (A,
   B, C) =>+ Z is shorthand for (A => (A, Z), B => (B, Z), C => (C,
   Z)).
#. An ``import_list`` which is **null** indicates that the final
   values of each ``export`` in the associated ``export_list`` do not
   depend on any ``import``, other than themselves, if the
   ``export_list =>+`` **null** self-dependency syntax is used.
#. A an ``export_list`` that is **null** represents a sink for each
   ``import`` in the ``import_list``.The purpose of a **null**
   ``export_list`` is to facilitate the abstraction and calling of units
   that are not in |SPARK|.
#. If a subcomponent S of a composite object is an ``import`` then the
   *entire* object which contains S is effectively an ``import``.
#. If a subcomponent S of a composite object is an ``export`` then the
   *entire* object which contains S is effectively both an ``import``
   and an ``export``, as only part of the object is updated, the rest
   being preserved.
#. A ``conditional_dependency`` indicates the conditions under which
   the initial value of an ``import`` may be used in determining the
   final value of an ``export``.
#. A ``conditional_dependency`` does not affect the effective
   ``exports`` and ``imports`` and their relationship as this is
   always considered unconditionally in terms of *entire objects*.
   The effective imports of a ``conditional_dependency`` are the
   union of the variables used in its conditions and every import in
   the ``import_list`` of every branch.
#. The meaning of a ``dependency_relation`` is given in terms of
   effective exports and imports: the final value of each effective
   export E shall be determined from only static constants and the
   initial value of the effective  imports appearing in the
   ``dependency_list`` of E or from E itself if the self-dependency
   notation ``=>+`` has been used in the ``dependency_clause``
   defining E.


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a ``dependency_aspect``
it used purely for static analysis purposes and is not executed.


.. centered:: **Examples**

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
   -- The "+" sign attached to the arrow indicates self-dependency, that is
   -- the final value of A depends on the initial value of A as well as the
   -- initial values of X and Y.
   -- Similarly, the final value of B depends on the initial value of B
   -- as well as the initial values of A, X and Y.
   -- The final value of C depends on the initial value of C and Z.
   -- The final value of D depends only on the initial value of D.

   procedure S
   with Global  => (Input  => (X, Y, Z),
                    In_Out => (A, B, C, D)),
        Depends => ((A, B) =>+ (A, X, Y),
                     C     =>+ Y,
                     D     =>+ null);
   -- Here globals are used rather than parameters and global items may appear
   -- in the dependency aspect as well as formal parameters.

   procedure T (X : in Integer; A : in out Integer)
   with Global  => (Input  => (Y, Z),
                    In_Out => (B, C, D)),
        Depends => ((A, B) =>+ (X, if X = 7 then (A,Y,Z)),
                     C     =>+ Y,
                     D     =>+ null);
   -- This example introduces a conditional dependency for the final values of A and B.
   -- The final value of A is dependent on the initial values of A and X and if X = 7
   -- then it is also dependent on the initial value of Y and Z.
   -- Similarly, the final value of B is dependent on the initial values of B and X
   -- and if X = 7 then it is also dependent on the initial values of A, Y, and Z.

   function F (X, Y : Integer) return Integer
   with Global  => G,
        Depends => (F'Result => (G, X, (if G then Y)));
   -- Dependency aspects are only needed for a function to describe conditional
   -- dependencies; otherwise they can be directly determined from
   -- its parameters and globals.
   -- In this example, the result of the function is dependent on G and X
   -- but only on Y if G is True.

Proof Functions
~~~~~~~~~~~~~~~

.. todo:: TN LA24-011 is open for someone to propose a strawman design.
   Target: D2.


Formal Parameter Modes
----------------------

No extensions or restrictions.

Subprogram Bodies
-----------------


Conformance Rules
~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Inline Expansion of Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Mode Refinement
~~~~~~~~~~~~~~~

If a subprogram has a mode refinement (in a ``global_aspect``, a
``refined_global_aspect`` or a ``param_aspect``) then the
implementation of its body must comply with the refined modes
specified for the ``moded_items``.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. The initial value of a ``moded_item`` (including a *formal
   parameter* if the restriction ``Strict_Modes`` is in force) which
   is of mode which has an effective mode of **in** or **in out** must
   be used in determining the final value of at least one ``export``
   of the subprogram.
#. If a ``moded_item`` (including a *formal parameter* if the
   restriction ``Strict_Modes`` is in force) is of mode **in out** it
   must be updated directly or indirectly on at least one executable
   path through the subprogram body.
#. If a ``moded_item`` (including a *formal parameter* if the
   restriction ``Strict_Modes`` is in force) is of mode **out** then
   it must be updated either directly or indirectly on every
   executable path through the subprogram body.
#. If a ``moded_item``, appears in the ``mode_refinement`` of a
   subprogram with a mode of **in**, then it may only appear as a
   ``moded_item`` of mode **in** in any ``mode_refinement`` nested
   within the subprogram.

.. centered:: *Checked by Proof*

#. If a subcomponent name appears in a ``mode_specification`` with a
   ``mode_selector`` of ``Output`` or ``In_Out`` then just that
   subcomponent is considered to be updated and the other
   subcomponents of the object are preserved (unchanged).  If more
   than one subcomponent of the same object appears in such a
   ``mode_specification`` then all the mentioned subcomponents are
   considered to be updated and remaining subcomponents of the object
   preserved.
#. If a subcomponent name appears in a ``mode_specification`` with a
   ``mode_selector`` of ``Input`` or ``In_Out`` then the initial value
   of just that subcomponent is considered to be read and used in
   determining the final value of at least one ``export``. If more than
   one subcomponent of the same object appears in such a
   ``mode_specification`` then the rule applies to all mentioned
   subcomponents.

.. todo:: Conditional mode specifications which have to be checked by proof. Target: rel2+.

Global Aspects
~~~~~~~~~~~~~~

If a subprogram does not have a separate declaration its body or body
stub may have a ``global_aspect`` in its aspect specification where
the same rules as for a ``global_aspect`` in a subprogram declaration
apply.  When a subprogram has a ``global_aspect`` either in its
declaration or its body or body stub the rules and semantics given
below should be satisfied by the implementation of its body.

If the subprogram has a ``refined_global_aspect`` (see
:ref:`refined-global-aspect`), this has to be checked for consistency
with the ``global_aspect`` and influences the rules for checking the
implementation of its body as described below.

.. centered:: **Legality Rules**

#. A subprogram body or body stub may only have a ``global_aspect`` if
   it does not have a separate declaration.
#. A subprogram, shall not declare, immediately within its body, an
   entity of the same name as a ``moded_item`` or the name of the
   object of which the ``moded_item`` is a subcomponent, appearing in
   the ``global_aspect`` of the subprogram.  If the subprogram has a
   ``refined_global_aspect`` then the rule applies to ``moded_items``
   from both aspects.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. A non-*local variable* of a subprogram which is not a formal
   parameter or listed as a ``moded_item`` in the ``global_aspect``
   shall not be read or updated directly or indirectly within the body
   of the subprogram unless it appears as a ``moded_item`` in
   ``refined_global_aspect`` of the subprogram.
#. If a subprogram does not have a ``global_aspect`` then an implicit
   one is synthesised from implementation of the body (if it exists).

Param Aspects
~~~~~~~~~~~~~

If a subprogram does not have a separate declaration its body or body
stub may have a ``param_aspect`` in its aspect specification where the
same rules as for a ``param_aspect`` in a subprogram declaration
apply.  When a subprogram has a ``param_aspect`` either in its
declaration or its body or body stub the rules and semantics given
below should be satisfied by the implementation of its body.

.. centered:: **Legality Rules**

#. A subprogram body or body stub may only have a ``param_aspect`` if
   it does not have a separate declaration.


Dependency Aspects
~~~~~~~~~~~~~~~~~~

If a subprogram does not have a separate declaration its body or body
stub may have a ``dependency_aspect`` in its aspect specification
where the same rules as for a ``dependency_aspect`` in a subprogram
declaration apply.  When a subprogram has a ``dependency_aspect``
either in its declaration or its body or body stub the rules and
semantics given below should be satisfied by the implementation of its
body.

If the subprogram has a ``refined_dependency_aspect`` (see
:ref:`refined-dependency-aspect`), this has to be checked for consistency
with the ``dependency_aspect`` and influences the rules for checking the
implementation of its body as described below.


.. centered:: **Legality Rules**

#. A subprogram body or body stub may only have a
   ``dependency_aspect`` if it does not have a separate declaration.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. A dependency relation D' is synthesised from the body of a
   subprogram P (if it exists). if P has a ``dependency_aspect`` and:

   * has ``refined_dependency_aspect`` then D' is compared with the
     ``refined_dependency_aspect`` any differences reported; or
   * has a ``dependency_aspect`` but not a
     ``refined_dependency_aspect`` when one is required due to state
     refinement, then D' is taken to be the
     ``refined_dependency_aspect``.  Using the
     ``refined_state_aspect`` the consistency between D' and the
     ``dependency_aspect`` of P is checked and any inconsistencies,
     reported using the rules given in
     :ref:`refined-dependency-aspect` ; or
   * has a ``dependency_aspect`` and does not require a
     ``refined_dependency_aspect``, then D' is compared directly with
     the ``dependency_aspect`` of P and any differences reported; or
   * does not have a ``dependency_aspect`` an implicit
     ``dependency_aspect`` is synthesised from D'.

#. A function that does not have an explicit ``dependency_aspect`` is
   assumed to have a dependency relation that its result is dependent
   on all of its imports and this dependency relation is compared with
   the implicit one determined from the body of the function.


.. centered:: *Checked by Proof*

.. todo:: conditional dependencies and subcomponents. Target: rel2+.


Subprogram Calls
----------------

A call is in |SPARK| only if it resolves statically to a subprogram whose
declaration view is in |SPARK| (whether the call is dispatching or not).

Parameter Associations
~~~~~~~~~~~~~~~~~~~~~~



Abstract and Refined Views
^^^^^^^^^^^^^^^^^^^^^^^^^^

There are two possible views of a subprogram P declared in the visible
part of a package.  An abstract view and a refined view.  The abstract
view is that seen by the client of the package.  The refined view is
seen within the body of the package and its private descendants.


Global Aspects
^^^^^^^^^^^^^^

Every subprogram is considered to have a ``global_aspect`` whether it
is explicit or synthesized and implicit.  A subprogram declared in the
visible part of a package may also have a ``refined_global_aspect``,
again this may be explicit or synthesized.  Which of these two aspects
is used depends on where the subprogram is called.  If it is called
from within the package or its private dependents and the subprogram
has a ``refined_global_aspect`` then this is used.  In all other calls
the ``global_aspect`` is used.

Anti-Aliasing
~~~~~~~~~~~~~

An alias is a name which refers to the same object as another name.
The presence of aliasing is inconsistent with the underlying flow
analysis and proof models used by the tools which assume that
different names represent different entities.  In general, it is not
possible or is difficult to deduce that two names refer to the same
object and problems arise when one of the names is used to update the
object.

A common place for aliasing to be introduced is through the *actual
parameters* (see Ada RM 6.4.1) and between *actual parameters* and
*global variables* in a procedure call.  Extra semantic rules are
given that avoid the possibility of aliasing through *actual
parameters* and *global variables*.  A function is not allowed to have
side-effects and cannot update an *actual parameter* or *global
variable*.  Therefore, function calls cannot introduce aliasing and
are excluded from the anti-aliasing rules given below for procedure
calls.

.. todo:: Relax rules for aliasing based on the following paragraph.
   RCC comment: I am happy that these rules are OK given the definition
   of "overlapping" below. Assign to SB, TJJ and/or YM
   to agree this is all OK. Target: D2.

In |SPARK|, it is not allowed in a call to pass as parameters references to
overlapping locations, when at least one of the parameters is of mode ``out``
or ``in out``, unless the other parameter is of mode ``in`` and
by-copy. Likewise, it is not allowed in a call to pass as ``out`` or ``in out``
parameter a reference to some location which overlaps with any global parameter
of the subprogram. Finally, it is not allowed in a call to pass as ``in`` or
``in out`` parameter a reference to some location which overlaps with a global
parameter of mode ``out`` or ``in out`` of the subprogram, unless the parameter
is of mode ``in`` and by-copy.

The ``moded_items`` which are *global* to a procedure have to be
determined.  These may be obtained from an explicit ``global_aspect``
or ``dependency_aspect`` of the procedure, if either or both of these
are present. If neither of these are present then an implicit global
aspect is used which is deduced by analysis of the bodies of the called
subprogram and the subprograms it calls.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. If a procedure declaration does not have a ``global_aspect`` but
   has a ``dependency_aspect``, an implicit ``global_aspect`` will be
   computed from the ``dependency_aspect``.
#. If a procedure does not have a global or dependency
   aspect, an implicit ``global_aspect`` will be computed using whole
   program analysis.
#. In a call to a procedure P:

   #. If P is declared in package Q with an explicit ``global_aspect``
      and the body of P has a ``refined_global_aspect``
      (see :ref:`refined-global-aspect`) then in applying the anti-aliasing rules to
      calls of P within the body of Q the ``refined_global_aspect`` of
      the body or body stub of P should be used.
   #. In all other cases the ``global_aspect`` from declaration or
      body of P, if P does not have a separate declaration, shall be
      used.  The ``global_aspect`` may be implicit.

#. If a *variable* V named in the ``global_aspect`` of a procedure P
   is of mode **out** or **in out**, then neither V nor any of its
   subcomponents can occur as an *actual parameter* of P.
#. If a *variable* V occurs in the ``global_aspect`` of a procedure P,
   then neither V nor any of its subcomponents can occur as an *actual
   parameter* of P where the corresponding *formal parameter* is of
   mode **out** or **in out**.
#. If an *entire variable* V or a subcomponent of V occurs as an
   *actual parameter* in a procedure call statement, and the
   corresponding *formal parameter* is of mode **out** or **in out**,
   then neither V nor an overlapping subcomponent of V can occur as
   another *actual parameter* in that statement. Two components are
   considered to be overlapping if they are elements of the same array
   with the same index, or slices of the same array with common
   indices (these two cases require the use of proof techniques), or
   are the same component of a record (for example V.F and V.F)
   including subcomponents of the component (for example V.F and
   V.F.P).
#. Where one of these rules prohibits the occurrence of a *variable* V
   or any of its subcomponents as an actual parameter, the following
   constructs are also prohibited in this context:

    #. a type conversion whose operand is a prohibited construct;
    #. a qualified expression whose operand is a prohibited construct;
    #. a prohibited construct enclosed in parentheses.

.. centered:: *Checked by Proof*

#. The requirement that no two array elements overlap and that there
   are no overlapping elements between array slices or between array
   slices and individual elements.

.. centered:: **Dynamic Semantics**

The extended static semantics are checked using static analyses, no
extra dynamic checks are required.

Dependency Relations
~~~~~~~~~~~~~~~~~~~~

Every subprogram has a dependency relation, explicitly given in a
``dependency_aspect``, implicitly synthesized from the subprogram code
or conservatively assumed from the *formal parameters* and *global
variables* of the subprogram.  If the subprogram is declared in the
visible part of package it may also have a
``refined_dependency_aspect``, again explicitly given or synthesised.

The dependency relation of a subprogram is used to determine the effect
of a call to a subprogram in terms of the flows of information through
the subprogram.

#. A subprogram P declared in the visible part of a package, called
   within the body or private descendants of the package and P
   requires a ``refined_dependency_aspect`` because of
   state_refinement, the following will be used as the dependency
   relation of P:

   * the ``dependency_relation`` from the explicit
     ``refined_dependency_aspect`` if one is present;
   * for a function which does not have an explicit
     ``dependency_aspect``, the assumed dependency relation is that
     its result is dependent on all of its imports;
   * for a procedure which does not have an explicit
     ``refined_dependency_aspect`` but the subprogram
     has a proper body, the implicit dependency relation synthesized
     from the subprogram code will be used.
   * for a procedure which has neither a ``refined_dependency_aspect``
     nor a proper body the conservative dependency relation that is
     used is that every ``export`` is dependent on every ``import``.

#. A call to a subprogram P from a client of the package containing
   the declaration of P or for a call to a subprogram which does not
   require a ``refined_dependency_aspect``, the following will be used
   as the dependency relation :

   * the ``dependency_relation`` from an explicit ``dependency_aspect`` if one is present;
   * for a function which does not have an explicit
     ``dependency_aspect``, the assumed dependency relation is that
     its result is dependent on all of its imports;
   * for a procedure which does not have an explicit
     ``dependency_aspect`` but the subprogram has a proper body, the
     implicit dependency relation synthesized from the subprogram code
     will be used.
   * for a procedure which has neither a ``dependency_aspect`` nor a
     proper body the conservative dependency relation that is used is
     that every ``export`` is dependent on every ``import``.

Return Statements
-----------------

No extensions or restrictions.

Overloading of Operators
------------------------

No extensions or restrictions.

Null Procedures
---------------

No extensions or restrictions.


Expression Functions
--------------------

No extensions or restrictions.




