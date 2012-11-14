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

.. centered:: **Extended Legality Rules**

.. include:: extended-legality.rst
   :start-after: 6 Subprograms
   :end-before:  6.1

.. include:: extended-legality.rst
   :start-after: 6.1 Subprogram Declarations
   :end-before:  END OF FILE


Preconditions and Postconditions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As indicated by the ``aspect_specification`` being part of a
``subprogram_declaration``, a subprogram is in |SPARK| only if its specific
contract expressions (introduced by ``Pre`` and ``Post``) and class-wide
contract expressions (introduced by ``Pre'Class`` and ``Post'Class``), if any,
are in |SPARK|.

.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

#. Verification conditions are generated from the program text.
#. The verification conditions have to be proven to be True to
   formally demonstrate that the implementation of the body of the
   subprogram satisfies the post condition provided the precondition is
   True and the subprogram completes without exceptions.

.. todo:: Think about Pre'Class and Post'Class. Target: D2.

Subprogram Contracts
~~~~~~~~~~~~~~~~~~~~

Subprogram contracts may be more rigorous in |SPARK| than in Ada.
Extra legality rules are applied to formal subprogram parameters and
further restrictions may be applied to their use.

Extra aspects are provided in |SPARK|, ``Global``, ``Param``,
``Dependency`` and ``Contract_Cases`` in addition to the Ada ``Pre``
and ``Post``.  The extra aspects facilitate an extended specification
and a potentially more concise form of pre and postcondition.

.. note:: RCC. Do we imply or require any specific order on the
   new aspects here?  I don't think Ada2012 even allows for that at all?
   In S95, the natural order is always enforced - global, derives, pre, post -
   this also simplifies implemenation, since there's a sort-of implied
   declaration-before-use ordering here.  Can we/should we impose
   ordering on Global, Depends, Pre and Post in S14? Target D1/CDR. Assign: ???

Contract Cases
~~~~~~~~~~~~~~

Contract cases provide a concise way to specify a mutually independent
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

  B1 .. Bn are Boolean expressions involving the final values of
  *formal parameters* and *global variables*.

.. note:: RCC: Surely B1 .. Bn may also contain initial values?
   I have also changed "entry value" to "initial value" here, since the
   latter is used throughout the rest of this chapter. Assign: JK to
   confirm, update, then remove this note.

.. centered:: **Syntax**

::

   contract_cases      ::= Contract_Cases => (contract_case_list)
   contrct_case_list   ::= contract_case {, contract_case_list}
   contract_case       ::= contract_guard => consequence
                         | others => consequence

where

   ``contract_guard    ::=`` *Boolean_*\ ``expression``

   ``consequence ::=`` *Boolean_*\ ``expression``


.. centered:: **Legality Rules**

#. Only one ``contract_cases`` aspect may appear in an
   ``aspect_specification``.
#. A ``contract_cases`` aspect may have at most one **others**
   ``contract_case`` and if it exists it must be the last one in the
   ``contract_case_list``.
#. A ``contact_cases`` may only appear in the ``aspect_specification``
   of a subprogram declaration or the body of a subprogram if it has
   not already been declared.
#. If the ``contract_cases`` aspect is applied to a function
   subprogram F, then a ``consequence`` may use the name F'Result in
   its *Boolean_*\ ``expression``. A procedure subprogram may not use
   such a name.
#. The *variables* appearing in the ``contact_cases`` of a subprogram
   shall be *formal parameters* or *global variables* of the
   subprogram or subcomponents thereof.
#. The *variables* appearing in the ``guard`` must be of mode **in**
   or **in out**.
#. The *variables* appearing in the ``consequence`` must be of mode
   **out** or **in out**.

.. note:: RCC. Surely *in* mode variables are also OK in the consequence? Assign: JK
   confirm, update and remove this note.

.. centered:: **Static Semantics**

#. The values of *variables* appearing in the ``contract_guard`` are the entry
   values of the *variables* at a call of the subprogram associated
   with the ``contract_cases``.
#. The values of variables (including function result attributes)
   appearing the ``consequence`` are their final values after
   completion of the subprogram associated with the
   ``contract_cases``.

.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

#. A verification condition is that exactly one ``guard`` is True.  An
   **others** case is considered to a negation of the conjunction of
   every other ``guard`` and this is anded with the precondition.
#. A verification condition is that the ``consequent`` for each
   ``guard`` is ``True`` given that the ``guard`` is satisfied.
#. At most one ``contract_guard`` may be True when the subprogram is
   called.  A True ``contract_guard`` *selects* the ``contract_case``
   to which it belongs.
#. If there is not a ``contract_guard`` which is True when the
   subprgram is called, then there must be an **others**
   ``contract_case`` and the **others** ``contract_case`` is *selected*.
#. If a ``contract_case`` is *selected* when a subprogram is called,
   then the expression of the ``concequence`` of the *selected*
   ``contract_case`` must be True.


.. centered:: **Dynamic Semantics**

#. In a call to a subprogram with a ``contract_cases`` aspect then the
   entry checks are: the precondition is evaluated and then, if the
   precondition is satisfied, each ``guard`` is evaluated.  At most
   one of them should evaluate to ``True``.  If the precondition
   fails, more than one ``guard`` evaluates to ``True``, or no
   ``guard`` evaluates to ``True`` and there is no **others** case ,
   an exception is raised. Which one??
#. If the entry checks do not raise an exception and the execution of
   the subprogram completes then, for the case whose ``guard``
   evaluated to ``True``, evaluate the ``consequence`` using the final
   values of the variables from the subprogram execution.  If the
   ``consequence`` does not evaluate to ``True``, raise the exception
   ....

.. note:: RCC. this section appears to be incomplete.  Assign: JK to complete please?

.. _mode-refinement:

Mode Refinement
~~~~~~~~~~~~~~~

Mode refinement is used in the specification of both Global and Param
aspects.  It allows the mode of each item read or updated by a
subprogram, *formal parameters*, *global variables* (see Ada LRM 8.1)
and *abstract states* (see :ref:`abstract-state`) to be more precisely
specified:

 * The *global variables* and *abstract states* used by a subprogram
   may be identified and a mode specified for each using a
   ``global_aspect``.
 * Modes can be applied to independent subcomponents of an object. For
   instance, the array element A (I) may be designated as mode **out**
   whereas A (J) may be designated as mode **in**.  This mode
   refinement may be applied to *global variables* using the
   ``global_aspect`` and *formal parameters* using the
   ``param_aspect``.
 * Both the ``global_aspect`` and the ``param_aspect`` may have
   conditional mode definitions.  If the ``condition`` is ``True``
   then the items guarded by the ``condition`` have the modes given in
   the specification otherwise these items may not be used in that
   mode.

Sometimes this manual needs to refer to an object which is not a
subcomponent of a larger containing object.  Such objects are called
*entire* objects.

.. centered:: **Syntax**

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
   conditional_mode            ::= (if condition then moded_item_list
                                    {elsif condition then moded_item_list}
                                    [else moded_item_list])
   moded_item_list             ::= moded_item
                                 | (moded_item {, moded_item})
   mode_selector               ::= Input| Output | In_Out | Proof
   moded_item                  ::= name

.. todo:: We may make an extra mode_selector available ``Proof`` which
   indicates that the listed variables are only used for proof and not
   in the code. RCC comments: Yes - agree this needs to be in.  Target: D1/CDR
   TJJ:12-Nov-12 Added Proof to mode_selector.
   for the grammar and legality, D2 for the implementation? Assign: TJJ.

.. centered:: **Legality Rules**

#. A ``mode_refinement`` is an ``expression`` and must satisfy the Ada
   syntax.  The non-terminals of the ``mode_refinement`` grammar,
   except ``mode_specification`` and ``mode_selector``, are also
   ``expressions``.
#. A ``default_mode_specification`` is considered to be a
   ``mode_specification`` with the ``mode_selector Input``.
#. In a single ``mode_refinement`` there can be at most one of each of
   a ``mode_specification`` with a ``mode_selector`` of ``Input``,
   ``Output`` and ``In_Out``.
#. A ``moded_item`` must be the name of a *global variable*, a *formal
   parameter*, a subcomponent of a *global variable* or a *formal
   parameter*, or an *abstract state*
#. A ``moded_item`` appearing in a ``mode_specification`` with a
   ``mode_selector`` of ``In_Out`` may not appear in any other
   ``mode_specification``.
#. A ``moded_item`` may not appear more than once within a single
   ``mode_specification`` other than appearing in a ``condition`` of a
   ``conditional_mode``.  The rule applies to indexed components in as
   much as an array element A (I) cannot appear more than once but
   both A (I) and A (J) may appear in the same ``mode_specification``
   even though I may equal J.
#. A *variable* appearing in the ``condition`` of a
   ``conditional_mode`` must be a ``moded_item`` of mode **in** or
   **in out** appearing in the same ``mode_refinement`` or a *formal
   parameter* of the associated subprogram of mode **in** or **in
   out**.
#. A ``moded_item`` may be a subcomponent provided a containing object
   is not a ``moded_item`` in the same ``mode_refinement``.  As long
   as this rule is satisfied, different subcomponents of a composite
   object may appear more than once and, for array subcomponents,
   elements A (I) and A (J) are considered as distinct instances even
   though I my equal J.

.. todo:: We probably need to think more carefully about discriminanted
   and variant records. RCC comment: we need an entire design activity
   for disciminated and variant records. ToDo in chapter 3 as well. Target: D2.

.. centered:: **Static Semantics**

#. The ``mode_selector`` of a ``mode_specification`` determines the
   effective mode of the ``moded_items`` in the
   ``mode_definition_list``.  ``Input`` is mode **in**, ``Output`` is
   mode **out**, and, ``In_Out`` is mode **in out**.

.. note:: RCC. Update for mode ``Proof``.  Assume this is *in*?

#. A ``moded_item`` appearing in a ``mode_specification`` with a
   ``mode_selector`` of ``Input`` and another with a ``mode_selector``
   of ``Output`` has the effective mode of **in out**.
#. For an entire composite object V which has subcomponents that
   appear in a ``mode_refinement`` the following applies:

   a. if all the subcomponents in the ``mode_refinement`` have an
      effective mode of **in**, then the effective mode of V is **in**;
   b. if at least one of the subcomponents in the ``mode_refinement``
      has an effective mode of **out** or **in out**, then the
      effective mode of V is **in out**.
#. Each branch of a ``conditional_mode`` defines a ``moded_item_list``
   but the effective mode of each ``moded_item`` in the
   ``moded_item_list`` is unconditional.  The condition is ignored for
   the purposes of determining the effective mode.

.. centered:: **Dynamic Semantics**


There are no dynamic semantics associated with a ``mode_refinement``
as it is used purely for static analyses purposes and is not executed.

.. todo:: We could consider executable semantics, especially for
   conditional modes, but I think we should only consider executing
   aspects which are Ada aspects such as Pre and Post. RCC agrees.
   Target: rel2+.


Global Aspects
~~~~~~~~~~~~~~

A ``global_aspect`` names the *global* items that are read and/or
updated by a subprogram.  The *global* items are considered to have
modes the same as *formal parameters*, **in**, **out** and **in out**
and the modes may be refined as described in :ref:`mode-refinement`.

A *global* item is a ``moded_item`` that denotes a *global_variable_*\
``name`` or a *abstract_state_*\ ``name``.

The ``global_aspect`` uses a ``mode_refinement`` as part of the
specification of a subprogram interface explicitly stating the
*global* items that it references.  It is also used in the detection
of illegal aliasing, preventing unintended use of a *global* variable
by forgetting to declare a *local* variable, and the accidental hiding
of a *global* variable by a more *local* variable.

.. centered:: **Syntax**

::

   global_aspect ::= Global => mode_refinement

.. centered:: **Legality Rules**

#. A ``global_aspect`` may only appear in the ``aspect_specification``
   of a subprogram or a constant declaration.
#. A function subprogram may not have a ``mode_selector`` of
   ``Output`` or ``In_Out`` in its ``global_aspect`` as a function is
   not permitted to have side-effects.
#. A ``moded_item`` appearing in a ``global_aspect`` must be the name
   of a *global variable*, a subcomponent of a *global variable*, or
   an *abstract state*.
#. A ``moded_item`` appearing in the ``global_aspect`` of a subprogram
   shall not have the same name, or be a subcomponent of an object
   with the same name as a *formal parameter* of the subprogram.
#. A name that denotes a *global variable* appearing in a precondition
   or postcondition aspect of a subprogram must also appear in the ``global_aspect``
   of the same subprogram.
#. A name that denotes a *global variable* or a *formal parameter* appearing in a precondition
   or postcondition aspect of a subprogram must be consistent with the mode indicated by
   the ``global_aspect`` or the ``parameter_specification`` for that name, according to
   the following rules:

   1. For a name of a object X to appear in a precondition aspect, X must be a formal
      parameter or global variable which is of mode "in", "in out", or "Proof".
   2. For a name of a object X to appear in a postcondition aspect, X must be
      a formal parameter or global variable of any mode.
   3. Additionally, X'Old is permitted in a postcondition aspect if X is
      a global variable or formal parameter of mode "in out".
   4. Additionally, if X is a formal parameter of an unconstrained array type,
      and X is mode "out", then the attributes X'First, X'Last, X'Length and
      X'Range may appear in a precondition aspect.

.. todo:: Following the discussion under LA11-017 (the thread
   started by RCC on 26/10), we must document here the rules
   for consistency of globals in Global and Pre/Post aspects.
   Essentially, if a global appears in the Pre or Post, then 
   it *must* appear in a mode-consistent fashion in the Global
   aspect as well. Update: RCC proposes rules 5 and 6 above. TJJ, YM
   and/or SB to check it. Target: D1/CDR. 

.. centered:: **Static Semantics**

#. A subprogram with a ``global_aspect`` that has a
   ``mode_refinement`` of **null** is taken to mean that the
   subprogram does not access any global items.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a ``global_aspect`` it
is used purely for static analyses purposes and is not executed.


.. centered:: **Examples**

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
~~~~~~~~~~~~~

A ``param_aspect`` is an optional aspect used to denote that a formal
parameter of a subprogram is only conditionally used or that only part
of a formal parameter of a composite type is used. It is specified
using a ``mode_refinement``.

A ``param_aspect`` should refine the regular Ada 2012 parameter modes,
for example when a *formal parameter* X appears as Param => (In_Out =>
X), its mode should be **in out**. Likewise, if a *formal parameter* Y
appears in a ``mode_specification`` with a ``mode selector`` of
``Input`` and in another with a ``mode_selector`` of ``Output``
(e.g. with different conditions), its *formal parameter* mode should
be **in out**.  If a subcomponent of a *formal parameter* appears in
an ``Output`` ``mode _specification``, e.g., Param => (Output => A
(I)), even though the effective mode of A is **in out** the *formal
parameter*, A, may be given as mode **out** provided no other
subcomponents of A appear in an ``Input`` ``mode_specification``.


.. centered:: **Syntax**

::

   param_aspect ::= Param => mode_refinement

.. centered:: **Legality Rules**

#. An ``aspect_specification`` of a subprogram may have at most one
   ``param_aspect``.
#. A ``param_aspect`` shall not have a ``mode_refinement`` of
   **null**.
#. A ``moded_item`` appearing in a ``param_aspect`` of a subprogram
   must be the name of a *formal parameter* or a subcomponent of a
   *formal parameter* of the subprogram.
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

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a ``param_aspect`` it
is used purely for static analyses purposes and is not executed.

.. todo:: We could consider executable semantics, especially for
     conditional modes, but I think we should only consider executing
     aspects which are Ada aspects such as Pre and Post. Target: rel2+.

.. centered:: **Examples**

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
~~~~~~~~~~~~~~~~~~

A ``dependency_aspect`` defines a ``dependency_relation`` for a
subprogram which may be given in the ``aspect_specification`` of the
subprogram.  The ``dependency_relation`` is used in information flow
analysis.

Dependency aspects are optional and are simple formal specifications.
They are dependency relations which are given in terms of imports
and exports.  An ``export`` of a subprogram is ``moded_item`` which is
updated directly or indirectly by the subprogram. An ``import`` of a
subprogram is a ``moded_item``, the initial value of which, is used in
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

.. centered:: **Syntax**

::

   dependency_aspect      ::= Depends => dependency_relation
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
   function_result        ::= function_designator'Result

where

  ``function_designator`` is the name of the function which is
  defining the ``aspect_specification`` enclosing the
  ``dependency_aspect``.

.. todo:: Do we want to consider conditional_modes which have (if
   condition then import_list {elsif condition then import_list}
   [else import_list]) ?  It can imagine that this will be useful.
   Target: rel2+.

.. centered:: **Legality Rules**

#. A ``dependency_relation`` is an ``expression`` and must satisfy the
   Ada syntax.  The non-terminals of the ``dependency_relation``
   grammar, except ``dependency_clause``, are also ``expressions``.
#. An ``aspect_specification`` of a subprogram may have at most one
   ``dependency_aspect``.
#. An ``import`` must have an effective mode of **in** or **in out**.
#. An ``export`` must have an effective mode of **in out** or **out**.
#. A ``moded_item`` which is both an ``import`` and an ``export``
   shall have an effective mode of **in out**.
#. A **null** ``dependency_relation`` indicates that there is not an
   ``import`` nor an ``export``.
#. A ``function_result`` may not appear in the ``dependency_relation``
   of a procedure.
#. There can be at most one ``export_list`` which is a **null** symbol
   and if it exists it must be the ``export_list`` of the last
   ``dependency_clause`` in the ``dependency_relation``.  An
   ``import`` which is in an ``import_list`` of a **null** export may
   not appear in another ``import_list`` of the same
   ``dependency_relation``.
#. Every ``moded_item`` of a subprogram shall appear at least once in the
   dependency relation.  A subcomponent of a composite object is
   sufficient to show an appearance.
#. An ``export`` may be a subcomponent provided the containing object
   is not an ``export`` in the same ``dependency_relation``.  As long
   as this rule is satisfied, different subcomponents of a composite
   object may appear each as a distinct ``export`` and, for array
   subcomponents, a single, e.g. element A (I), cannot appear more
   than once as an ``export``, whereas elements A (I) and A (J) are
   considered as distinct and may both appear as an export even
   though I my equal J.
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
   designates that each ``export`` in the ``export-list`` has a
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
it used purely for static analyses purposes and is not executed.


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

.. note:: RCC. procedure S does not make sense.  It has X and A as both formal
   parameter and global, so can't be right. Assign TJJ to correct.

Proof Functions
~~~~~~~~~~~~~~~

.. todo:: TN LA24-011 is open for someone to propose a strawman design.
   Target: D2.


Formal Parameter Modes
----------------------

See Appendix :ref: `restrictions-and-profiles-label` for restrictions that may be applied.


Subprogram Bodies
-----------------


Conformance Rules
~~~~~~~~~~~~~~~~~

No extensions or restrictions.

.. note:: RCC. I can't think of any reason that we might need any
   extension or restrictions in this section.  Anyone disagree?

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
   determining the final value of at least one ``export``.  If more than
   one subcomponent of the same object appears in such a
   ``mode_specification`` then all the rule applies to all mentioned
   subcomponents.

.. todo:: Conditional mode specifications which have to be checked by proof. Target: rel2+.

Global Aspects
~~~~~~~~~~~~~~

If subprogram does not have a separate declaration its body or body
stub may have a ``global_aspect`` in its aspect specification where
the same rules as for a ``global_aspect`` in a subprogram declaration
apply.  When a subprogram has a ``global_aspect`` either in its
declaration or its body or body stub the rules and semantics given
below should be satisfied by the implementation of its body.

If the subprogram has a ``refined_global_aspect`` (see
:ref:`refined-global-aspect`), this has to be checked for consitency
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

.. todo:: rules for working out an implicit global aspect. RCC comment: not
   sure this is needed here.  What are these rules? Why does the reader of 
   the LRM need to see them? Target: clarify or remove this ToDo for D1/CDR.

Param Aspects
~~~~~~~~~~~~~

If subprogram does not have a separate declaration its body or body
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

If subprogram does not have a separate declaration its body or body
stub may have a ``dependency_aspect`` in its aspect specification
where the same rules as for a ``dependency_aspect`` in a subprogram
declaration apply.  When a subprogram has a ``dependency_aspect``
either in its declaration or its body or body stub the rules and
semantics given below should be satisfied by the implementation of its
body.

If the subprogram has a ``refined_dependency_aspect`` (see
:ref:`refined-dependency-aspect`), this has to be checked for consitency
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
   the implicit one determiined from the body of the function.


.. centered:: *Checked by Proof*

.. todo:: conditional dependencies and subcomponents. Target: rel2+.


Subprogram Calls
----------------

A call is in |SPARK| only if it resolves statically to a subprogram whose
declaration view is in |SPARK| (whether the call is dispatching or not).

Parameter Associations
~~~~~~~~~~~~~~~~~~~~~~

.. todo:: possible restrictions regarding not mixing named and
   positional parameters, requiring all, or more than a certain
   number of parameters require named association, or more than one
   parameter of the same type requires named association. RCC comment:
   Is it worth restricting these things if they don't impact verifiability?
   Target: D2. 


Abstract and Refined Views
^^^^^^^^^^^^^^^^^^^^^^^^^^

There are two possible views of a subprogram P declared in the visible
part of a package.  An abstract view and a refined view.  The abstract
view is that seen by the client of the package.  The refined view is
seen within the body of the package and its private descendents.


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
object and problems arise when one of names is used to update the
object.

A common place for aliasing to be introduced is through the *actual
parameters* (see Ada LRM 6.4.1) and between *actual parameters* and
*global variables* in a procedure call.  Extra semantic rules are
given that avoid the possibility of aliasing through *actual
parameters* and *global variables*.  A function is not allowed to have
side-effects and cannot update an *actual parameter* or *global
variable*.  Therefore a function call cannot introduce aliasing and
are excluded from the anti-aliasing rules given below for procedure
calls.

.. todo:: Relax rules for aliasing based on the following paragraph.
   RCC comment: I am happy that these rules are OK given the definition
   of "overlapping" below. Target: D1/CDR. Assign: ??? (probably TJJ and YM
   to agree this is all OK.)

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
aspect is used which is deduced by analysing the bodies of the called
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
      and the body of P has a ``refined_global_aspect`` (need a
      reference here???) then in applying the anti-aliasing rules to
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

The dependency relation of a subprgram is used to determine the effect
of a call to a subprogram in terms of the flows of information through
the subprogram.  

#. A subprogram P declared in the visible part of a package, called
   within the body or private descendents of the package and P
   requires a ``refined_dependency_aspect`` because of
   state_refinement, the following will be used as the dependency
   relation of P:

   * the ``dependency_relation`` from the explicit
     ``refined_dependency_aspect`` if one is present;
   * for a function which does not have an explicit
     ``dependency_aspect``, the assumed dependency relation is that
     its result is dependent on all of its imports;
   * for a procedure which does not does not have an explicit
     ``refined_dependency_aspect`` but the the subprogram
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
   * for a procedure which does not does not have an explicit
     ``dependency_aspect`` but the subprogram has a proper body, the
     implicit dependency relation synthesized from the subprogram code
     will be used.
   * for a procedure which has neither a ``dependency_aspect`` nor a
     proper body the conservative dependency relation that is used is
     that every ``export`` is dependent on every ``import``.

Return Statements
-----------------

No extensions or restrictions.

.. note:: RCC. Is this really true? I don't understand the use of the extended
   return statement, so advice here is welcome!  Target: D1/CDR.

Overloading of Operators
------------------------

No extensions or restrictions.

.. note:: RCC. Anything to add here anyone? Target: D1/CDR.

Null Procedures
---------------

No extensions or restrictions.

.. note:: RCC. Anything to add here anyone? Target: D1/CDR.

Expression Functions
--------------------

No extensions or restrictions.

.. note:: RCC. Anything to add here anyone? Target: D1/CDR.



