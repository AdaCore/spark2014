Subprograms
===========

Subprogram Declarations
-----------------------

We distinguish the *declaration view* introduced by a ``subprogram_declaration``
from the *implementation view* introduced by a ``subprogram_body`` or an
``expression_function_declaration``. For subprograms that are not declared by
a ``subprogram_declaration``, the ``subprogram_body`` or
``expression_function_declaration`` also introduces a declaration view which
may be in |SPARK| even if the implementation view is not.

.. index:: subprogram with side effects

A *subprogram with side effects* is either a procedure, a protected entry, or a
function with side effects (see :ref:`Functions With Side Effects`). A
subprogram with side effects may have output parameters, write global
variables, raise exceptions and not terminate.

Rules are imposed in |SPARK| to ensure that the execution of a function call
does not modify any variables declared outside of the function, unless it is a
function with side effects.  Outside of this special case, it follows as a
consequence of these rules that the evaluation of any |SPARK| expression is
side-effect free.

.. index:: global item

We also introduce the notion of a *global item*, which is a name that denotes a
global object or a state abstraction (see :ref:`Abstract_State Aspects`). Global items
are presented in Global aspects (see :ref:`Global Aspects`).

.. index:: entire object

An *entire object* is an object which is not a subcomponent of a larger
containing object.  More specifically, an *entire object* is
an object declared by an ``object_declaration`` (as opposed to, for example,
a slice or the result object of a function call) or a formal parameter of
a subprogram. In particular, a component of a protected unit is not
an *entire object*.

.. container:: heading

   Static Semantics

1. The *exit* value of a global item or parameter of a subprogram is its
   value immediately following the call of the subprogram.

2. The *entry* value of a global item or parameter of a subprogram is its
   value at the call of the subprogram.

.. index:: subprogram output

3. An *output* of a subprogram is a global item or parameter whose final value,
   or the final value of any of its reachable parts (see :ref:`Access Types`),
   may be updated by a
   successful call to the subprogram. The result of a
   function is also an output.  A global item or parameter which is an external
   state with the property Async_Readers => True, and for which intermediate
   values are written during an execution leading to a successful call, is also
   an output even if the final state is the same as the initial state. (see
   :ref:`External State`). [On the contrary, a global item or parameter is not
   an output of the subprogram if it is updated only on paths that lead to a
   statement raising an unexpected exception or to a
   ``pragma Assert (statically_False)``.]

.. index:: subprogram input

4. An *input* of a subprogram is a global item or parameter whose
   initial value (or that of any of its reachable parts -
   see :ref:`Access Types`) may be used in determining the exit value of an
   output of the subprogram.  For a global item or parameter which is
   an external state with Async_Writers => True, each successive value
   read from the external state is also an input of the subprogram
   (see :ref:`External State`).  As a special case, a global item or
   parameter is also an input if it is mentioned in a
   ``null_dependency_clause`` in the Depends aspect of the subprogram
   (see :ref:`Depends Aspects`).

5. An output of a subprogram is said to be *fully initialized* by a call
   if all parts of the output are initialized as a result of any successful
   execution of a call of the subprogram. In the case of a parameter X
   of a class-wide type T'Class, this set of "all parts" is not limited
   to the (statically known) parts of T. For example, if the underlying
   dynamic tag of X is T2'Tag, where T2 is an extension of T that declares
   a component C, then C would be included in the set. In this case,
   this set of "all parts" is not known statically.
   [In order to fully initialize such a parameter, it is necessary
   to use some form of dispatching assignment. This can be done by either
   a direct (class-wide) assignment to X, passing X as an actual out-mode
   parameter in a call where the formal parameter is of a class-wide type,
   or passing X as a controlling out-mode parameter in a dispatching call.]
   The meaning of "all parts" in the case of a parameter of a specific
   tagged type is determined by the applicable Extensions_Visible aspect
   (see :ref:`Extensions_Visible Aspects`).
   [A state abstraction cannot be fully initialized by initializing
   individual constituents unless its refinement is visible.]

.. container:: heading

   Legality Rules


6. The declaration of a function without side effects shall not have a
   ``parameter_specification`` with a mode of **out** or **in out** unless it
   has a mode of **in out** and is the first parameter of a borrowing traversal
   function (see :ref:`Access Types`). This rule also applies to a
   ``subprogram_body`` for a function without side effects for which no explicit
   declaration is given. A function without side effects shall have no outputs
   other than its result. [A subprogram parameter of mode **in out** shall not
   be an output of its borrowing traversal function].

7. A subprogram parameter of mode **in** shall not be an output of its
   subprogram unless the type of the parameter is an access type and the
   subprogram is a subprogram with side effects.

.. container:: heading

   Verification Rules

8. At the point of a call, all inputs of the callee except for those that have
   relaxed initialization (see :ref:`Relaxed Initialization`) shall be
   fully initialized. Similarly, upon return from a call all outputs of the
   callee except for those that have relaxed initialization shall be
   fully initialized.

9. If a call propagates an exception, all global outputs of the callee and all
   output parameters which either have a *by reference* type or are marked as
   aliased shall be fully initialized when the exception is propagated
   except for those that have relaxed initialization.

10. If a call exits the whole program, all global outputs of the callee
    mentioned in the boolean expression of its aspect Program_Exit outside of
    a reference to the Old attribute shall be fully initialized when the
    program is exited except for those that have relaxed initialization.

11. A function without side effects shall always return normally.

12. A call to a ghost procedure occurring outside of a ghost context shall
    always return normally.

.. index:: precondition, postcondition

Preconditions and Postconditions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. container:: heading

   Legality Rules


1. The corresponding expression for an inherited Pre'Class or Post'Class of an
   inherited subprogram S of a tagged type T shall not call a non-inherited
   primitive function of type T.

[The notion of corresponding expression is defined in Ada RM 6.1.1(18/4) as
follows: If a Pre'Class or Post'Class aspect is specified for a primitive
subprogram S of a tagged type T, or such an aspect defaults to True, then a
corresponding expression also applies to the corresponding primitive subprogram
S of each descendant of T.]

[The rationale for this rule is that, otherwise, if the contract applicable to
an inherited subprogram changes due to called subprograms in its contract being
overridden, then the inherited subprogram would have to be re-verified for the
derived type. This rule forbids the cases that require re-verification.]


2. The Pre aspect shall not be specified for a primitive operation of a
   type T at a point where T is tagged. [Pre'Class
   should be used instead to express preconditions.]

[The rationale for this rule is that, otherwise, the combination of dynamic
semantics and verification rules below would force an identical Pre'Class
each time Pre is used on a dispatching operation.]


3. A subprogram_renaming_declaration shall not declare a primitive
   operation of a tagged type.

[Consider

.. code-block:: ada

   package Outer is
      type T is tagged null record;
      package Nested is
         procedure Op (X : T) with Pre => ..., Post => ... ;
         -- not a primitive, so Pre/Post specs are ok
      end Nested;
      procedure Renamed_Op (X : T) renames Nested.Op; -- illegal
   end Outer;

Allowing this example in SPARK would introduce a case of a dispatching
operation which is subject to a Pre (and Post) aspect specification.
This rule is also intended to avoid problematic interactions between
the Pre/Pre'Class/Post/Post'Class aspects of the renamed subprogram
and the Pre'Class/Post'Class inheritance associated with the declaration
of a primitive operation of a tagged type.

Note that a dispatching subprogram can be renamed as long as the renaming
does not itself declare a dispatching operation. Note also that this rule
would never apply to a renaming-as-body.]


.. container:: heading

   Verification Rules

For a call on a nondispatching operation,
a verification condition is introduced (as
for any run-time check) to ensure that the specific precondition
check associated with the statically denoted callee will succeed.
Upon entry to such a subprogram, the specific preconditions of
the subprogram may then be assumed.

For a call (dispatching or not) on a dispatching operation,
a verification condition is introduced (as
for any run-time check) to ensure that the class-wide precondition
check associated with the statically denoted callee will succeed.

The verification condition associated with the specific precondition
of a dispatching subprogram is imposed on the callee, as opposed to
on callers of the subprogram. Upon entry to a subprogram, the
class-wide preconditions of the subprogram may be assumed. Given
this, the specific preconditions of the subprogram must be proven.

The callee is responsible for discharging the verification conditions associated
with any postcondition checks, class-wide or specific. The success of these
checks may then be assumed by the caller.

.. index:: verification condition; on dispatching operation

In the case of an overriding dispatching operation whose Pre'Class
attribute is explicitly specified, a verification condition is introduced
to ensure that the specified Pre'Class condition is implied by the
Pre'Class condition of the overridden inherited subprogram(s). Similarly,
in the case of an overriding dispatching operation whose Post'Class
attribute is explicitly specified, a verification condition is introduced
to ensure that the specified Post'Class condition implies the
Post'Class condition of the overridden inherited subprogram(s).
[These verification conditions do not correspond to any run-time check.
They are intended to, in effect, require users to make explicit the implicit
disjunction/conjunction of class-wide preconditions/postconditions
that is described in Ada RM 6.1.1.]

Subprogram Contracts
~~~~~~~~~~~~~~~~~~~~

The syntax of all language-defined subprogram contracts is extended to allow
splitting the contract into one or more parts associated with an assertion level
(see :ref:`Pragma Assertion_Level`):

.. container:: heading

   Syntax

::
   level_and_expression ::= assertion_level => boolean_expression
   level_and_expression_list ::= level_and_expression[, level_and_expression_list]

The ``aspect_definition`` of subprogram contracts can be either a boolean
expression or a ``level_and_expression_list``. In the second case, the boolean
expressions are handled similarly to the boolean expression of the first case
with respect to legality rules and name resolution.

In order to extend Ada's support for specification of subprogram contracts
(e.g., the Pre and Post) by providing more precise and/or concise contracts, the
|SPARK| aspects, Global, Depends, and Contract_Cases are defined.

.. container:: heading

   Legality Rules


1. The Global, Depends and Contract_Cases aspects may be
   specified for a subprogram with an ``aspect_specification``. More
   specifically, such aspect specifications are allowed in the same
   contexts as Pre or Post aspect specifications. [In particular,
   these aspects may be specified for a generic subprogram but not
   for an instance of a generic subprogram.]

2. The Global and Depends (but not Contract_Cases) aspects may be specified for
   an abstract subprogram.

3. The Global, Depends and Contract_Cases aspects shall not be specified for a
   null procedure.

See section :ref:`Contract Cases` for further detail on Contract_Case aspects, section
:ref:`Global Aspects` for further detail on Global aspects and section :ref:`Depends Aspects`
for further detail on Depends aspects.

.. container:: heading

   Dynamic Semantics

4. The checks associated with a contract containing assertion levels are
   performed in a similar fashion to regular contracts for each boolean
   expression. The associated assertion level is taken into account when
   determining whether each expression is
   enabled. [Intuitively, the boolean expressions of a contract containing
   assertion levels are joined together using a conjunction.]

.. index:: Contract_Cases

Contract Cases
~~~~~~~~~~~~~~

The Contract_Cases aspect provides a structured way of defining a subprogram
contract using mutually exclusive subcontract cases. The final case in the
Contract_Case aspect may be the keyword **others** which means that, in a
specific call to the subprogram, if all the ``conditions`` are False this
``contract_case`` is taken. If an **others** ``contract_case`` is not specified,
then in a specific call of the subprogram exactly one of the guarding
``conditions`` should be True.

A Contract_Cases aspect may be used in conjunction with the
language-defined aspects Pre and Post in which case the precondition
specified by the Pre aspect is augmented with a check that exactly one
of the ``conditions`` of the ``contract_case_list`` is satisfied and
the postcondition specified by the Post aspect is conjoined with
conditional expressions representing each of the ``contract_cases``.
For example:

.. code-block:: ada

 procedure P (...)
    with Pre  => General_Precondition,
         Post => General_Postcondition,
         Contract_Cases => (A1 => B1,
                            A2 => B2,
                            ...
                            An => Bn);

is short hand for

.. code-block:: ada

   procedure P (...)
     with Pre  => General_Precondition
                    and then Exactly_One_Of (A1, A2, ..., An),
          Post => General_Postcondition
                    and then (if A1'Old then B1)
                    and then (if A2'Old then B2)
                    and then ...
                    and then (if An'Old then Bn);


where

  A1 .. An are Boolean expressions involving the entry values of
  formal parameters and global objects and

  B1 .. Bn are Boolean expressions that may also use the exit values of
  formal parameters, global objects and results.

  ``Exactly_One_Of(A1,A2...An)`` evaluates to True if exactly one of its inputs evaluates
  to True and all other of its inputs evaluate to False.

The Contract_Cases aspect is specified with an ``aspect_specification`` where
the ``aspect_mark`` is Contract_Cases and the ``aspect_definition`` must follow
the grammar of ``contract_case_list`` given below.


.. container:: heading

   Syntax

::

   contract_case_list  ::= (contract_case {, contract_case})
   contract_case       ::= condition => consequence
                         | others => consequence

where

   ``consequence ::=`` *Boolean_*\ ``expression``

Similarly to other subprogram contracts, the ``aspect_specification`` of a
Contract_Cases aspect can be a list of associations of an assertion level
and a ``contract_case_list`` instead. In this case, each ``contract_case_list``
is handled as for simple Contract_Cases aspects, but their execution semantic
is governed by the associated assertion level.


.. container:: heading

   Legality Rules


1. A Contract_Cases aspect may have at most one **others**
   ``contract_case`` and if it exists it shall be the last one in the
   ``contract_case_list``.


2. A ``consequence`` expression is considered to be a postcondition
   expression for purposes of determining the legality of Old or
   Result ``attribute_references``.


.. container:: heading

   Static Semantics


3. A Contract_Cases aspect is an assertion (as defined in RM
   11.4.2(1.1/3)); its assertion expressions are as described
   below. Contract_Cases may be specified as an
   ``assertion_aspect_mark`` in an Assertion_Policy pragma.


.. container:: heading

   Dynamic Semantics


4. Upon a call of a subprogram which is subject to an enabled
   Contract_Cases aspect, Contract_Cases checks are
   performed as follows:

   * Immediately after the specific precondition expression is
     evaluated and checked (or, if that check is disabled, at the
     point where the check would have been performed if it were
     enabled), all of the ``conditions`` of the ``contract_case_list``
     are evaluated in textual order. A check is performed that exactly
     one (if no **others** ``contract_case`` is provided) or at most
     one (if an **others** ``contract_case`` is provided) of these
     ``conditions`` evaluates to True; Assertions.Assertion_Error is
     raised if this check fails.

   * Immediately after the specific postcondition expression is
     evaluated and checked (or, if that check is disabled, at the
     point where the check would have been performed if it were
     enabled), exactly one of the ``consequences`` is evaluated. The
     ``consequence`` to be evaluated is the one corresponding to the
     one ``condition`` whose evaluation yielded True (if such a
     ``condition`` exists), or to the **others** ``contract_case`` (if
     every ``condition``\ 's evaluation yielded False). A check
     is performed that the evaluation of the selected ``consequence``
     evaluates to True; Assertions.Assertion_Error is raised if this
     check fails.


5. If an Old ``attribute_reference`` occurs within a ``consequence``
   other than the ``consequence`` selected for (later) evaluation
   as described above, then the associated implicit constant declaration
   (see Ada RM 6.1.1) is not elaborated. [In particular, the prefix of the
   Old ``attribute_reference`` is not evaluated].


.. container:: heading

   Verification Rules

The verification conditions associated with the Contract_Cases runtime checks
performed at the beginning of a call are assigned in the same way
as those associated with a specific precondition check. More specifically,
the verification condition is imposed on the caller or on the callee depending
on whether the subprogram in question is a dispatching operation.

.. container:: heading

   Examples

.. code-block:: ada

   -- This subprogram is specified using a Contract_Cases aspect.
   -- The prover will check that the cases are disjoint and
   -- cover the domain of X.
   procedure Incr_Threshold (X : in out Integer; Threshold : in Integer)
     with Contract_Cases => (X < Threshold  => X = X'Old + 1,
                             X >= Threshold => X = X'Old);

   -- This is the equivalent specification not using Contract_Cases.
   -- It is noticeably more complex and the prover is not able to check
   -- for disjoint cases or that the domain of X is covered.
   procedure Incr_Threshold_1 (X : in out Integer; Threshold : in Integer)
     with Pre  => (X < Threshold and not (X >= Threshold))
                     or else (not (X < Threshold) and X >= Threshold),
          Post => (if X'Old < Threshold then X = X'Old + 1
                   elsif X'Old >= Threshold then X = X'Old);

   -- Contract_Cases can be used in conjunction with pre and postconditions.
   procedure Incr_Threshold_2 (X : in out Integer; Threshold : in Integer)
     with Pre  => X in 0 .. Threshold,
          Post => X >= X'Old,
          Contract_Cases => (X < Threshold => X = X'Old + 1,
                             X = Threshold => X = X'Old);


.. index:: Global

Global Aspects
~~~~~~~~~~~~~~

A Global aspect of a subprogram lists the global items whose values
are used or affected by a call of the subprogram.

The Global aspect shall only be specified for the initial declaration of a
subprogram (which may be a declaration, a body or a body stub), of a
protected entry, or of a task unit.
The implementation of a subprogram body shall be consistent with the
subprogram's Global aspect. Similarly, the implementation of an entry or
task body shall be consistent with the entry or task's Global aspect.

Note that a Refined_Global aspect may be applied to a subprogram body when
using state abstraction; see section :ref:`Refined_Global Aspects` for further
details.

The Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Global and the ``aspect_definition`` must
follow the grammar of ``global_specification``

For purposes of the rules concerning the Global, Depends, Refined_Global, and
Refined_Depends aspects, when any of these aspects are specified for a
task unit the task unit's body is considered to be the body of a
nonreturning procedure and the current instance of the task unit is
considered to be a formal parameter (of that notional procedure)
of mode **in out**. [For example, rules which refer to the
"subprogram body" refer, in the case of a task unit, to the
task body.]
[Because a task (even a
discriminated task) is effectively a constant, one might think that a
mode of **in** would make more sense. However, the current instance of
a task unit is, strictly speaking, a variable; for example, it may be
passed as an actual **out** or **in out** mode parameter in a call.]
The Depends and Refined_Depends aspect of a task unit T need not mention
this implicit parameter; an implicit specification of "T => T" is
assumed, although this may be confirmed explicitly.

Similarly, for purposes of the rules concerning the Global, Refined_Global,
Depends, and Refined_Depends aspects as they apply to protected operations,
the current instance of the enclosing protected unit is considered to be
a formal parameter (of mode **in** for a protected function, of mode
**in out** otherwise) and a protected entry is considered to be
a protected procedure. [For example, rules which refer to the
"subprogram body" refer, in the case of a protected entry, to the
entry body. As another example, the Global aspect of a subprogram nested
within a protected operation might name the current instance of the
protected unit as a global in the same way that it might name any
other parameter of the protected operation.]

[Note that AI12-0169 modifies the Ada RM syntax for an ``entry_body``
to allow an optional ``aspect_specification`` immediately before the
``entry_barrier``. This is relevant for aspects such as Refined_Global
and Refined_Depends.]

.. container:: heading

   Syntax


::

   global_specification        ::= (moded_global_list {, moded_global_list})
                                 | global_list
                                 | null_global_specification
   moded_global_list           ::= mode_selector => global_list
   global_list                 ::= global_item
                                 | (global_item {, global_item})
   mode_selector               ::= Input | Output | In_Out | Proof_In
   global_item                 ::= name
   null_global_specification   ::= null


.. container:: heading

   Static Semantics


1. A ``global_specification`` that is a ``global_list`` is shorthand for a
   ``moded_global_list`` with the ``mode_selector`` Input.


2. A ``global_item`` is *referenced* by a subprogram if:

   * It denotes an input or an output of the subprogram, or;

   * Its entry value is used to determine the value of an assertion
     expression within the subprogram, or;

   * Its entry value is used to determine the value of an assertion
     expression within another subprogram that is called either directly or
     indirectly by this subprogram.


3. A ``null_global_specification`` indicates that the subprogram does not
   reference any ``global_item`` directly or indirectly.


4. If a subprogram's Global aspect is not otherwise specified and either

   * the subprogram is a library-level subprogram declared in a library
     unit that is declared pure (i.e., a subprogram to which the
     implementation permissions of Ada RM 10.2.1 apply); or

   * a Pure_Function pragma applies to the subprogram

   then a Global aspect of *null* is implicitly specified for the subprogram.


.. container:: heading

   Name Resolution Rules


5. A ``global_item`` shall denote an entire object or a state abstraction.
   [This is a name resolution rule because a ``global_item`` can unambiguously
   denote a state abstraction even if a function having the same fully qualified
   name is also present].


.. container:: heading

   Legality Rules


6. The Global aspect may only be specified for the initial declaration of a
   subprogram (which may be a declaration, a body or a body stub), of a
   protected entry, or of a task unit.


7. A ``global_item`` occurring in a Global aspect specification of a subprogram
   shall not denote a formal parameter of the subprogram.


8. A ``global_item`` shall not denote a state abstraction whose
   refinement is visible. [A state abstraction cannot be named within
   its enclosing package's body other than in its refinement. Its
   constituents shall be used rather than the state abstraction.]


9. Each ``mode_selector`` shall occur at most once in a single
   Global aspect.


10. A function without side effects shall not have a ``mode_selector`` of
    Output or In_Out in its Global aspect.


11. A user-defined primitive equality operation on a record type shall have a
    Global aspect of ``null``, unless the record type has only limited views
    (see :ref:`Overloading of Operators`).

    [This avoids the case where such a record type is a component of another
    composite type, whose predefined equality operation now depends on
    variables through the primitive equality operation on its component.]


12. The ``global_items`` in a single Global aspect specification shall denote
    distinct entities. Additionally, if a ``global_item`` is a state
    abstraction, none of its constituents shall appear as a ``global_item`` in
    the same Global aspect specification.


13. If a subprogram is nested within another and if the
    ``global_specification`` of the outer subprogram has an entity
    denoted by a ``global_item`` with a ``mode_specification`` of
    Input or the entity is a formal parameter with a mode of **in**,
    then a ``global_item`` of the ``global_specification`` of the
    inner subprogram shall not denote the same entity with a
    ``mode_selector`` of In_Out or Output.


14. A ``global_item`` occurring with mode Input in the Global aspect
    specification of a function annotated with Pure_Function aspect or pragma
    shall denote a constant object whose type is not an owning type (see
    :ref:`Access Types`).

    [This restriction ensures that two calls to the function with the same
    parameters return the same value, so that the compiler can safely apply
    corresponding optimizations.]


.. container:: heading

   Dynamic Semantics

There are no dynamic semantics associated with a Global aspect as it
is used purely for static analysis purposes and is not executed.

.. container:: heading

   Verification Rules


15. For a subprogram that has a ``global_specification``, an object (except a
    constant without variable inputs) or state abstraction that is declared
    outside the scope of the subprogram, shall only be referenced within its
    implementation if it is a ``global_item`` in the ``global_specification``.


16. A ``global_item`` shall occur in a Global aspect of a subprogram if and
    only if it denotes an entity (except for a constant without variable
    inputs) that is referenced by the subprogram.


17. Where the refinement of a state abstraction is not visible (see
    :ref:`State Refinement`) and a subprogram references one or more
    of its constituents, the constituents may be represented by a
    ``global_item`` that denotes the state abstraction in the
    ``global_specification`` of the subprogram. [The state abstraction
    encapsulating a constituent is known from the Part_Of indicator on
    the declaration of the constituent.]


18. Each entity denoted by a ``global_item`` in a
    ``global_specification`` of a subprogram that is an input or
    output of the subprogram shall satisfy the following mode
    specification rules [which are checked during analysis of the
    subprogram body]:

    * a ``global_item`` that denotes an input but not an output has a
      ``mode_selector`` of Input;

    * a ``global_item`` has a ``mode_selector`` of Output if:

      - it denotes an output but not an input, other than the use of a
        discriminant or an attribute related to a property, not its
        value, of the ``global_item`` [examples of attributes that may
        be used are A'Last, A'First and A'Length; examples of
        attributes that are dependent on the value of the object and
        shall not be used are X'Old and X'Loop_Entry] and

      - it does not have relaxed initialization
        (see :ref:`Relaxed Initialization`);

    * a ``global_item`` that denotes an output which is not an input and
      which has relaxed initialization may have a ``mode_selector`` of
      Output or In_Out;

    * otherwise the ``global_item`` denotes both an input and an output, and
      has a ``mode_selector`` of In_Out.


   [For purposes of determining whether an output of a subprogram shall have a
   ``mode_selector`` of Output or In_Out, reads of array bounds, discriminants,
   or tags of the output are ignored. Reads of array bounds, discriminants, or
   tag of any reachable part of the output are not considered either if they are
   constrained by their subtype. Similarly, for purposes of
   determining whether an entity is fully initialized as a result of any
   successful execution of the call, the mutable discriminants of the output
   itself are not considered.
   This implies that given an output of a discriminated type that is not known
   to be constrained ("known to be constrained" is defined in Ada RM 3.3), the
   discriminants of the output might or might not be updated by the call.]


19. An entity that is denoted by a ``global_item`` which is referenced
    by a subprogram but is neither an input nor an output but is only
    referenced directly, or indirectly in assertion expressions has a
    ``mode_selector`` of Proof_In.


.. index:: constant with variable inputs; in Global

20. A ``global_item`` shall not denote a constant object other than a formal
    parameter [of an enclosing subprogram] of mode **in**, a generic formal
    object of mode **in**, a constant of (named or anonymous)
    access-to-variable type, or a *constant with variable inputs*.

    If a ``global_item`` denotes a generic formal object of mode **in**,
    then the corresponding ``global_item`` in an instance of the generic
    unit may denote a constant which has no variable inputs. [This can occur
    if the corresponding actual parameter is an expression which has no
    variable inputs]. Outside of the instance, such a ``global_item`` is
    ignored. For example,

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/global_and_generics.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/global_and_generics.adb
   :language: ada
   :linenos:


21. The ``mode_selector`` of a ``global_item`` denoting a *constant with
    variable inputs* shall be ``Input`` or ``Proof_In``.


.. index:: Constant_After_Elaboration; in Global

22. The ``mode_selector`` of a ``global_item`` denoting a variable marked
    as a *constant after elaboration* shall be ``Input`` or ``Proof_In`` [,
    to ensure that such variables are only updated directly by package
    elaboration code].
    A subprogram or entry having such a ``global_item`` shall not be called
    during library unit elaboration[, to ensure only the final ("constant")
    value of the object is referenced].


.. container:: heading

   Examples

.. code-block:: ada

   with Global => null; -- Indicates that the subprogram does not reference
                        -- any global items.
   with Global => V;    -- Indicates that V is an input of the subprogram.
   with Global => (X, Y, Z);  -- X, Y and Z are inputs of the subprogram.
   with Global => (Input    => V); -- Indicates that V is an input of the subprogram.
   with Global => (Input    => (X, Y, Z)); -- X, Y and Z are inputs of the subprogram.
   with Global => (Output   => (A, B, C)); -- A, B and C are outputs of
                                           -- the subprogram.
   with Global => (In_Out   => (D, E, F)); -- D, E and F are both inputs and
                                           -- outputs of the subprogram
   with Global => (Proof_In => (G, H));    -- G and H are only used in
                                           -- assertion expressions within
                                           -- the subprogram
   with Global => (Input    => (X, Y, Z),
                   Output   => (A, B, C),
                   In_Out   => (P, Q, R),
                   Proof_In => (T, U));
                   -- A global aspect with all types of global specification


.. index:: Depends

Depends Aspects
~~~~~~~~~~~~~~~

A Depends aspect defines a *dependency relation* for a subprogram
which may be given in the ``aspect_specification`` of the subprogram.
A dependency relation is a sort of formal specification which
specifies a simple relationship between inputs and outputs of the
subprogram.  It may be used with or without a postcondition.

The Depends aspect shall only be specified for the initial declaration of a
subprogram (which may be a declaration, a body or a body stub), of a
protected entry, or of a task unit.

Unlike a postcondition, the Depends aspect must be
complete in the sense that every input and output of the subprogram
must appear in it.  A postcondition need only
specify properties of particular interest.

Like a postcondition, the dependency relation may be omitted from a
subprogram declaration when it defaults to the conservative
relation that each output depends on every input of the subprogram.  A
particular |SPARK| tool may synthesize a more accurate approximation
from the subprogram implementation if it is present (see
:ref:`Synthesis of |SPARK| Aspects`).

For accurate information flow analysis the Depends aspect should be
present on every subprogram.

A Depends aspect for a subprogram specifies for each output every
input on which it depends. The meaning of *X depends on Y* in this
context is that the input value(s) of *Y* may affect:

* the exit value of *X*; and
* the intermediate values of *X* if it is an external state
  (see section  :ref:`External State`), or if the subprogram
  is a nonreturning procedure [, possibly the notional nonreturning
  procedure corresponding to a task body].

This is written *X => Y*. As in UML, the entity at the tail of the
arrow depends on the entity at the head of the arrow.

If an output does not depend on any input this is indicated
using a **null**, e.g., *X =>* **null**. An output may be
self-dependent but not dependent on any other input. The shorthand
notation denoting self-dependence is useful here, X =>+ **null**.

Note that a Refined_Depends aspect may be applied to a subprogram body when
using state abstraction; see section :ref:`Refined_Depends Aspects` for further
details.

See section :ref:`Global Aspects` regarding how the rules given in this
section apply to protected operations and to task bodies.

The Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Depends and the ``aspect_definition`` must follow
the grammar of ``dependency_relation`` given below.


.. container:: heading

   Syntax


::

   dependency_relation    ::= null
                            | (dependency_clause {, dependency_clause})
   dependency_clause      ::= output_list =>[+] input_list
                            | null_dependency_clause
   null_dependency_clause ::= null => input_list
   output_list            ::= output
                            | (output {, output})
   input_list             ::= input
                            | (input {, input})
                            | null
   input                  ::= name
   output                 ::= name | function_result

where

   ``function_result`` is a function Result ``attribute_reference``.


.. container:: heading

   Name Resolution Rules


1. An ``input`` or ``output`` of a ``dependency_relation`` shall denote only
   an entire object or a state abstraction. [This is a name resolution rule
   because an ``input`` or ``output`` can unambiguously denote a state
   abstraction even if a function having the same fully qualified name is also
   present.]


.. container:: heading

   Legality Rules


2. The Depends aspect shall only be specified for the initial declaration of a
   subprogram (which may be a declaration, a body or a body stub), of a
   protected entry, or of a task unit.


3. An ``input`` or ``output`` of a ``dependency_relation`` shall not denote a
   state abstraction whose refinement is visible [a state abstraction cannot be
   named within its enclosing package's body other than in its refinement].


4. The *explicit input set* of a subprogram is the set of formal parameters of
   the subprogram of mode **in** and **in out** along with the entities denoted
   by ``global_items`` of the Global aspect of the subprogram with a
   ``mode_selector`` of Input and In_Out.


5. The *input set* of a subprogram is the explicit input set of the
   subprogram augmented with those formal parameters of mode **out** and
   those ``global_items`` with a ``mode_selector`` of Output having discriminants,
   array bounds, or a tag which can be read and whose values are not
   implied by the subtype of the parameter. More specifically, it includes formal
   parameters of mode **out** and ``global_items`` with a ``mode_selector`` of
   Output which are of an unconstrained array subtype, an unconstrained
   discriminated subtype, or a tagged type (with one exception). The exception
   mentioned in the previous sentence is in the case where the formal
   parameter is of a specific tagged type and the applicable Extensions_Visible
   aspect is False. In that case, the tag of the parameter cannot be read
   and so the fact that the parameter is tagged does not cause it to
   included in the subprogram's *input_set*, although it may be included
   for some other reason (e.g., if the parameter is of an unconstrained
   discriminated subtype).


6. The *output set* of a subprogram is the set of formal parameters of the
   subprogram of mode **in out** and **out** along with the entities denoted by
   ``global_items`` of the Global aspect of the subprogram with a
   ``mode_selector`` of In_Out and Output and (for a function) the
   ``function_result`` or (for a subprogram with side effects) the set of formal
   parameters of the subprogram of mode **in** of an access-to-variable type.


7. The entity denoted by each ``input`` of a ``dependency_relation`` of a
   subprogram shall be a member of the input set of the subprogram.


8. Every member of the explicit input set of a subprogram shall be denoted by
   at least one ``input`` of the ``dependency_relation`` of the subprogram.


9. The entity denoted by each ``output`` of a ``dependency_relation`` of a
   subprogram shall be a member of the output set of the subprogram.


10. Every member of the output set of a subprogram shall be denoted by exactly
    one ``output`` in the ``dependency_relation`` of the subprogram.


11. For the purposes of determining the legality of a Result
    ``attribute_reference``, a ``dependency_relation`` is considered
    to be a postcondition of the function to which the enclosing
    ``aspect_specification`` applies.


12. In a ``dependency_relation`` there can be at most one
    ``dependency_clause`` which is a ``null_dependency_clause`` and if
    it exists it shall be the last ``dependency_clause`` in the
    ``dependency_relation``.


13. An entity denoted by an ``input`` which is in an ``input_list`` of
    a ``null_dependency_clause`` shall not be denoted by an ``input``
    in another ``input_list`` of the same ``dependency_relation``.


14. The ``inputs`` in a single ``input_list`` shall denote distinct entities.


15. A ``null_dependency_clause`` shall not have an ``input_list`` of **null**.


.. container:: heading

   Static Semantics


16. A ``dependency_clause`` with a "+" symbol in the syntax
    ``output_list`` =>+ ``input_list`` means that each ``output`` in
    the ``output_list`` has a *self-dependency*, that is, it is
    dependent on itself. [The text (A, B, C) =>+ Z is shorthand for
    (A => (A, Z), B => (B, Z), C => (C, Z)).]


17. A ``dependency_clause`` of the form A =>+ A has the same meaning
    as A => A.  [The reason for this rule is to allow the short hand:
    ((A, B) =>+ (A, C)) which is equivalent to (A => (A, C), B => (A,
    B, C)).]


18. A ``dependency_clause`` with a **null** ``input_list`` means that
    the final value of the entity denoted by each ``output`` in the
    ``output_list`` does not depend on any member of the input set of
    the subprogram (other than itself, if the ``output_list`` =>+
    **null** self-dependency syntax is used).


19. The ``inputs`` in the ``input_list`` of a
    ``null_dependency_clause`` may be read by the subprogram but play
    no role in determining the values of any outputs of the
    subprogram.


20. A Depends aspect of a subprogram with a **null**
    ``dependency_relation`` indicates that the subprogram has no
    ``inputs`` or ``outputs``.  [From an information flow analysis
    viewpoint it is a null operation (a no-op).]


21. A function without side effects without an explicit Depends aspect
    specification has the default ``dependency_relation`` that its result is
    dependent on all of its inputs. [Generally an explicit Depends aspect is
    not required for a function declaration.]


22. A subprogram with side effects without an
    explicit Depends aspect specification has a
    default ``dependency_relation`` that each member of its output set
    is dependent on every member of its input set. [This conservative
    approximation may be improved by analyzing the body of the
    subprogram if it is present.]


.. container:: heading

   Dynamic Semantics

There are no dynamic semantics associated with a Depends aspect
as it is used purely for static analysis purposes and is not executed.

.. container:: heading

   Verification Rules


23. Each entity denoted by an ``output`` given in the Depends aspect
    of a subprogram shall be an output in the implementation of the
    subprogram body and the output shall depend on all, but only, the
    entities denoted by the ``inputs`` given in the ``input_list``
    associated with the ``output``.


24. Each output of the implementation of the subprogram body is denoted by
    an ``output`` in the Depends aspect of the subprogram.


25. Each input of the implementation of a subprogram body is denoted by an
    ``input`` of the Depends aspect of the subprogram.


26. If not all parts of an output are updated, then the updated entity is
    dependent on itself as the parts that are not updated have their
    current value preserved.

    [In the case of a parameter of a tagged type (specific or class-wide),
    see the definition of "fully initialized" for a clarification of what
    the phrase "all parts" means in the preceding sentence.]



.. container:: heading

   Examples

.. code-block:: ada

   procedure P (X, Y, Z in : Integer; Result : out Boolean)
     with Depends => (Result => (X, Y, Z));
   -- The exit value of Result depends on the entry values of X, Y and Z

   procedure Q (X, Y, Z in : Integer; A, B, C, D, E : out Integer)
     with Depends => ((A, B) => (X, Y),
                      C      => (X, Z),
                      D      => Y,
                      E      => null);
   -- The exit values of A and B depend on the entry values of X and Y.
   -- The exit value of C depends on the entry values of X and Z.
   -- The exit value of D depends on the entry value of Y.
   -- The exit value of E does not depend on any input value.

   procedure R (X, Y, Z : in Integer; A, B, C, D : in out Integer)
     with Depends => ((A, B) =>+ (A, X, Y),
                      C      =>+ Z,
                      D      =>+ null);
   -- The "+" sign attached to the arrow indicates self-dependency, that is
   -- the exit value of A depends on the entry value of A as well as the
   -- entry values of X and Y.
   -- Similarly, the exit value of B depends on the entry value of B
   -- as well as the entry values of A, X and Y.
   -- The exit value of C depends on the entry value of C and Z.
   -- The exit value of D depends only on the entry value of D.

   procedure S
     with Global  => (Input  => (X, Y, Z),
                      In_Out => (A, B, C, D)),
          Depends => ((A, B) =>+ (A, X, Y, Z),
                      C      =>+ Y,
                      D      =>+ null);
   -- Here globals are used rather than parameters and global items may appear
   -- in the Depends aspect as well as formal parameters.

   function F (X, Y : Integer) return Integer
     with Global  => G,
          Depends => (F'Result => (G, X),
                      null     => Y);
   -- Depends aspects on functions are only needed for special cases like here where the
   -- parameter Y has no discernible effect on the result of the function.

Global and Depends Aspects of Dispatching Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Additional rules apply to the Global and Depends aspects on a dispatching
subprogram, in order to ensure that the effects of dynamically calling an
overriding subprogram are properly captured by the aspects of the statically
denoted callee.

.. container:: heading

   Static Semantics

1. A Global aspect specification G2 is said to be
   a *valid overriding* of another such specification, G1, if the following
   conditions are met:

   * each Input-mode item of G2 is an Input-mode or an In_Out-mode
     item of G1 or a direct or indirect constituent thereof; and

   * each In_Out-mode item of G2 is an In_Out-mode item of G1 or a
     direct or indirect constituent thereof; and

   * each Output-mode item of G2 is an Output-mode or In_Out-mode item of G1
     or a direct or indirect constituent thereof; and

   * each Output-mode item of G1 which is not a state abstraction whose
     refinement is visible at the point of G2 is an Output-mode item of G2; and

   * for each Output-mode item of G1 which is a state abstraction whose
     refinement is visible at the point of G2, each direct or indirect
     constituent thereof is an Output-mode item of G2.

2. A Depends aspect specification D2 is said to be a
   *valid overriding* of another such specification, D1, if the set of
   dependencies of D2 is a subset of the dependencies of D1 or, in the
   case where D1 mentions a state abstraction whose refinement is
   visible at the point of D2, if D2 is derivable from such a subset
   as described in :ref:`Refined_Depends Aspects`.


.. container:: heading

   Legality Rules

3. The Global aspect of an overriding subprogram shall be a valid overriding
   of the Global aspect(s) of the overridden inherited subprogram(s).

4. The Depends aspect of an overriding subprogram shall be a valid
   overriding of the Depends aspect(s) of the overridden inherited
   subprogram(s).

.. index:: Extensions_Visible

Extensions_Visible Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~

The Extensions_Visible aspect provides a mechanism for ensuring that "hidden"
components of a formal parameter of a specific tagged type are unreferenced.
For example, if a formal parameter of a specific tagged type T is converted to
a class-wide type and then used as a controlling operand in a dispatching call,
then the (dynamic) callee might reference components of the parameter which are
declared in some extension of T. Such a use of the formal parameter could be
forbidden via an Extensions_Visible aspect specification as described
below. The aspect also plays a corresponding role in the analysis of callers of
the subprogram.

.. container:: heading

   Static Semantics

1. Extensions_Visible is a Boolean-valued aspect which may be specified for a
   noninstance subprogram or a generic subprogram.
   If directly specified, the aspect_definition shall be a static
   [Boolean] expression. The aspect is inherited by an inherited primitive
   subprogram. If the aspect is neither inherited nor directly specified
   for a subprogram, then the aspect is False, except in the case of the
   predefined equality operator of a type extension. In that case, the
   aspect value is that of the primitive [(possibly user-defined)] equality
   operator for the parent type.

.. container:: heading

   Legality Rules

2. If the Extensions_Visible aspect is False for a subprogram, then
   certain restrictions are imposed on the use of any parameter of the
   subprogram which is of a specific tagged type (or of a private type
   whose full view is a specific tagged type).
   Such a parameter shall not be converted (implicitly or explicitly) to
   a class-wide type. Such a parameter shall not be passed as an actual
   parameter in a call to a subprogram whose Extensions_Visible aspect is
   True. These restrictions also apply to any parenthesized expression,
   qualified expression, or type conversion whose operand is subject to
   these restrictions, to any Old or Loop_Entry
   ``attribute_reference`` whose prefix is subject to these restrictions,
   to any delta aggregate whose expression is subject to these restrictions,
   and to any conditional expression having at least one dependent_expression
   which is subject to these restrictions.
   [A subcomponent of a parameter is not itself a parameter and is therefore
   not subject to these restrictions. A parameter whose type is class-wide
   is not subject to these restrictions. An Old or
   Loop_Entry ``attribute_reference`` does not itself violate these
   restrictions (despite the fact that (in the tagged case) each of these
   attributes yields a result having the same underlying dynamic tag as their
   prefix).]

3. A subprogram whose Extensions_Visible aspect is True shall not override
   an inherited primitive operation of a tagged type whose
   Extensions_Visible aspect is False. [The reverse is allowed.]

4. If a nonnull type extension inherits a
   procedure having both a False Extensions_Visible aspect and one or
   more controlling out-mode parameters, then the inherited procedure
   requires overriding. [This is because the inherited procedure would not
   initialize the noninherited component(s).]

5. The Extensions_Visible aspect shall not be specified for a subprogram
   which has no parameters of either a specific tagged type or a private
   type unless the subprogram is declared in an instance of a generic
   unit and the corresponding subprogram in the generic unit satisfies
   this rule. [Such an aspect specification, if allowed, would be ineffective.]

6. [These rules ensure that the value of the underlying tag (at run time) of
   the actual parameter of a call to a subprogram whose Extensions_Visible
   aspect is False will have no effect on the behavior of that call.
   In particular, if the actual parameter has any additional components
   which are not components of the type of the formal parameter, then these
   components are unreferenced by the execution of the call.]

.. container:: heading

   Verification Rules

7. [|SPARK| typically requires that an actual parameter corresponding
   to an in mode or in out mode formal parameter in a call shall be fully
   initialized before the call; similarly, the callee is typically responsible
   for fully initializing any out-mode formal parameters before returning.
   For details (including interactions with relaxed initialization), see
   the verification rule about full initialization of subprogram inputs
   and outputs (which include parameters) in :ref:`Subprogram Declarations`
   and then :ref:`Relaxed Initialization`].

8. In the case of a formal parameter of a specific tagged type T (or of a
   private type whose full view is a specific tagged type), the set of
   components which shall be initialized in order to meet these requirements
   depends on the Extensions_Visible aspect of the callee.
   If the aspect is False, then that set of components is the
   [statically known] set of nondiscriminant components of T.
   If the aspect is True, then this set is the set of nondiscriminant
   components of the specific type associated with the tag of the
   corresponding actual parameter. [In general, this is not statically known.
   This set will always include the nondiscriminant components of T, but
   it may also include additional components.]

9. [To put it another way, if the applicable Extensions_Visible aspect
   is True, then the initialization requirements (for both the caller and
   the callee) for a parameter of a specific tagged type T are the same as
   if the formal parameter's type were T'Class. If the aspect is False,
   then components declared in proper descendants of T need not be initialized.
   In the case of an out mode parameter, such initialization by the callee
   is not only not required, it is effectively forbidden because
   such an out-mode parameter could not be fully initialized
   without some form of dispatching (e.g., a class-wide assignment or a
   dispatching call in which an out-mode parameter is a controlling operand).
   Such a dispatching assignment will always fully initialize its controlling
   out-mode parameters, regardless of the Extensions_Visible aspect
   of the callee. An assignment statement whose target is of a class-wide
   type T'Class is treated, for purposes of formal verification, like a call
   to a procedure with two parameters of type T'Class, one of mode out and
   one of mode in.]

10. [In the case of an actual parameter of a call to a subprogram whose
    Extensions_Visible aspect is False where the corresponding formal parameter
    is of a specific tagged type T, these rules imply that formal verification
    can safely assume that any components of the actual parameter which are not
    components of T will be neither read nor written by the call.]

.. index:: Subprogram_Variant
           termination; of subprogram

Subprogram_Variant Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~

The aspect Subprogram_Variant may be specified for subprograms; it can be
used to ensure termination of recursive subprograms in a way that is
similar to how pragma Loop_Variant can be used to ensure termination of loops.

.. container:: heading

   Syntax

::

  subprogram_variant_list ::= structural_subprogram_variant_item | numeric_subprogram_variant_items
  numeric_subprogram_variant_items ::= numeric_subprogram_variant_item {, numeric_subprogram_variant_item}
  numeric_subprogram_variant_item ::= change_direction => expression
  structural_subprogram_variant_item ::= Structural => expression
  change_direction        ::= Increases | Decreases

The aspect_definition for a Subprogram_Variant aspect_specification
shall be a subprogram_variant_list. The Subprogram_Variant aspect
of an inherited subprogram for a derived type is always unspecified.

Two Subprogram_Variant aspects are said to be `compatible` if either both are
structural subprogram variants or both are numeric subprogram variants, the
lengths of the two ``numeric_subprogram_variant_items`` are equal, and
corresponding pairs of the elements of the two lists agree with respect to both
``change_direction`` and the type of their respective ``expressions``. An
unspecified Subprogram_Variant aspect is compatible with, and only with, another
unspecified Subprogram_Variant aspect (including itself).

.. index:: recursive subprograms

Two subprograms are said to be `statically mutually recursive`, if they are
mutually recursive taking into account only direct calls (that is,
ignoring dispatching calls and calls through access-to-subprogram values).
For example, if subprogram Aa calls Bb (that is, Aa
statically contains a direct call to Bb), Bb calls Cc, Cc calls Dd, and
Dd calls Aa, then any 2 of those 4 subprograms (e.g., Bb and Dd) are
statically mutually recursive. The case of a direct recursive call is just
a special case of a statically mutually recursive call; thus, it
is possible [and not unusual] for a subprogram to be statically mutually
recursive with itself and with no other subprogram.

In some cases (described in more detail below) involving a call where the
calling subprogram and the called subprogram have compatible (specified)
Subprogram_Variant aspects, a runtime check (or a verification condition
corresponding to such a runtime check) may be be introduced to ensure that
the "variant of the call progresses". For numeric subprogram variants, this
means that the values of the caller's ``expressions`` (which were saved upon
entry to the caller, as will be described below) are compared in textual
order with those of the callee (which are evaluated only as needed as part of
the check) until either a pair of unequal values is encountered or until
all pairs have been compared.
In either case, a check is performed that the last pair of values to be
compared satisfies the following condition: if the ``change_direction`` for
the associated ``subprogram_variant_item`` is Increases (respectively,
Decreases) then the expression value obtained for the call is greater
(respectively, less) than the value that was saved upon entry to the caller.

.. container:: heading

   Static Semantics

1. [Aspect Subprogram_Variant can be used to demonstrate that execution of
   any of a set of statically mutually recursive subprogram(s)
   will not result in unbounded recursion. This is accomplished by specifying
   expressions that will increase or decrease at each (mutually) recursive
   call.]

2. Subprogram_Variant is an assertion aspect [and may be used in an
   Assertion_Policy pragma]. Subprogram_Variant is an assertion (as
   defined in Ada RM 11.4.2(1.1/3)); any Subprogram_Variant runtime checking
   associated with a call (see below) is governed by
   the Subprogram_Variant assertion policy that is in effect at the
   point of the call.

.. container:: heading

   Legality Rules

3. A Subprogram_Variant aspect may be specified for the same subprograms
   that a Pre aspect may be specified for. [This implies, for example,
   that the Subprogram_Variant aspect cannot be specified for an abstract
   subprogram.]

4. The expression of a ``numeric_subprogram_variant_item`` shall be either
   of a discrete type,
   of a subtype of ``Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer``,
   of a subtype of ``Ada.Numerics.Big_Numbers.Big_Integers_Ghost.Big_Integer``
   or
   of a subtype of ``SPARK.Big_Numbers.Big_Integer``.
   In the second and third cases the associated ``change_direction`` shall be
   Decreases.

5. The expression of a ``structural_subprogram_variant_item`` shall denote a
   formal parameter of the subprogram.

6. The Subprogram_Variant assertion policy in effect at the
   point of a direct recursive call (i.e., a call where the calling
   subprogram is the same as the callee) and at the point where the
   subprogram is declared shall agree.

7. For purposes of the rules given in this section (including static semantics,
   dynamic semantics, legality rules, and verification rules), a call to
   an inherited subprogram associated with a derived type is treated as
   if the call were replaced with the equivalent call to the corresponding
   primitive subprogram of the parent or progenitor type described in
   the "Dynamic Semantics" section of Ada RM 3.4. This notional transformation
   is applied repeatedly in the case of multiple levels of subprogram
   inheritance.

.. container:: heading

   Dynamic Semantics

8. At the beginning of a subprogram with a specified numeric Subprogram_Variant
   aspect,
   the ``expressions`` are evaluated in textual order and their
   values are each saved in a constant that is implicitly declared at
   the beginning of the subprogram body[, in the same way as for
   an unconditionally evaluated Old attribute reference (see Ada RM 6.1.1)].
   For every expression whose type is a subtype of
   ``Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer``, a check is
   performed that it is non-negative.

9. For a direct recursive call (i.e., the calling subprogram is the same
   as the callee), if the subprogram variant is numeric,
   for every expression in the variant of the call whose type
   is a subtype of ``Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer``, a
   check is performed that it is non-negative. Then, a check is made that
   the variant of the call progresses (as described above).
   If the check fails, Assertion_Error is raised.
   [No runtime check is performed in the case of a direct call from one
   subprogram to a different subprogram, even if the two subprograms are
   statically mutually recursive. No runtime check is performed for a
   dispatching call or a call through an access-to-subprogram value.]
   No runtime check is performed if the Subprogram_Variant assertion policy
   in effect at the point of the call is not Check.

.. container:: heading

   Verification Rules

10. Statically mutually recursive subprograms shall have compatible variants.

11. A statically mutually recursive call (that is, a direct call where the
    caller and the callee are statically mutually recursive) where the
    Subprogram_Variant aspects of the two subprograms are specified shall not
    occur with a precondition expression, within a subtype predicate
    expression, within a type invariant expression, within a
    Default_Initial_Condition expression, within a discrete_expression
    of a Subprogram_Variant aspect specification, or as part of the
    default initialization of a type. Such a call shall also not occur
    inside the elaboration of a package unless the package is located
    within a subprogram and not within a declare block.

12. For a statically mutually recursive call to a subprogram whose numeric
    Subprogram_Variant aspect is specified, a verification condition
    is introduced to ensure that the evaluation of the
    ``expressions`` of the ``subprogram_variant_list`` of the
    callee does not a raise any exception.
    Then, for every expression in the variant of the called subprogram whose
    type is a subtype of ``Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer``,
    a check is performed that it is non-negative.
    Finally, a verification condition is generated to ensure that the
    variant of the call progresses.
    This verification condition is already
    implicitly generated in the case where the caller and the callee are the
    same (a direct recursive call) as a consequence of the runtime check taking
    place in that case. It is also generated in the case of other mutually
    recursive calls, although no checks are introduced at runtime due to
    compiler implementation constraints.

13. For a statically mutually recursive call to a subprogram whose structural
    Subprogram_Variant aspect is specified, a verification condition is
    generated to ensure that the actual parameter corresponding to the
    formal parameter denoted by the ``expression`` is a path rooted either
    at the formal parameter of the enclosing subprogram denoted by the
    expression of its Subprogram_Variant aspect or at a local object
    of an anonymous access-to-object type ultimately borrowing or observing a
    part of this formal parameter, that this path corresponds to a strict
    subcomponent of the structure denoted by the formal parameter of the
    enclosing subprogram, and that no deep parts of this structure are
    updated before the call. [This ensures that the rule is sufficient to
    prove recursion termination on acyclic data structures.]

Exceptional Cases
~~~~~~~~~~~~~~~~~

The aspect Exceptional_Cases may be specified for procedures and functions with
side effects; it can be used to list exceptions that might be propagated by the
subprogram with side effects in the context of its precondition, and associate
them with a specific postcondition. The Exceptional_Cases aspect is specified
with an aspect_specification where the ``aspect_mark`` is Exceptional_Cases and
the ``aspect_definition`` must follow the grammar of ``exceptional_case_list``
given below.

.. container:: heading

   Syntax

::

 exceptional_case_list ::= ( exceptional_case   {,  exceptional_case  })
 exceptional_case      ::= exception_choice {'|' exception_choice} => consequence

where ``consequence`` is a boolean expression.

.. container:: heading

   Name Resolution Rules

The boolean expression in the consequences should be resolved as regular
postconditions. In particular, references to the Old attribute are allowed to
occur in them.

.. container:: heading

   Static Semantics

An Exceptional_Cases aspect is an assertion (as defined in RM 11.4.2(1.1/3));
its assertion expressions are the consequences of its exceptional cases.

All prefixes of references to the Old attribute in exceptional cases are
expected to be evaluated at the beginning of the call regardless of whether or
not the particular exception is raised. This allows to introduce constants for
these prefixes at the beginning of the subprogram together with the ones
introduced for the regular postcondition.

.. container:: heading

   Dynamic Semantics

Exceptional_Cases aspects are ignored for execution.

.. container:: heading

   Legality Rules

1. Parameters of modes *out* or *in out* of the subprogram which are neither
   of a *by-reference* type nor marked as aliased shall only occur in
   the consequences of an exceptional case:

   * directly or indirectly in the prefix of a reference to the Old
     attribute, or
   * directly as a prefix of the Constrained, First, Last, Length, or Range
     attributes.

   References to attribute Result shall not occur in the consequences of an
   exceptional case.

.. container:: heading

   Verification Rules

2. If an exception raised in a subprogram annotated with Exceptional_Cases
   is not handled and causes the subprogram body to complete, then a verification
   condition is introduced to make sure that the consequence associated to
   the exceptional case covering the exception evaluates to True. [Because of
   the verification conditions introduced when raising unexpected exceptions,
   there is always an exceptional case covering the propagated exception.]

Program_Exit Aspects
~~~~~~~~~~~~~~~~~~~~

The aspect Program_Exit may be specified for subprograms with
side effects; it can be used to indicate that a subprogram might exit the whole
program, and provide a specific postcondition. The Program_Exit aspect is
specified with an aspect_specification where the aspect_mark is Program_Exit and
the optional aspect_definition is a boolean expression. A Program_Exit aspect
with no aspect_definition is equivalent to a Program_Exit aspect with an
aspect_definition of True.

.. container:: heading

   Name Resolution Rules

The boolean expression in the aspect_definition should be resolved as a
postcondition. In particular, references to the Old attribute are allowed to
occur in it.

.. container:: heading

   Static Semantics

A Program_Exit aspect is an assertion (as defined in RM 11.4.2(1.1/3)); its
assertion expression is its boolean expression.

1. If an output of a subprogram with side effects is mentioned in the boolean
   expression of its aspect Program_Exit, then it shall either occur inside
   the prefix of a reference to the Old attribute or be a stand-alone object.

.. container:: heading

   Dynamic Semantics

Program_Exit aspects are ignored for execution.

.. container:: heading

   Legality Rules

2. The Program_Exit aspect may only be specified for the initial
   declaration of a subprogram with side effects (which may be a declaration, a
   body or a body stub).

.. container:: heading

   Verification Rules

3. A verification condition is introduced on calls to subprograms annotated with
   the Program_Exit aspect. For calls occuring directly inside subprograms also
   annotated with the Program_Exit aspect, it ensures that the boolean
   expression of the Program_Exit aspect of the caller evaluates to True if the
   callee exits the whole program. For other calls, it
   ensures that the callee does not exit the whole program.

Exit Cases
~~~~~~~~~~

The aspect Exit_Cases may be specified for procedures and functions with side
effects; it can be used to partition the input state into a list of cases and
specify, for each case, how the subprogram is allowed to terminate (i.e. return
normally, propagate an exception, or exit the whole program).
The Exit_Cases aspect is specified with an
``aspect_specification`` where the ``aspect_mark`` is Exit_Cases and the
``aspect_definition`` must follow the grammar of ``exit_case_list`` given
below.

.. container:: heading

   Syntax

::

  EXIT_CASE_LIST ::= EXIT_CASE {, EXIT_CASE}
  EXIT_CASE      ::= GUARD => EXIT_KIND
  EXIT_KIND      ::= Normal_Return
                   | Exception_Raised
                   | (Exception_Raised => exception_name)
                   | Program_Exit
  GUARD          ::= Boolean_expression | OTHERS

.. container:: heading

   Name Resolution Rules

The boolean expressions in the guards should be resolved as regular
preconditions.

.. container:: heading

   Static Semantics

An Exit_Cases aspect is an assertion (as defined in RM 11.4.2(1.1/3)); its
assertion expressions are the guards of its exit cases.

.. container:: heading

   Dynamic Semantics

Exit_Cases aspects are ignored for execution.

.. container:: heading

   Legality Rules

1. A guard **others**, if present, shall appear in the last exit case.

2. If all the exit cases of the Exit_Cases aspect of a subprogram are associated
   with Normal_Return, then the subprogram shall have either an
   Exceptional_Cases contract that does not contain only consequences which
   are known to be False at compile time or a Program_Exit contract whose
   postcondition is not known to be False at compile time.
   [A subprogram annotated with Exit_Cases shall be allowed to either
   propagate an exception or exit the program.]

3. All exceptions mentioned in the Exit_Cases aspect of a subprogram shall be
   allowed by the Exceptional_Cases contract of the subprogram, if any.

4. If the Exit_Cases aspect has at least one exit case associated with
   Program_Exit, then the Program_Exit contract for the subprogram, if any,
   shall not have a postcondition which is known to be False at compile time.

.. container:: heading

   Verification Rules

5. If a subprogram is annotated with Exit_Cases and there are at least two
   exit cases whose guards are not the **others** choice, then a verification
   condition is introduced to make sure that all the non-**others** guards are
   disjoint in the context of the precondition.

6. If a subprogram annotated with Exit_Cases returns normally, then a
   verification condition is introduced to make sure that the exit kind of the
   exit case whose guard evaluates to True is Normal_Return, if there is one.

7. If an exception raised in a subprogram annotated with Exit_Cases is not
   handled and causes the subprogram body to complete, then a verification
   condition is introduced to make sure that the exit kind of the exit case
   whose guard evaluates to True, if there is one, is either Exception_Raised or
   (Exception_Raised => E), where E is resolved to the exception that is
   propagated.

8. If a subprogram annotated with Exit_Cases exits the whole program, then a
   verification condition is introduced to make sure that the exit kind of the
   exit case whose guard evaluates to True is Program_Exit, if there is one.

Always_Terminates Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~

The aspect Always_Terminates may be specified for subprograms with
side effects; it can be used to provide a condition under which the subprogram
shall necessarily complete (either return normally, raise an exception, or
exit the whole program). This
aspect may also be specified on packages to provide a default for all
subprograms with side effects declared in the package or in one of its nested
packages. The Always_Terminates aspect is specified with an
aspect_specification where the aspect_mark is Always_Terminates and the
optional aspect_definition is a boolean expression. An Always_Terminates aspect
with no aspect_definition is equivalent to an Always_Terminates aspect with an
aspect_definition of True. [The execution of a SPARK subprogram which does not
complete necessarily runs forever. Other behaviors cannot be modeled in SPARK.]

.. container:: heading

   Name Resolution Rules

The boolean expression in the aspect_definition should be resolved as a
precondition.

.. container:: heading

   Static Semantics

An Always_Terminates aspect is an assertion (as defined in RM 11.4.2(1.1/3));
its assertion expression is its boolean expression.

1. If the aspect Always_Terminates is specified for a package, it shall not have
   an aspect definition.

2. If the aspect Always_Terminates for a package specification or a subprogram
   with side effects P is not otherwise specified and P is declared directly
   inside a package (explicitly or implicitly) annotated with an aspect
   Always_Terminates then an Always_Terminates aspect of True is implicitly
   specified for P.


.. container:: heading

   Dynamic Semantics

Always_Terminates aspects are ignored for execution.

.. container:: heading

   Legality Rules

3. The Always_Terminates aspect may only be specified for the initial
   declaration of a subprogram with side effects (which may be a declaration, a
   body or a body stub), or of a package specification.

.. container:: heading

   Verification Rules

4. A verification condition is introduced on loops and calls occuring inside
   functions without side effects or package elaborations to make sure that
   they necessarily complete.

5. A verification condition is introduced on loops and calls occuring inside
   subprograms with side effects annotated with an Always_Terminates aspect to
   make sure that they necessarily complete in cases where the boolean
   condition mentioned in the Always_Terminates aspect evaluates to True on
   entry of the subprogram with side effects.


Functions With Side Effects
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The aspect Side_Effects may be specified for functions; it can be used to
indicate that a function should be handled like a procedure with respect to
parameter modes, Global contract, exceptional contract and termination: it may
have output parameters, write global variables, raise exceptions and not
terminate. Such a function is called a *function with side effects*.

Note that a function with side effects is also a volatile function (see section
:ref:`External State`).

.. container:: heading

   Static Semantics

1. Side_Effects is a Boolean-valued aspect which may be specified for a
   noninstance function or a generic function. If directly specified, the
   aspect_definition shall be a static [Boolean] expression. The aspect is
   inherited by an inherited primitive function. If the aspect is neither
   inherited nor directly specified for a function, then the aspect is False.

.. container:: heading

   Legality Rules

2. [Redundant: The declaration of a function with side effects may have a
   ``parameter_specification`` with a mode of **out** or **in out**. This rule
   also applies to a ``subprogram_body`` for a function with side effects for
   which no explicit declaration is given.]

3. [Redundant: A function with side effects may have a ``mode_selector`` of
   Output or In_Out in its Global aspect.]

4. A call to a function with side effects may only occur as the [right-hand
   side] expression of an assignment statement or of a local object declaration
   witout a block. [Redundant: In particular,
   functions with side effects cannot be called inside assertions.]

5. A function with side effects shall not have a Pure_Function aspect or
   pragma.

6. A function with side effects shall not be an expression function.

7. A function with side effects shall not be a traversal function (see section
   :ref:`Access Types`).

8. A user-defined primitive equality operation on a record type shall not be a
   function with side effects, unless the record type has only limited views
   (see :ref:`Overloading of Operators`).

   [This avoids the case where such a record type is a component of another
   composite type, whose predefined equality operation now has side effects
   through the primitive equality operation on its component.]


Formal Parameter Modes
----------------------

In flow analysis, particularly information flow analysis, the update
of a component of composite object is treated as updating the whole of
the composite object with the component set to its new value and the
remaining components of the composite object with their value preserved.

This means that if a formal parameter of a subprogram is a composite
type and only individual components, but not all, are updated, then
the mode of the formal parameter should be **in out**.

In general, it is not possible to statically determine whether all
elements of an array have been updated by a subprogram if individual
array elements are updated. The mode of a formal parameter of an
array with such updates should be **in out**.

.. todo: Consider providing a way of proving that all elements of
         an array have been updated individually and providing a means to
         specify that a composite object is updated but not read by a
         subprogram.

A formal parameter with a mode of **out** is treated as not having an
entry value (apart from any discriminant or attributes of properties
of the formal parameter). Hence, a subprogram cannot read a value of
a formal parameter of mode **out** until the subprogram has updated
it.

.. container:: heading

   Verification Rules


1. A subprogram formal parameter of a composite type which is updated
   but not fully initialized by the subprogram shall have a mode of
   **in out**, unless it has relaxed initialization
   (see section :ref:`Relaxed Initialization`).


2. A subprogram formal parameter of mode **out** shall not be read by
   the subprogram until it has been updated by the subprogram.  The
   use of a discriminant or an attribute related to a property, not
   its value, of the formal parameter is not considered to be a read
   of the formal parameter. [Examples of attributes that may be used
   are A'First, A'Last and A'Length; examples of attributes that are
   dependent on the value of the formal parameter and shall not be
   used are X'Old and X'Loop_Entry.]


Subprogram Bodies
-----------------


Conformance Rules
~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Inline Expansion of Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Subprogram Calls
----------------

No extensions or restrictions.


Parameter Associations
~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


.. index:: aliasing

Anti-Aliasing
~~~~~~~~~~~~~

An alias is a name which refers to the same object as another name.
The presence of aliasing is inconsistent with the underlying flow
analysis and proof models used by the tools which assume that
different names represent different entities.  In general, it is not
possible or is difficult to deduce that two names refer to the same
object and problems arise when one of the names is used to update the
object (although object renaming declarations are not problematic in
|SPARK|).

A common place for aliasing to be introduced is through the actual parameters
and between actual parameters and global variables in a call to a subprogram
with side effects. Extra verification rules are given that avoid the
possibility of problematic aliasing through actual parameters and global
variables.  Except for functions with side effects (see :ref:`Functions With
Side Effects`), a function is not allowed to have side effects and cannot
update an actual parameter or global variable.  Therefore, such function calls
cannot introduce problematic aliasing and are excluded from the anti-aliasing
rules given below for calls to subprograms with side effects.

.. container:: heading

   Static Semantics

.. index:: interfering object

1. An object is said to be *interfering* if it is unsynchronized (see section
   :ref:`Tasks and Synchronization`) or it is synchronized only due to being
   *constant after elaboration* (see section :ref:`Object Declarations`).

   Two names that potentially overlap (see section :ref:`Access Types`)
   and which each denotes an interfering object are said to
   *potentially introduce aliasing via parameter passing*.
   [This definition has the effect of exempting most synchronized objects
   from the anti-aliasing rules given below; aliasing of most synchronized
   objects via parameter passing is allowed.]

.. index:: immutable parameter

2. A formal parameter is said to be *immutable* if it is of mode **in** and
   neither of an access-to-variable type nor of an anonymous access-to-constant
   type. [Note that access parameters are of mode **in** too.]

   Otherwise, the formal parameter is said to be *mutable*.

.. container:: heading

   Verification Rules


3. A call to a subprogram with side effects shall only pass two actual
   parameters which potentially introduce aliasing via parameter passing when
   either

   * both of the corresponding formal parameters are either

     * immutable; or
     * of mode **in** and of an anonymous access-to-constant type; or

   * at least one of the corresponding formal parameters is immutable and is of
     a by-copy type. [Note that this includes parameters of named
     access-to-constant and (named or anonymous) access-to-subprograms
     types. Ownership rules prevent other problematic aliasing, see section
     :ref:`Access Types`.]


4. If an actual parameter in a call to a subprogram with side effects and a
   ``global_item`` referenced by the called subprogram potentially introduce
   aliasing via parameter passing, then

   * the corresponding formal parameter shall be either

     * immutable; or
     * of mode **in** and of an anonymous access-to-constant type; and

   * if the ``global_item``'s mode is Output or In_Out, then the
     corresponding formal parameter shall be immutable and of
     a by-copy type.


5. A call to a function with side effects shall only pass an actual parameter
   which potentially introduces aliasing via parameter passing with an object
   referenced from the [left-hand side] name of the enclosing assignment
   statement, when the corresponding formal parameter is either

   * immutable; or
   * of mode **in** and of an anonymous access-to-constant type.

   [The rationale for this rule is that, otherwise, the result of the
   evaluation of the assignment statement would depend on the order of
   evaluation chosen by the compiler, as the object assigned to might depend on
   this choice.]

6. A call to a function with side effects shall not reference a ``global_item``
   of mode Output or In_Out which potentially introduces aliasing via parameter
   passing with an object referenced from the [left-hand side] name of the
   enclosing assignment statement.

   [The rationale for this rule is the same as for the previous rule.]

7. A call to a function with side effects shall not reference the symbol ``@``
   to refer to the target name of the assignment.

   [The rationale for this rule is the same as for the previous rule.]

8. Where one of these rules prohibits the occurrence of an object V or any of
   its subcomponents as an actual parameter, the following constructs are also
   prohibited in this context:

   * A type conversion whose operand is a prohibited construct;

   * A call to an instance of Unchecked_Conversion whose operand is a prohibited construct;

   * A qualified expression whose operand is a prohibited construct;

   * A prohibited construct enclosed in parentheses.


.. container:: heading

   Examples

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/anti_aliasing.adb
   :language: ada
   :linenos:


Exception Propagation
~~~~~~~~~~~~~~~~~~~~~

.. container:: heading

   Verification Rules

1. A call to a procedure annotated with an aspect Exceptional_Cases
   (see :ref:`Exceptional Cases`) introduces
   an obligation to prove that potentially raised exceptions are expected as
   defined in :ref:`Raise Statements and Raise Expressions`.

Return Statements
-----------------

No extensions or restrictions.


Overloading of Operators
------------------------

.. container:: heading

   Legality Rules


1. [A user-defined primitive equality operation on a record type shall have a
   Global aspect of ``null``, unless the record type has only limited views;
   see :ref:`Global Aspects` for the statement of this rule.]

2. [A user-defined primitive equality operation on a record type shall not be a
   volatile function, unless the record type has only limited views; see
   :ref:`External State - Variables and Types` for the statement of this rule.]

3. [A user-defined primitive equality operation on a record type shall not be a
   function with side effects, unless the record type has only limited views;
   see :ref:`Functions With Side Effects` for the statement of this rule.]

4. [A user-defined primitive equality operation on a non-ghost record type
    shall not be ghost, unless the record type has only limited views; see
    :ref:`Ghost Entities` for the statement of this rule.]


Null Procedures
---------------

No extensions or restrictions.


.. index:: expression function

Expression Functions
--------------------

.. container:: heading

   Legality Rules


1. Contract_Cases, Global and Depends aspects may be applied to an
   expression function as for any other function declaration if it
   does not have a separate declaration.  If it has a separate
   declaration then the aspects are applied to that.  It may have
   refined aspects applied (see :ref:`State Refinement`).


.. index:: ghost code
           see: Ghost; ghost code

Ghost Entities
--------------

Ghost entities are intended for use in discharging verification conditions and
in making it easier to express assertions about a program. The essential
property of ghost entities is that they have no effect on the dynamic behavior
of a valid SPARK program. More specifically, if one were to take a valid SPARK
program and remove all ghost entity declarations from it (considering the
association of a ghost formal parameter in a generic instantiation as a
declaration) and all "innermost" statements, declarations, and pragmas which
refer to those declarations (replacing removed statements with null statements
when syntactically required), then the resulting program might no longer be a
valid SPARK program (e.g., it might no longer be possible to discharge all of
the program's verification conditions) but its dynamic semantics (when viewed
as an Ada program) should be unaffected by this transformation. [This
transformation might affect the performance characteristics of the program
(e.g., due to no longer evaluating provably true assertions), but that is not
what we are talking about here. In rare cases, it might be necessary to make a
small additional change after the removals (e.g., adding an Elaborate_Body
pragma) in order to avoid producing a library package that no longer needs a
body (see Ada RM 7.2(4))].

.. container:: heading

   Static Semantics


1. |SPARK| defines the representation aspect Ghost. It can be associated with
   either a boolean value or an assertion level
   (see :ref:`Pragma Assertion_Level`).
   Ghost is an aspect of all entities (e.g., subprograms, types, objects).
   An entity whose Ghost aspect is either True or an assertion level is said to
   be a ghost entity; terms such as "ghost function" or "ghost variable" are
   defined analogously (e.g., a function whose Ghost aspect is either True or
   an assertion level is said to be a ghost function).
   In addition, a subcomponent of a ghost object is a ghost object.

   Ghost is an assertion aspect.
   [This means that Ghost can be named in an Assertion_Policy pragma.]

   [The assertion policy applicable to the declaration of a
   Ghost entity may be associated either with an assertion level, if the
   entity has an associated assertion level, or with the Ghost assertion kind
   otherwise.]


2. Unless explicitly provided, the Ghost aspect of an entity declared inside of
   a ghost entity (e.g., within the body of a ghost subprogram) is defined to be
   the Ghost aspect of its enclosing entity.
   The Ghost aspect of an entity implicitly declared as part of the
   explicit declaration of a ghost entity (e.g., an implicitly declared
   subprogram associated with the declaration of a ghost type) is defined
   to be the Ghost aspect of the declared object.
   Unless explicitly provided, the Ghost aspect of a child
   of a ghost library unit is defined to be Ghost aspect of the library unit.


3. An object declaration which occurs inside an expression in a ghost
   declaration, statement, assertion pragma or specification aspect declaration
   is a ghost declaration.

   If this declaration does not have the Ghost aspect specified, the assertion
   policy applicable to this declaration comes from the policy applicable to the
   enclosing declaration, statement, assertion pragma or specification aspect.

   Otherwise, the assertion policy applicable to an object declaration comes
   either from its assertion level if any, or from the ghost policy at the point
   of declaration.


4. A statement or pragma is said to be a "ghost statement" if

   * it occurs within a ghost subprogram or package; or

   * it is a call to a ghost procedure; or

   * it is an assignment statement whose target is a ghost variable; or

   * it is a pragma which specifies an aspect of a ghost entity; or

   * it is an assertion pragma which encloses a name denoting a ghost entity.

   The assertion policy applicable to an assignment statement whose target
   is a ghost variable is the assertion policy applicable to the ghost variable
   at the point of assignment.

   The assertion policy applicable to a call to a
   ghost procedure is the assertion policy applicable to the ghost procedure
   at the point of call.

   The assertion policy applicable to assertion pragmas
   and specification aspects occurring inside a ghost entity or that apply to a
   ghost entity whose applicable assertion policy is Ignore is Ignore.

   Otherwise, the assertion policy applicable to
   an assertion pragma or specification aspect may come either from its
   assertion level if any, or from an assertion kind (e.g., Pre for a
   precondition expression, Assert for the argument of an Assert pragma...).

   The applicable assertion policy for other ghost statements is the assertion
   policy applicable to the enclosing ghost subprogram or package.


5. If the assertion policy applicable to a ghost statement or the declaration of
   a ghost entity is Ignore, then the
   elaboration of that construct (at run time) has no effect,
   other Ada or |SPARK| rules notwithstanding. Similarly, the elaboration
   of the completion of a ghost entity has no effect if the assertion policy
   applicable to the entity's initial declaration is Ignore.
   [Assertion policy Ignore can be used to ensure that
   a compiler generates no code for ghost constructs.]
   Such a declaration is said to be a *disabled ghost declaration*;
   terms such as "disabled ghost type" and "disabled ghost subprogram"
   are defined analogously.

6. A ghost entity A is said to be *assertion-level-dependent* on a
   ghost entity B if either:

   * A or B does not have an associated assertion level or

   * both A and B have an associated assertion level and either:

     * the associated assertion level of A depends on the associated assertion
       level of B or

     * the associated assertion level of A cannot be enabled. [It is Static or
       depends on Static.]

   In the same way, an assertion expression or specification aspect is said to
   be *assertion-level-dependent* on a ghost entity if either:

   * the ghost entity or the assertion or aspect does not have an associated
     assertion level or

   * both the ghost entity and the assertion or aspect have an associated
     assertion level and either:

     * the assertion level of the assertion or aspect depends on the assertion
       level of the ghost entity or

     * the assertion level of the assertion cannot be enabled.

   [The following rules enforce that a reference to a ghost entity always occurs
   in a context that is assertion-level-dependent on it. This ensures
   that disabling or enabling an assertion
   level won't cause the program to stop compiling. Ghost entities and
   assertions without a level are exempted from this check so as not to force
   the use of assertion levels in user code.]

   Two ghost entities A and B are said to have a *matching assertion level* if
   A is assertion-level-dependent on B and B is assertion-level-dependent on A.


.. container:: heading

   Legality Rules


7. The Ghost aspect may only be specified [explicitly] for
   the declaration of a subprogram, a
   generic subprogram, a type (including a partial view thereof),
   an object (or list of objects, in the case of an ``aspect_specification``
   for an ``object_declaration`` having more than one ``defining_identifier``),
   a package, a generic package, or a generic formal parameter.
   The Ghost aspect may be specified via either an ``aspect_specification``
   or via a pragma. The representation pragma Ghost takes the same argument
   as the Ghost aspect.
   [In particular, |SPARK| does not currently include any form of
   ghost components of non-ghost record types, or ghost parameters of non-ghost
   subprograms. |SPARK| does define
   ghost state abstractions, but these are described elsewhere.]


8. A Ghost aspect value of False shall not be explicitly specified
   except in a confirming aspect specification. [For example, a
   non-ghost declaration cannot occur within a ghost subprogram.]

   The value specified for the Ghost assertion policy in an
   Assertion_Policy pragma shall be either Check or Ignore.
   [In other words, implementation-defined assertion policy values
   are not permitted.] The Ghost assertion policy in effect at any
   point of a SPARK program shall be either Check or Ignore.


9. A ghost type or object shall not be effectively volatile.
   A ghost object shall not be imported or exported.
   [In other words, no ghost objects for which reading or writing
   would constitute an external effect (see Ada RM 1.1.3).]


10. A ghost primitive subprogram of a non-ghost type extension shall
    not override an inherited non-ghost primitive subprogram.
    A non-ghost primitive subprogram of a type extension shall
    not override an inherited ghost primitive subprogram.
    In addition, a ghost primitive subprogram of a type extension that
    overrides an inherited ghost primitive subprogram shall have the same
    Ghost aspect value as the overridden subprogram unless the ghost type
    extension is assertion-level-dependent on the overridden subprogram. In this
    case, the overriding subprogram shall have the same Ghost aspect value as
    the type extension.
    [A ghost subprogram may be a primitive subprogram of a non-ghost tagged
    type.
    A ghost type extension may have a non-ghost parent type or progenitor;
    primitive subprograms of such a type may override inherited (ghost or
    non-ghost) subprograms.]


11. A Ghost pragma which applies to a declaration occuring in the visible part
    of a package shall not occur in the private part of that package.
    [This rule is to ensure that the ghostliness of a visible entity can be
    determined without having to look into the private part of the enclosing
    package.]

12. If ghost entity is declared inside another ghost entity or as the child of
    another ghost entity, then it shall be assertion-level-dependent
    on its enclosing or parent ghost entity unless the declared entity is a
    generic instance or a renaming declaration.
    [This avoids enabled declarations in disabled scope.]

13. A ghost entity E shall only be referenced:

    * from within an assertion expression that is
      assertion-level-dependent on E; or

    * from within an aspect specification [(i.e., either an
      ``aspect_specification`` or an aspect-specifying pragma)]; or

    * within the declaration or completion of a ghost entity that is
      assertion-level-dependent on E
      (e.g., from within the body of a ghost subprogram); or

    * within a call to a ghost procedure that is assertion-level-dependent on
      E; or

    * within an assignment statement whose target is a ghost variable that is
      assertion-level-dependent on E; or

    * within a ``with_clause`` or ``use_clause``; or

    * within a renaming_declaration which either renames a ghost entity or
      occurs within a ghost subprogram or package; or

    * within an actual parameter in a generic instantiation when the
      corresponding generic formal parameter is ghost.

    A ghost attribute like ``Initialized`` shall only be referenced where a
    ghost entity would be allowed.

14. A ghost entity E shall not be referenced within an aspect specification
    [(including an aspect-specifying pragma)]
    which specifies an aspect of an entity that is either non-ghost or not
    assertion-level-dependent on E except in the following cases:

    * the reference occurs within an assertion expression that is
      assertion-level-dependent on E and is not a predicate expression,
      unless the predicate is introduced by aspect Ghost_Predicate; or

    * the specified aspect is either Global, Depends, Refined_Global,
      Refined_Depends, Initializes, Refined_State, or Iterable.
      [For example, the Global aspect of a non-ghost subprogram might
      refer to a ghost variable.]

   [Predicate expressions are excluded because predicates participate
   in membership tests; no Assertion_Policy pragma has any effect on
   this participation. In the case of a Static_Predicate expression,
   there are also other reasons (e.g., case statements).]


15. An **out** or **in out** mode actual parameter in a call to a ghost
    subprogram shall be a ghost variable. In addition, the variable and the
    subprogram shall have matching assertion levels.


16. In a generic declaration:

    * the default expression (if any) for a ghost generic formal object [both
      of mode **in** and] of access-to-variable type shall be a ghost object
      with a matching assertion level
      [otherwise writing to a reachable part (see :ref:`Access Types`) of the
      ghost formal object would have an effect on a non-ghost variable]; and

    * the default subprogram (if any) for a ghost generic formal procedure
      shall be a ghost procedure with a matching assertion level
      [otherwise a call to the ghost formal
      procedure could have effects on non-ghost variables, if the default
      non-ghost procedure is writing to non-ghost variables].


17. In a generic instantiation:

    * the actual parameter for a ghost generic formal object of mode **in out**
      or both of mode **in** and of access-to-variable type, shall be a ghost
      object with a matching assertion level
      [otherwise writing to a reachable part (see :ref:`Access Types`)
      of the ghost formal object would have an effect on a non-ghost variable];

    * the actual parameter for a ghost generic formal procedure shall be a
      ghost procedure with a matching assertion level
      [otherwise a call to the ghost formal procedure could
      have effects on non-ghost variables, if the actual non-ghost procedure is
      writing to non-ghost variables]; and

    * the actual parameter for a ghost generic formal package shall be a ghost
      package with a matching assertion level
      [otherwise an object or a procedure in the package could lead to
      the problems mentions in the two previous cases].


18. If the assertion policy applicable to the declaration of a Ghost entity is
    Ignore, then the assertion policy applicable to any reference
    to that entity shall be Ignore except if the reference occurs in an
    aspect specification for the aspects Global, Depends, Refined_Global,
    Refined_Depends, Initializes, or Refined_State.
    If the Ghost assertion policy in effect at the point of the declaration
    of a ghost variable is Check, then the assertion policy applicable
    to any assignment to a part of that variable shall be Check.
    Additionally, if an assignment to a part of a ghost variable occurs in a
    ghost entity, then the variable should be assertion-level-dependent on this
    entity.
    [This includes both assignment statements and passing a ghost variable
    as an **out** or **in out** mode actual parameter.]


19. An Assertion_Policy pragma specifying a Ghost policy shall not occur within
    a ghost subprogram or package.
    Similarly, an Assertion_Policy pragma specifying an Assertion_Level policy
    shall not occur within a ghost subprogram or package associated to an
    assertion level which depends on this level.
    If a ghost entity has a completion then the assertion policies applicable to
    the declaration and to the completion of the entity shall
    be the same. [This rule applies to subprograms, packages, types,
    and deferred constants.]

    The assertion policies applicable to the declaration of an entity and to an
    aspect specification which applies to that entity shall be the same.


20. If the assertion policy applicable to the declaration of a Ghost entity
    state abstraction is Ignore, then the assertion policy applicable to the
    declaration of each constituent of that
    abstraction shall be Ignore. In addition, constituents of a ghost state
    abstraction shall be assertion-level-dependent of it.


21. If a tagged type is not a disabled ghost type, and if a
    primitive operation of the tagged type overrides an inherited operation,
    then the corresponding operation of the ancestor type shall be
    a disabled ghost subprogram if and only if the overriding subprogram
    is a disabled ghost subprogram.


22. A ghost type shall not have a task or protected part.
    A ghost object shall not be of a type which yields synchronized objects
    (see section :ref:`Tasks and Synchronization`).
    A ghost object shall not have a volatile part.
    A synchronized state abstraction shall not be a ghost state abstraction
    (see :ref:`Abstract_State Aspects`).


23. A user-defined primitive equality operation on a non-ghost record type
    shall not be ghost, unless the record type has only limited views (see
    :ref:`Overloading of Operators`). In addition, a user-defined primitive
    equality operation on a ghost record type shall have a matching assertion
    level.

    [This avoids the case where such a record type is a component of another
    non-ghost composite type, whose predefined non-ghost equality operation now
    calls a ghost function through the primitive equality operation on its
    component.]


.. container:: heading

   Verification Rules


24. A ghost subprogram with side effects shall not have a non-ghost [global]
    output. In addition, [global] outputs of a ghost subprogram shall be
    assertion-level-dependent on the subprogram. [This ensures that a
    disabled ghost subprogram never modifies an enabled (ghost) state].


25. An output of a non-ghost subprogram other than a state abstraction
    or a ghost global shall not depend on a ghost input. In addition, if a ghost
    output of a subprogram depends on one of its ghost inputs, then the output
    should be assertion-level-dependent on the input.
    [It is intended
    that this follows as a consequence of other rules. Although a
    non-ghost state abstraction output which depends on a ghost input may
    have a non-ghost constituent, other rules prevent such a non-ghost
    constituent from depending on the ghost input.]


26. A global input of a ghost subprogram with side effects shall not be effectively
    volatile for reading.  [This rule says, in effect, that ghost procedural
    subprograms are subject to the same restrictions as non-ghost nonvolatile
    functions with respect to reading volatile objects.]  A name occurring
    within a ghost statement shall not denote an object that is effectively
    volatile for reading. [In other words, a ghost statement is subject to
    effectively the same restrictions as a ghost subprogram with side effects.]


27. If the assertion policy applicable to the declaration of
    a ghost variable or ghost state abstraction is Check, then the
    assertion policy applicable to any call to a procedural
    subprogram for which that variable or state abstraction is a global output
    shall be Check.


.. container:: heading

   Examples

.. code-block:: ada

   function A_Ghost_Expr_Function (Lo, Hi : Natural) return Natural is
     (if Lo > Integer'Last - Hi then Lo else ((Lo + Hi) / 2))
     with Pre  => Lo <= Hi,
          Post => A_Ghost_Expr_Function'Result in Lo .. Hi,
          Ghost;

   function A_Ghost_Function (Lo, Hi : Natural) return Natural
     with Pre  => Lo <= Hi,
          Post => A_Ghost_Function'Result in Lo .. Hi,
          Ghost;
   -- The body of the function is declared elsewhere.

   function A_Nonexecutable_Ghost_Function (Lo, Hi : Natural) return Natural
     with Pre  => Lo <= Hi,
          Post => A_Nonexecutable_Ghost_Function'Result in Lo .. Hi,
          Ghost,
          Import;
   -- The body of the function is not declared elsewhere.

.. index:: Relaxed_Initialization
           Initialized
           initialization; by proof

Relaxed Initialization
----------------------

|SPARK| defines the Boolean-valued aspect Relaxed_Initialization and the related
Boolean-valued ghost attribute, Initialized.

Without the Relaxed_Initialization aspect, the rules that statically prevent
reading an uninitialized scalar object are defined with "whole object"
granularity. For example, all inputs of a subprogram are required
to be fully initialized at the point of a call to the subprogram and all
outputs of a subprogram are required to be fully initialized at the point of a
return from the subprogram. The Relaxed_Initialization aspect, together with
the Initialized attribute, provides a mechanism for safely (i.e., without
introducing the possibility of improperly reading an uninitialized scalar)
referencing partially initialized Inputs and Outputs.

The Relaxed_Initialization aspect may be specified for a type or for a
subprogram or entry, where it effectively applies to one or more of its formal
parameters and the return object of a function.
The prefix of an Initialized attribute reference shall denote an object.

.. container:: heading

   Static Semantics

1. An object is said to *have relaxed initialization* if and only if

   * its Relaxed_Initialization aspect is True; or

   * the Relaxed_Initialization aspect of its type is True; or

   * it is a subcomponent of an object that has relaxed initialization; or

   * it is the return object of a function call and the Relaxed_Initialization
     aspect of the function's result is True; or

   * it is the return object of a call to a predefined concatenation
     operator and at least one of the operands is a name denoting an
     object having relaxed initialization; or

   * it is the result object of an aggregate having a least one component
     whose value is that of an object that has relaxed initialization; or

   * it is the result of evaluating a value conversion whose operand
     has relaxed initialization; or

   * it is the associated object of an expression (e.g., a view conversion,
     a qualified expression, or a conditional expression) which has at least
     one operative constituent (see Ada RM 4.4) which is not the expression
     itself and whose associated object has relaxed initialization.

   A type has relaxed initialization if its
   Relaxed_Initialization aspect is True. An expression has relaxed
   initialization if its evaluation yields an object that has relaxed
   initialization.

2. A Relaxed_Initialization aspect specification for a formal parameter
   of a subprogram or entry or for a function's result is expressed syntactically
   as an aspect_specification of the declaration of the enclosing callable
   entity.  [This is expressed this way because Ada does not
   provide syntax for specifying aspects for subprogram/entry parameters,
   or for the result of a function.] In the following example,
   the parameter X1 and the result of F are specified as having relaxed
   initialization; the parameters X2 and X3 are not:

   .. code-block:: ada

      function F (X1 : T1; X2 : T2; X3 : T3) return T4
        with Relaxed_Initialization => (X1 => True, F'Result);

..

   More precisely, the Relaxed_Initialization aspect for a subprogram
   or entry (or a generic subprogram) is specified by
   an ``aspect_specification`` where the ``aspect_mark`` is
   Relaxed_Initialization and the ``aspect_definition`` has the
   following grammar for ``profile_aspect_spec``:

   ::

      profile_aspect_spec ::= ( profile_spec_item {, profile_spec_item} )
      profile_spec_item   ::= parameter_name [=> aspect_definition]
                            | function_name'Result [=> aspect_definition]

3. Relaxed_Initialization aspect specifications are inherited by
   a derived type (if the aspect is specified for the ancestor type)
   and by an inherited subprogram (if the aspect is specified for the
   corresponding primitive subprogram of the ancestor type).

4. For a prefix *X* that denotes an object which has relaxed initialization,
   the following attribute is defined:

   ::

      X'Initialized

   [It follows as a consequence of the other rules of |SPARK| that if
   X'Initialized is True,
   then for every reachable part Y of X whose type is not
   annotated with the Relaxed_Initialization aspect, Y belongs to its
   subtype.] An Initialized attribute reference is never a static expression.

.. container:: heading

   Legality Rules

5. The following rules apply to the profile_aspect_spec of a
   Relaxed_Initialization aspect specification for a subprogram, a
   generic subprogram, or an entry.

   * Each parameter_name shall name a parameter of the given subprogram or entry
     and no parameter shall be named more than once. It is not
     required that every parameter be named.

   * Each aspect_definition within a profile_aspect_spec shall be as for a
     Boolean aspect.

   * The form of profile_spec_item that includes a Result
     attribute reference shall only be provided if the given subprogram or entry
     is a function or generic function; in that case, the prefix
     of the attribute reference shall denote that function or generic
     function. Such a Result attribute reference is allowed,
     other language restrictions on the use of Result attribute
     references notwithstanding (i.e., despite the fact that such a
     Result attribute reference does not occur within a postcondition
     expression).

   * A parameter or function result named in the aspect_specification shall not
     be of an elementary type. [It is a bounded error to pass an uninitialized
     scalar parameter as input for an input parameter or as output for an
     output parameter or function result, so there is no benefit of marking
     such a parameter or result as having relaxed initialization. An object of
     access type is always initialized.]

   * A Boolean value of True is implicitly specified if no aspect_definition
     is provided, as per Ada RM 13.1.1's rules for Boolean-valued aspects.
     A Boolean value of False is implicitly specified if a given parameter
     (or, in the case of a function or generic function, the result) is not
     mentioned in any profile_spec_item.

6. No part of a tagged type, or of a tagged object, shall have relaxed
   initialization.

7. No part of an effectively volatile type, or of an effectively volatile
   object, shall have relaxed initialization.

8. No part of an Unchecked_Union type shall have relaxed initialization.
   No part of the type of the prefix of an Initialized attribute reference
   shall be of an Unchecked_Union type.

9. A Relaxed_Initialization aspect specification which applies to a
   declaration occuring in the visible part of a package [(e.g., the
   declaration of a private type or of a deferred constant)] shall not
   occur in the private part of that package.

10. A formal parameter of a dispatching operation shall not have relaxed
    initialization; the result of a dispatching function shall not have
    relaxed initialization.

11. [Ghost attribute ``Initialized`` shall only be referenced where a
    ghost entity would be allowed;
    see :ref:`Ghost Entities` for the statement of this rule.]

.. container:: heading

   Verification Rules

12. At the point of a read of an elementary object X that has relaxed
    initialization,
    a verification condition is introduced to ensure that X is initialized.
    This includes the case where X is a subcomponent of a composite object
    that is passed as an argument in a call to a predefined relational
    operator (e.g., "=" or "<"). Such a verification condition is also
    introduced in the case where X is a reachable part
    (see :ref:`Access Types`) of the [source]
    expression of an assignment operation and the target of the assignment
    does not have relaxed initialization, where X is a reachable part of
    an actual parameter in a call where the corresponding formal parameter is
    of mode **in** or **in out** and does not have relaxed initialization,
    upon a call whose precondition implies X'Initialized, and upon return
    from a call whose postcondition implies X'Initialized.

    [For updates to X that do not involve calls, this check that X is
    initialized is implemented via flow analysis and no additional
    annotations are required. Preconditions and postconditions that mention
    X'Initialized may also be used to communicate information about the
    initialization status of X across subprogram boundaries.

    These rules statically prevent any of the bounded-error or erroneous
    execution scenarios associated with reading an uninitialized scalar
    object described in Ada RM 13.9.1. It may provide useful intuition to
    think of a subprogram as having (roughly speaking) an implicit
    precondition of X'Initialized for each of its inputs X that does not have
    relaxed initialization and an implicit postcondition of Y'Initialized for
    each of its outputs Y that does not have relaxed initialization; this
    imprecise description ignores things like volatile objects and state
    abstractions. For a particular call, this notional precondition is also
    in effect for a given formal parameter if the corresponding actual
    parameter does not have relaxed initialization (even if the formal
    parameter does).

    The verification conditions described here are not needed if
    X does not have relaxed initialization because the more conservative
    whole-object-granularity rules that govern that case will ensure that X is
    initialized whenever it is read.]

13. For any object X, evaluation of
    X'Initialized includes the evaluation of any subtype predicate applying
    to X. In addition:

    * if X has a composite type, evaluation of X'Initialized includes the
      evaluation of Y'Initialized for every component Y of X whose type is not
      annotated with the Relaxed_Initialization aspect,

    * if X has unconstrained discriminants, evaluation of X'Initialized
      includes the evaluation of Y'Initialized for every discriminant Y of X,

    * if X has an access-to-object type, evaluation of X'Initialized includes
      the evaluation X.all'Initialized if X is not null and the designated
      type of the type of X is not annotated with the Relaxed_Initialization
      aspect,

    * if X has an elementary type, its value must have been written either
      explicitly or implicitly through default initialization.

   Discriminants of out-mode parameters and Output globals of a subprogram are
   considered to be initialized at the beginning of the subprogram. Other
   reachable parts are not.
