Subprograms
===========

.. _subprogram-declarations:

Subprogram Declarations
-----------------------

We distinguish the *declaration view* introduced by a ``subprogram_declaration``
from the *implementation view* introduced by a ``subprogram_body`` or an
``expression_function_declaration``. For subprograms that are not declared by
a ``subprogram_declaration``, the ``subprogram_body`` or
``expression_function_declaration`` also introduces a declaration view which
may be in |SPARK| even if the implementation view is not.

Rules are imposed in |SPARK| to ensure that the execution of a function
call does not modify any variables declared outside of the function.
It follows as a consequence of these rules that the evaluation
of any |SPARK| expression is side-effect free.

We also introduce the notion of a *global item*, which is a name that denotes a
global object or a state abstraction (see :ref:`abstract-state`). Global items
are presented in Global aspects (see :ref:`global-aspects`).

An *entire object* is an object which is not a subcomponent of a larger
containing object.  More specifically, an *entire object* is
an object declared by an ``object_declaration`` (as opposed to, for example,
a slice or the result object of a function call) or a formal parameter of
a subprogram. In particular, a component of a protected unit is not
an *entire object*.

An object O1 is said to be a *reachable element* of an object O2 if

- O1 is a part of O2; or
- O1 is a reachable element of the object designated by
  (the value of) an access-valued part of O2.

.. centered:: **Static Semantics**

1. The *exit* value of a global item or parameter of a subprogram is its
   value immediately following the successful call of the subprogram.

2. The *entry* value of a global item or parameter of a subprogram is its
   value at the call of the subprogram.

3. An *output* of a subprogram is a global item or parameter whose final value,
   or the final value of any of its reachable elements, may be updated by a
   successful call to the subprogram. The result of a
   function is also an output.  A global item or parameter which is an external
   state with the property Async_Readers => True, and for which intermediate
   values are written during an execution leading to a successful call, is also
   an output even if the final state is the same as the initial state. (see
   :ref:`external_state`). [On the contrary, a global item or parameter is not
   an output of the subprogram if it is updated only on paths that lead to an
   explicit ``raise_statement`` or to a ``pragma Assert (statically_False)`` or
   to a call to a subprogram marked ``No_Return``.]

4. An *input* of a subprogram is a global item or parameter whose
   initial value (or that of any of its reachable elements)
   may be used in determining the exit value of an
   output of the subprogram.  For a global item or parameter which is
   an external state with Async_Writers => True, each successive value
   read from the external state is also an input of the subprogram
   (see :ref:`external_state`).  As a special case, a global item or
   parameter is also an input if it is mentioned in a
   ``null_dependency_clause`` in the Depends aspect of the subprogram
   (see :ref:`depends-aspects`).

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
   (see :ref:`extensions-visible-aspects`).
   [A state abstraction cannot be fully initialized by initializing
   individual constituents unless its refinement is visible.]

.. centered:: **Legality Rules**


6. A function declaration shall not have a ``parameter_specification``
   with a mode of **out** or **in out**. This rule also applies to
   a ``subprogram_body`` for a function for which no explicit declaration
   is given. A function shall have no outputs other than its result.


7. A subprogram parameter of mode **in** shall not be an output of its
   subprogram unless the type of the parameter is an access type and
   the subprogram is not a function.


.. centered:: **Verification Rules**

8. At the point of a call, all inputs of the callee except for those that have
   relaxed initialization (see :ref:`relaxed-initialization`) shall be
   fully initialized. Similarly, upon return from a call all outputs of the
   callee except for those that have relaxed initialization shall be
   fully initialized.

.. _preconditions-and-postconditions:

Preconditions and Postconditions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**


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


.. centered:: **Verification Rules**

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

In order to extend Ada's support for specification of subprogram contracts
(e.g., the Pre and Post) by providing more precise and/or concise contracts, the
|SPARK| aspects, Global, Depends, and Contract_Cases are defined.

.. centered:: **Legality Rules**


1. The Global, Depends and Contract_Cases aspects may be
   specified for a subprogram with an ``aspect_specification``. More
   specifically, such aspect specifications are allowed in the same
   contexts as Pre or Post aspect specifications. [In particular,
   these aspects may be specified for a generic subprogram but not
   for an instance of a generic subprogram.]

2. The Global, Depends and Contract_Cases aspects shall not be specified for an
   abstract subprogram or a null procedure. Only Global'Class and Depends'Class
   may be specified for such a subprogram.


See section :ref:`contract-cases` for further detail on Contract_Case aspects, section
:ref:`global-aspects` for further detail on Global aspects and section :ref:`depends-aspects`
for further detail on Depends aspects.

.. _contract-cases:

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


.. centered:: **Syntax**

::

   contract_case_list  ::= (contract_case {, contract_case})
   contract_case       ::= condition => consequence
                         | others => consequence

where

   ``consequence ::=`` *Boolean_*\ ``expression``


.. centered:: **Legality Rules**


1. A Contract_Cases aspect may have at most one **others**
   ``contract_case`` and if it exists it shall be the last one in the
   ``contract_case_list``.


2. A ``consequence`` expression is considered to be a postcondition
   expression for purposes of determining the legality of Old or
   Result ``attribute_references``.


.. centered:: **Static Semantics**


3. A Contract_Cases aspect is an assertion (as defined in RM
   11.4.2(1.1/3)); its assertion expressions are as described
   below. Contract_Cases may be specified as an
   ``assertion_aspect_mark`` in an Assertion_Policy pragma.


.. centered:: **Dynamic Semantics**


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


.. centered:: **Verification Rules**

The verification conditions associated with the Contract_Cases runtime checks
performed at the beginning of a call are assigned in the same way
as those associated with a specific precondition check. More specifically,
the verification condition is imposed on the caller or on the callee depending
on whether the subprogram in question is a dispatching operation.

.. centered:: **Examples**

.. code-block:: ada

   -- This subprogram is specified using a Contract_Cases aspect.
   -- The prover will check that the cases are disjoint and
   -- cover the domain of X.
   procedure Incr_Threshold (X : in out Integer; Threshold : in Integer)
     with Contract_Cases => (X < Threshold  => X = X'Old + 1,
                             X >= Threshold => X = X'Old);

   -- This is the equivalent specification not using Contract_Cases.
   -- It is noticeably more complex and the prover is not able to check
   -- for disjoint cases or that he domain of X is covered.
   procedure Incr_Threshold_1 (X : in out Integer; Threshold : in Integer)
     with Pre  => (X < Threshold and not (X = Threshold))
                     or else (not (X < Threshold) and X = Threshold),
          Post => (if X'Old < Threshold then X = X'Old + 1
                   elsif X'Old = Threshold then X = X'Old);

   -- Contract_Cases can be used in conjunction with  pre and postconditions.
   procedure Incr_Threshold_2 (X : in out Integer; Threshold : in Integer)
     with Pre  => X in 0 .. Threshold,
          Post => X >= X'Old,
          Contract_Cases => (X < Threshold => X = X'Old + 1,
                             X = Threshold => X = X'Old);


.. _global-aspects:

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
using state abstraction; see section :ref:`refined-global-aspect` for further
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

.. centered:: **Syntax**


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


.. centered:: **Static Semantics**


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


.. centered:: **Name Resolution Rules**


5. A ``global_item`` shall denote an entire object or a state abstraction.
   [This is a name resolution rule because a ``global_item`` can unambiguously
   denote a state abstraction even if a function having the same fully qualified
   name is also present].


.. centered:: **Legality Rules**


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


10. A function subprogram shall not have a ``mode_selector`` of
    Output or In_Out in its Global aspect.


11. A user-defined equality operation on a record type shall have a Global
    aspect of ``null`` (see :ref:`overloading_of_operators`).

    [This avoids the case where such a record type is a component of another
    composite type, whose predefined equality operation now depends on
    variables through the primitive equality operation on its component.]


12. The ``global_items`` in a single Global aspect specification shall denote
    distinct entities.


13. If a subprogram is nested within another and if the
    ``global_specification`` of the outer subprogram has an entity
    denoted by a ``global_item`` with a ``mode_specification`` of
    Input or the entity is a formal parameter with a mode of **in**,
    then a ``global_item`` of the ``global_specification`` of the
    inner subprogram shall not denote the same entity with a
    ``mode_selector`` of In_Out or Output.


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Global aspect as it
is used purely for static analysis purposes and is not executed.

.. centered:: **Verification Rules**


14. For a subprogram that has a ``global_specification``, an object (except a
    constant without variable inputs) or state abstraction that is declared
    outside the scope of the subprogram, shall only be referenced within its
    implementation if it is a ``global_item`` in the ``global_specification``.


15. A ``global_item`` shall occur in a Global aspect of a subprogram if and
    only if it denotes an entity (except for a constant without variable
    inputs) that is referenced by the subprogram.


16. Where the refinement of a state abstraction is not visible (see
    :ref:`state_refinement`) and a subprogram references one or more
    of its constituents the constituents may be represented by a
    ``global_item`` that denotes the state abstraction in the
    ``global_specification`` of the subprogram. [The state abstraction
    encapsulating a constituent is known from the Part_Of indicator on
    the declaration of the constituent.]


17. Each entity denoted by a ``global_item`` in a
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
        shall not be used are X'Old and X'Update] and

      - it does not have relaxed initialization
        (see :ref:`relaxed-initialization`);

    * a ``global_item`` that denotes an output which is not an input and
      which has relaxed initialization may have a ``mode_selector`` of
      Output or In_Out;

    * otherwise the ``global_item`` denotes both an input and an output, and
      has a ``mode_selector`` of In_Out.


   [For purposes of determining whether an output of a subprogram shall have a
   ``mode_selector`` of Output or In_Out, reads of array bounds, discriminants,
   or tags of any part of the output are ignored. Similarly, for purposes of
   determining whether an entity is fully initialized as a result of any
   successful execution of the call, only nondiscriminant parts are considered.
   This implies that given an output of a discriminated type that is not known
   to be constrained ("known to be constrained" is defined in Ada RM 3.3), the
   discriminants of the output might or might not be updated by the call.]


18. An entity that is denoted by a ``global_item`` which is referenced
    by a subprogram but is neither an input nor an output but is only
    referenced directly, or indirectly in assertion expressions has a
    ``mode_selector`` of Proof_In.


19. A ``global_item`` shall not denote a constant object other than a formal
    parameter [of an enclosing subprogram] of mode **in**, a generic formal
    object of mode **in**, or a *constant with variable inputs*.


    If a ``global_item`` denotes a generic formal object of mode **in**,
    then the corresponding ``global_item`` in an instance of the generic
    unit may denote a constant which has no variable inputs. [This can occur
    if the corresponding actual parameter is an expression which has no
    variable inputs]. Outside of the instance, such a ``global_item`` is
    ignored. For example,

.. code-block:: ada

        generic
           Xxx : Integer;
        package Ggg is
           procedure Ppp (Yyy : in out Integer) with Global => Xxx,
                                                     Depends => (Yyy =>+ Xxx);
        end Ggg;

        package body Ggg is
           procedure Ppp (Yyy : in out Integer) is
           begin
              Yyy := Integer'Max (Xxx, Yyy);
           end Ppp;
        end Ggg;

        package Iii is new Ggg
          (Xxx => 123); -- actual parameter lacks variable inputs

        procedure Qqq (Zzz : in out Integer) with Global => null,
                                                  Depends => (Zzz =>+ null);
        procedure Qqq (Zzz : in out Integer) is
        begin
           Iii.Ppp (Yyy => Zzz);
        end Qqq;

        -- Qqq's Global and Depends aspects don't mention Iii.Xxx even though
        -- Qqq calls Iii.Ppp which does reference Iii.Xxx as a global.
        -- As seen from outside of Iii, Iii.Ppp's references to Iii.Xxx in its
        -- Global and Depends aspect specifications are ignored.


20. The ``mode_selector`` of a ``global_item`` denoting a *constant with
    variable inputs* shall be ``Input`` or ``Proof_In``.


21. The ``mode_selector`` of a ``global_item`` denoting a variable marked
    as a *constant after elaboration* shall be ``Input`` or ``Proof_In`` [,
    to ensure that such variables are only updated directly by package
    elaboration code].
    A subprogram or entry having such a ``global_item`` shall not be called
    during library unit elaboration[, to ensure only the final ("constant")
    value of the object is referenced].


.. centered:: **Examples**

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


.. _depends-aspects:

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
:ref:`verific_modes`).

For accurate information flow analysis the Depends aspect should be
present on every subprogram.

A Depends aspect for a subprogram specifies for each output every
input on which it depends. The meaning of *X depends on Y* in this
context is that the input value(s) of *Y* may affect:

* the exit value of *X*; and
* the intermediate values of *X* if it is an external state
  (see section  :ref:`external_state`), or if the subprogram
  is a nonreturning procedure [, possibly the notional nonreturning
  procedure corresponding to a task body].

This is written *X => Y*. As in UML, the entity at the tail of the
arrow depends on the entity at the head of the arrow.

If an output does not depend on any input this is indicated
using a **null**, e.g., *X =>* **null**. An output may be
self-dependent but not dependent on any other input. The shorthand
notation denoting self-dependence is useful here, X =>+ **null**.

Note that a Refined_Depends aspect may be applied to a subprogram body when
using state abstraction; see section :ref:`refined-depends-aspect` for further
details.

See section :ref:`global-aspects` regarding how the rules given in this
section apply to protected operations and to task bodies.

The Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Depends and the ``aspect_definition`` must follow
the grammar of ``dependency_relation`` given below.


.. centered:: **Syntax**


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


.. centered:: **Name Resolution Rules**


1. An ``input`` or ``output`` of a ``dependency_relation`` shall denote only
   an entire object or a state abstraction. [This is a name resolution rule
   because an ``input`` or ``output`` can unambiguously denote a state
   abstraction even if a function having the same fully qualified name is also
   present.]


.. centered:: **Legality Rules**


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
   discriminated subtype, a tagged type (with one exception), or a type having
   a subcomponent of an unconstrained discriminated subtype. The exception
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
   ``function_result``.

   [TBD: include in-mode parameters that are outputs. Do we want to
   define a term for such parameters?]


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


.. centered:: **Static Semantics**


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


21. A function without an explicit Depends aspect specification has
    the default ``dependency_relation`` that its result is dependent
    on all of its inputs. [Generally an explicit Depends aspect is
    not required for a function declaration.]


22. A procedure without an explicit Depends aspect specification has a
    default ``dependency_relation`` that each member of its output set
    is dependent on every member of its input set. [This conservative
    approximation may be improved by analyzing the body of the
    subprogram if it is present.]


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Depends aspect
as it is used purely for static analysis purposes and is not executed.

.. centered:: **Verification Rules**


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



.. centered:: **Examples**

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
   -- Depends aspects are only needed for special cases like here where the
   -- parameter Y has no discernible effect on the result of the function.

.. _class-wide-global-and-depends-aspects:

Class-Wide Global and Depends Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Global'Class and Depends'Class aspects may be specified for
a dispatching subprogram just as the Global and Depends aspects
may be specified for any subprogram (dispatching or not). [The
syntax, static semantics, and legality rules are all the same,
except that the Depends'Class aspect of a subprogram is
checked for consistency with the Global'Class aspect of the
subprogram rather than with the Global aspect.]

.. centered:: **Verification Rules**

When analyzing a dispatching call, the Global and Depends aspects
of the statically denoted callee play no role; the corresponding
class-wide aspects are used instead.

[No relationship between the Global'Class/Depends'Class aspects of a
subprogram and the subprogram's implementation is explicitly verified.
This is instead accomplished implicitly by
checking the consistency of the subprogram's implementation with
its Global/Depends aspects (as described in preceding sections) and then
checking (as described in this section) the consistency of the
Global/Depends aspects with the Global'Class/Depends'Class
aspects.]

.. centered:: **Static Semantics**

A Global or Global'Class aspect specification G2 is said to be
a *valid overriding* of another such specification, G1, if the following
conditions are met:

* each Input-mode item of G2 is an Input-mode or an In_Out-mode
  item of G1 or a direct or indirect constituent thereof; and

* each In_Out-mode item of G2 is an In_Out-mode item of G1 or a
  direct or indirect constituent thereof; and

* each Output-mode item of G2 is an Output-mode or In_Out-mode item of G1
  or a direct or indirect constituent therof; and

* each Output-mode item of G1 which is not a state abstraction whose
  refinement is visible at the point of G2 is an Output-mode item of G2; and

* for each Output-mode item of G1 which is a state abstraction whose
  refinement is visible at the point of G2, each direct or indirect
  constituent thereof is an Output-mode item of G2.

A Depends or Depends'Class aspect specification D2 is said to be a
*valid overriding* of another such specification, D1, if the set of
dependencies of D2 is a subset of the dependencies of D1 or, in the
case where D1 mentions a state abstraction whose refinement is
visible at the point of D2, if D2 is derivable from such a subset
as described in :ref:`refined-depends-aspect`.


.. centered:: **Legality Rules**

The Global aspect of a subprogram shall be a valid overriding of the
Global'Class aspect of the subprogram. The Global'Class aspect of an
an overriding subprogram shall be a valid overriding of the Global'Class
aspect(s) of the overridden inherited subprogram(s).

The Depends aspect of a subprogram shall be a valid overriding of the
Depends'Class aspect of the subprogram. The Depends'Class aspect of an
an overriding subprogram shall be a valid overriding of the Depends'Class
aspect(s) of the overridden inherited subprogram(s).

.. _extensions-visible-aspects:

Extensions_Visible Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~

1. The Extensions_Visible aspect provides a mechanism for ensuring that
   "hidden" components of a formal parameter of a specific tagged type
   are unreferenced.
   For example, if a formal parameter of a specific tagged type T is converted
   to a class-wide type and then used as a controlling operand in a dispatching
   call, then the (dynamic) callee might reference components of the parameter
   which are declared in some extension of T. Such a use of the formal parameter
   could be forbidden via an Extensions_Visible aspect specification as
   described below. The aspect also plays a corresponding role in the analysis
   of callers of the subprogram.

.. centered:: **Static Semantics**

2. Extensions_Visible is a Boolean-valued aspect which may be specified for a
   noninstance subprogram or a generic subprogram.
   If directly specified, the aspect_definition shall be a static
   [Boolean] expression. The aspect is inherited by an inherited primitive
   subprogram. If the aspect is neither inherited nor directly specified
   for a subprogram, then the aspect is False, except in the case of the
   predefined equality operator of a type extension. In that case, the
   aspect value is that of the primitive [(possibly user-defined)] equality
   operator for the parent type.

.. centered:: **Legality Rules**

3. If the Extensions_Visible aspect is False for a subprogram, then
   certain restrictions are imposed on the use of any parameter of the
   subprogram which is of a specific tagged type (or of a private type
   whose full view is a specific tagged type).
   Such a parameter shall not be converted (implicitly or explicitly) to
   a class-wide type. Such a parameter shall not be passed as an actual
   parameter in a call to a subprogram whose Extensions_Visible aspect is
   True. These restrictions also apply to any parenthesized expression,
   qualified expression, or type conversion whose operand is subject to
   these restrictions, to any Old, Update, or Loop_Entry
   ``attribute_reference`` whose prefix is subject to these restrictions,
   and to any conditional expression having at least one dependent_expression
   which is subject to these restrictions.
   [A subcomponent of a parameter is not itself a parameter and is therefore
   not subject to these restrictions. A parameter whose type is class-wide
   is not subject to these restrictions. An Old, Update, or
   Loop_Entry ``attribute_reference`` does not itself violate these
   restrictions (despite the fact that (in the tagged case) each of these
   attributes yields a result having the same underlying dynamic tag as their
   prefix).]

#. A subprogram whose Extensions_Visible aspect is True shall not override
   an inherited primitive operation of a tagged type whose
   Extensions_Visible aspect is False. [The reverse is allowed.]

#. If a nonnull type extension inherits a
   procedure having both a False Extensions_Visible aspect and one or
   more controlling out-mode parameters, then the inherited procedure
   requires overriding. [This is because the inherited procedure would not
   initialize the noninherited component(s).]

#. The Extensions_Visible aspect shall not be specified for a subprogram
   which has no parameters of either a specific tagged type or a private
   type unless the subprogram is declared in an instance of a generic
   unit and the corresponding subprogram in the generic unit satisfies
   this rule. [Such an aspect specification, if allowed, would be ineffective.]

#. [These rules ensure that the value of the underlying tag (at run time) of
   the actual parameter of a call to a subprogram whose Extensions_Visible
   aspect is False will have no effect on the behavior of that call.
   In particular, if the actual parameter has any additional components
   which are not components of the type of the formal parameter, then these
   components are unreferenced by the execution of the call.]

.. centered:: **Verification Rules**

#. [|SPARK| typically requires that an actual parameter corresponding
   to an in mode or in out mode formal parameter in a call shall be fully
   initialized before the call; similarly, the callee is typically responsible
   for fully initializing any out-mode formal parameters before returning.
   For details (including interactions with relaxed initialization), see
   the verification rule about full initialization of subprogram inputs
   and outputs (which include parameters) in :ref:`subprogram-declarations`
   and then :ref:`relaxed-initialization`].

#. In the case of a formal parameter of a specific tagged type T (or of a
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

#. [To put it another way, if the applicable Extensions_Visible aspect
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

#. [In the case of an actual parameter of a call to a subprogram whose
   Extensions_Visible aspect is False where the corresponding formal parameter
   is of a specific tagged type T, these rules imply that formal verification
   can safely assume that any components of the actual parameter which are not
   components of T will be neither read nor written by the call.]

Subprogram_Variant Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~

The aspect Subprogram_Variant is defined for subprograms. It is intended for
use in ensuring termination of recursive subprograms.

.. centered:: **Syntax**

::

  subprogram_variant_list ::= subprogram_variant_item {, subprogram_variant_item}
  subprogram_variant_item ::= change_direction => discrete_expression
  change_direction        ::= Increases | Decreases

where ``discrete_expression`` is an ``expression`` of a discrete type.

Two aspects Subprogram_Variant are said to be `compatible`, if the length of
their subprogram_variant_item_list is the same, and, for each
subprogram_variant_item,
both sequences agree on the change_direction and the base type of the
discrete_expression.

Two subprograms are said to be `statically mutually recursive`, if they are
mutually recursive ignoring indirect calls (dispatching calls and calls
through access-to-subprogram values). In the following, a direct recursive call
is considered as a special case of a statically mutually recursive call. 

The variant of a (mutually) recursive call to a subprogram which
has an aspect
Subprogram_Variant compatible with the aspect of its caller is said to
`progress` if it passes the following check.
One or more of the ``discrete_expressions`` of the callee are each compared
to the result of the evaluation of the ``discrete_expression`` of the
corresponding ``subprogram_variant_item`` at the beginning of the caller as
follows: comparisons are performed in textual order either until unequal
values are found or until values for all expressions have been compared.
In either case, the last pair of values to be compared is then checked as
follows: if the ``change_direction`` for the associated
``subprogram_variant_item`` is Increases (respectively, Decreases) then the
expression value obtained for the call is greater (respectively, less) than
the value obtained at the beginning of the caller.

.. centered:: **Static Semantics**

1. Aspect Subprogram_Variant is used to demonstrate that a (set of statically
   mutually) recursive subprogram(s)
   will terminate by specifying expressions that will increase or decrease at
   each (mutually) recursive call.

.. centered:: **Legality Rules**

2. Subprogram_Variant is an assertion and has an expected actual parameter
   which is a specialization of an Ada expression. Otherwise, it has
   the same name resolution and legality rules as aspect Precondition.

3. The expression of a ``subprogram_variant_item`` shall be of any
   discrete type.

.. centered:: **Dynamic Semantics**

4. At the beginning of a subprogram, the ``discrete_expressions`` are evaluated
   in textual order.

5. On direct recursive calls, the ``discrete_expressions`` of the
   subprogram_variant_list of the callee are evaluated in textual order.
   A check is made that the variant of the call progresses. If it fails,
   Assertion_Error is raised. [No runtime exception is raised in the case of
   mutually recursive calls or indirect calls.] Aspect Subprogram_Variant is an
   assertion (as defined in Ada RM 11.4.2(1.1/3)) and is governed by the
   Subprogram_Variant assertion aspect [and may be used in an Assertion_Policy
   pragma].

.. centered:: **Verification Rules**

6.  Statically mutually recursive subprograms shall have compatible variants.

7.  A statically mutually recursive call to a subprogram annotated with aspect
    Subprogram_Variant shall not occur inside a precondition or inside a
    Subprogram_Variant aspect.

8.  A statically mutually recursive call to a subprogram annotated with aspect
    Subprogram_Variant shall not occur inside a type invariant or subtype
    predicate, or as part of the default initialization of an object.

9.  A statically mutually recursive call to a subprogram annotated with aspect
    Subprogram_Variant shall not occur inside the elaboration of a
    package, unless this package is located in the sequence of declarations of
    a subprogram.

10. On a statically  mutually recursive call to a subprogram annotated with
    aspect Subprogram_Variant, a verification condition is introduced to
    make sure that the evaluation of the ``discrete_expressions`` of the
    subprogram_variant_list of the callee does not a raise any exception.
    Additionally, a verification condition is generated to ensure that the
    variant of the call progresses. This verification condition is already
    implicitly generated in the case where the caller and the callee are the
    same (direct recursive call) as a consequence of the runtime check taking
    place in that case. We state it explicitly for the case of mutually
    recursive calls, for which no checks are introduced at runtime due to
    compiler implementation constraints.

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

.. centered:: **Verification Rules**


1. A subprogram formal parameter of a composite type which is updated
   but not fully initialized by the subprogram shall have a mode of
   **in out**.


2. A subprogram formal parameter of mode **out** shall not be read by
   the subprogram until it has been updated by the subprogram.  The
   use of a discriminant or an attribute related to a property, not
   its value, of the formal parameter is not considered to be a read
   of the formal parameter. [Examples of attributes that may be used
   are A'First, A'Last and A'Length; examples of attributes that are
   dependent on the value of the formal parameter and shall not be
   used are X'Old and X'Update.]


.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/param_1_illegal.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/param_1_legal.adb
   :language: ada
   :linenos:


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


.. _anti-aliasing:

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

A common place for aliasing to be introduced is through the actual
parameters and between actual parameters and
global variables in a procedure call. Extra verification rules are
given that avoid the possibility of aliasing through actual
parameters and global variables.  A function is not allowed to have
side-effects and cannot update an actual parameter or global
variable.  Therefore, function calls cannot introduce aliasing and
are excluded from the anti-aliasing rules given below for procedure
calls.

.. centered:: **Static Semantics**

1. An object is said to be *interfering* if it is unsynchronized (see section
   :ref:`tasks-and-synchronization`) or it is synchronized only due to being
   *constant after elaboration* (see section :ref:`object-declarations`).

   Two names that potentially overlap (see section :ref:`access-types`)
   and which each denotes an interfering object are said to
   *potentially introduce aliasing via parameter passing*.
   [This definition has the effect of exempting most synchronized objects
   from the anti-aliasing rules given below; aliasing of most synchronized
   objects via parameter passing is allowed.]

2. A formal parameter is said to be *immutable* in the following cases:

   * it is an anonymous access-to-constant parameter; or

   * it is of mode **in** and not of an access type.

   Otherwise, the formal parameter is said to be *mutable*.

.. centered:: **Verification Rules**


3. A procedure call shall not pass two actual parameters which potentially
   introduce aliasing via parameter passing unless either

   * both of the corresponding formal parameters are immutable; or

   * at least one of the corresponding formal parameters is immutable and is of
     a by-copy type that is not an access type.


4. If an actual parameter in a procedure call and a ``global_item`` referenced
   by the called procedure potentially introduce aliasing via parameter
   passing, then

   * the corresponding formal parameter shall be immutable; and

   * if the ``global_item``'s mode is Output or In_Out, then the
     corresponding formal parameter shall be of a by-copy type that is not an
     access type.


5. Where one of these rules prohibits the occurrence of an object V or any of
   its subcomponents as an actual parameter, the following constructs are also
   prohibited in this context:

   * A type conversion whose operand is a prohibited construct;

   * A call to an instance of Unchecked_Conversion whose operand is a prohibited construct;

   * A qualified expression whose operand is a prohibited construct;

   * A prohibited construct enclosed in parentheses.


.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/anti_aliasing.adb
   :language: ada
   :linenos:


Return Statements
-----------------

No extensions or restrictions.

Nonreturning Procedures
~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Verification Rules**


1. A call to a nonreturning procedure introduces an obligation to prove that
   the statement will not be executed, much like the verification condition
   associated with

       ``pragma Assert (False);``

   [In other words, the verification conditions introduced for a call to a
   nonreturning procedure are the same as those introduced for a runtime check
   which fails unconditionally. See also section :ref:`exceptions`, where a
   similar verification rule is imposed on ``raise_statements``.]


.. _overloading_of_operators:

Overloading of Operators
------------------------

.. centered:: **Legality Rules**


1. [A user-defined equality operation on a record type shall have a Global
   aspect of ``null``; see :ref:`global-aspects` for the statement of this
   rule.]


.. centered:: **Verification Rules**

2.  A user-defined equality operation on a record type shall always
    terminate.


Null Procedures
---------------

No extensions or restrictions.


Expression Functions
--------------------

.. centered:: **Legality Rules**


1. Contract_Cases, Global and Depends aspects may be applied to an
   expression function as for any other function declaration if it
   does not have a separate declaration.  If it has a separate
   declaration then the aspects are applied to that.  It may have
   refined aspects applied (see :ref:`state_refinement`).


.. centered:: **Examples**

.. code-block:: ada

   function Expr_Func_1 (X : Natural; Y : Natural) return Natural is (X + Y)
     with Pre => X <= Natural'Last - Y;

.. _ghost-functions:

Ghost Entities
--------------

Ghost entities are intended for use in discharging verification conditions
and in making it easier to express assertions about a program. The essential
property of ghost entities is that they have no effect on the dynamic behavior
of a valid SPARK program. More specifically, if one
were to take a valid SPARK program and remove all ghost entity declarations
from it and all "innermost" statements, declarations, and pragmas which
refer to those declarations (replacing removed statements with null statements
when syntactically required), then the resulting  program might no longer be
a valid SPARK program (e.g., it might no longer be possible to discharge all
of the program's verification conditions) but its dynamic semantics (when
viewed as an Ada program) should be unaffected by this transformation. [This
transformation might affect the performance characteristics of the program
(e.g., due to no longer evaluating provably true assertions), but that
is not what we are talking about here. In rare cases, it might be necessary
to make a small additional change after the removals
(e.g., adding an Elaborate_Body pragma) in order to avoid producing a
library package that no longer needs a body (see Ada RM 7.2(4))].

.. centered:: **Static Semantics**


1. |SPARK| defines the Boolean-valued representation aspect Ghost.
   Ghost is an aspect of all entities (e.g., subprograms, types, objects).
   An entity whose Ghost aspect is True is said to be a ghost entity;
   terms such as "ghost function" or "ghost variable" are defined analogously
   (e.g., a function whose Ghost aspect is True is said to be a ghost function).
   In addition, a subcomponent of a ghost object is a ghost object.

   Ghost is an assertion aspect.
   [This means that Ghost can be named in an Assertion_Policy pragma.]


2. The Ghost aspect of an entity declared inside of a ghost entity (e.g.,
   within the body of a ghost subprogram) is defined to be True.
   The Ghost aspect of an entity implicitly declared as part of the
   explicit declaration of a ghost entity (e.g., an implicitly declared
   subprogram associated with the declaration of a ghost type) is defined
   to be True. The Ghost aspect of a child of a ghost library unit
   is defined to be True.


3. A statement or pragma is said to be a "ghost statement" if

   * it occurs within a ghost subprogram or package; or

   * it is a call to a ghost procedure; or

   * it is an assignment statement whose target is a ghost variable; or

   * it is a pragma which encloses a name denoting a ghost entity or
     which specifies an aspect of a ghost entity.


4. If the Ghost assertion policy in effect at the point of a
   ghost statement or the declaration of a ghost entity is Ignore, then the
   elaboration of that construct (at run time) has no effect,
   other Ada or |SPARK| rules notwithstanding. Similarly, the elaboration
   of the completion of a ghost entity has no effect if the Ghost
   assertion policy in effect at the point of the entity's
   initial declaration is Ignore.
   [A Ghost assertion policy of Ignore can be used to ensure that
   a compiler generates no code for ghost constructs.]
   Such a declaration is said to be a *disabled ghost declaration*;
   terms such as "disabled ghost type" and "disabled ghost subprogram"
   are defined analogously.


.. centered:: **Legality Rules**


5. The Ghost aspect may only be specified [explicitly] for
   the declaration of a subprogram, a
   generic subprogram, a type (including a partial view thereof),
   an object (or list of objects, in the case of an ``aspect_specification``
   for an ``object_declaration`` having more than one ``defining_identifier``),
   a package, or a generic package.
   The Ghost aspect may be specified via either an ``aspect_specification``
   or via a pragma. The representation pragma Ghost takes a single
   argument, a name denoting one or more entities whose Ghost aspect is
   then specified to be True.
   [In particular, |SPARK| does not currently include any form of
   ghost components of non-ghost record types, or ghost parameters of non-ghost
   subprograms. |SPARK| does define
   ghost state abstractions, but these are described elsewhere.]


6. A Ghost aspect value of False shall not be explicitly specified
   except in a confirming aspect specification. [For example, a
   non-ghost declaration cannot occur within a ghost subprogram.]

   The value specified for the Ghost assertion policy in an
   Assertion_Policy pragma shall be either Check or Ignore.
   [In other words, implementation-defined assertion policy values
   are not permitted.] The Ghost assertion policy in effect at any
   point of a SPARK program shall be either Check or Ignore.


7.  A ghost type or object shall not be effectively volatile.
    A ghost object shall not be imported or exported.
    [In other words, no ghost objects for which reading or writing
    would constitute an external effect (see Ada RM 1.1.3).]


8.  A ghost primitive subprogram of a non-ghost type extension shall
    not override an inherited non-ghost primitive subprogram.
    A non-ghost primitive subprogram of a type extension shall
    not override an inherited ghost primitive subprogram.
    [A ghost subprogram may be a primitive subprogram of a non-ghost tagged
    type.
    A ghost type extension may have a non-ghost parent type or progenitor;
    primitive subprograms of such a type may override inherited (ghost or
    non-ghost) subprograms.]


9.  A Ghost pragma which applies to a declaration occuring
    in the visible part of a package shall not occur in the
    private part of that package.
    [This rule is to ensure that the ghostliness of a visible entity can be
    determined without having to look into the private part of the
    enclosing package.]


10. A ghost entity shall only be referenced:

    * from within an assertion expression; or

    * from within an aspect specification [(i.e., either an
      ``aspect_specification`` or an aspect-specifying pragma)]; or

    * within the declaration or completion of a
      ghost entity (e.g., from within the body of a ghost subprogram); or

    * within a ghost statement; or

    * within a ``with_clause`` or ``use_clause``; or

    * within a renaming_declaration which either renames a ghost entity
      or occurs within a ghost subprogram or package.


11. A ghost entity shall not be referenced within an aspect specification
    [(including an aspect-specifying pragma)]
    which specifies an aspect of a non-ghost entity except in the
    following cases:

    * the reference occurs within an assertion expression which is
      not a predicate expression; or

    * the specified aspect is either Global, Depends,
      Refined_Global, Refined_Depends, Initializes, or Refined_State.
      [For example, the Global aspect of a non-ghost subprogram might
      refer to a ghost variable.]

   [Predicate expressions are excluded because predicates participate
   in membership tests; no Assertion_Policy pragma has any effect on
   this participation. In the case of a Static_Predicate expression,
   there are also other reasons (e.g., case statements).]


12. An **out** or **in out** mode actual parameter in a call to a ghost
    subprogram shall be a ghost variable.


13. If the Ghost assertion policy in effect at the point of the declaration
    of a ghost entity is Ignore, then the Ghost assertion policy in effect
    at the point of any reference to that entity shall be Ignore.
    If the Ghost assertion policy in effect at the point of the declaration
    of a ghost variable is Check, then the Ghost assertion policy in effect
    at the point of any assignment to a part of that variable shall be Check.
    [This includes both assignment statements and passing a ghost variable
    as an **out** or **in out** mode actual parameter.]


14. An Assertion_Policy pragma specifying a Ghost assertion policy
    shall not occur within a ghost subprogram or package.
    If a ghost entity has a completion then the Ghost assertion policies in
    effect at the declaration and at the completion of the entity shall
    be the same. [This rule applies to subprograms, packages, types,
    and deferred constants.]

    The Ghost assertion policies in effect at the point of the declaration
    of an entity and at the point of an aspect specification
    which applies to that entity shall be the same.


15. The Ghost assertion policies in effect at the declaration of a
    state abstraction and at the declaration of each constituent of that
    abstraction shall be the same.


16. The Ghost assertion policies in effect at the declaration of a
    primitive subprogram of a ghost tagged type and at
    the declaration of the ghost tagged type shall be the same.


17. If a tagged type is not a disabled ghost type, and if a
    primitive operation of the tagged type overrides an inherited operation,
    then the corresponding operation of the ancestor type shall be
    a disabled ghost subprogram if and only if the overriding subprogram
    is a disabled ghost subprogram.


18. If the Ghost assertion policy in effect at the point of an
    a reference to a Ghost entity which occurs within an assertion expression
    is Ignore, then the assertion policy which governs the assertion
    expression (e.g., Pre for a precondition expression, Assert for the
    argument of an Assert pragma) shall [also] be Ignore.


19. A ghost type shall not have a task or protected part.
    A ghost object shall not be of a type which yields synchronized objects
    (see section :ref:`tasks-and-synchronization`).
    A ghost object shall not have a volatile part.
    A synchronized state abstraction shall not be a ghost state abstraction
    (see :ref:`abstract-state-aspect`).


.. centered:: **Verification Rules**


20. A ghost procedure shall not have a non-ghost [global] output.


21. An output of a non-ghost subprogram other than a state abstraction
    or a ghost global shall not depend on a ghost input. [It is intended
    that this follows as a consequence of other rules. Although a
    non-ghost state abstraction output which depends on a ghost input may
    have a non-ghost constituent, other rules prevent such a non-ghost
    constituent from depending on the ghost input.]


22. A global input of a ghost procedure shall not be effectively volatile for reading.
    [This rule says, in effect, that ghost procedures are
    subject to the same restrictions as non-ghost nonvolatile
    functions with respect to reading volatile objects.]
    A name occurring within a ghost statement shall not denote
    an object that is effectively volatile for reading. [In other words, a ghost statement is
    subject to effectively the same restrictions as a ghost procedure.]


23. If the Ghost assertion policy in effect at the point of the declaration
    of a ghost variable or ghost state abstraction is Check, then the Ghost
    assertion policy in effect at the point of any call to a procedure
    for which that variable or state abstraction is a global output shall
    be Check.


.. centered:: **Examples**

.. code-block:: ada

   function A_Ghost_Expr_Function (Lo, Hi : Natural) return Natural is
     (if Lo > Integer'Last - Hi then Lo else ((Lo + Hi) / 2))
     with Pre        => Lo <= Hi,
          Post       => A_Ghost_Expr_Function'Result in Lo .. Hi,
          Ghost;

   function A_Ghost_Function (Lo, Hi : Natural) return Natural
     with Pre        => Lo <= Hi,
          Post       => A_Ghost_Function'Result in Lo .. Hi,
          Ghost;
   -- The body of the function is declared elsewhere.

   function A_Nonexecutable_Ghost_Function (Lo, Hi : Natural) return Natural
     with Pre        => Lo <= Hi,
          Post       => A_Nonexecutable_Ghost_Function'Result in Lo .. Hi,
          Ghost,
          Import;
   -- The body of the function is not declared elsewhere.

.. _relaxed-initialization:

Relaxed Initialization
----------------------

|SPARK| defines the Boolean-valued aspect Relaxed_Initialization and the related
Boolean-valued attribute, Initialized.

Without the Relaxed_Initialization aspect, the rules that statically prevent
reading an uninitialized scalar object are defined with "whole object"
granularity. For example, all inputs of a subprogram are required
to be fully initialized at the point of a call to the subprogram and all
outputs of a subprogram are required to be fully initialized at the point of a
return from the subprogram. The Relaxed_Initialization aspect, together with
the Initialized attribute, provides a mechanism for safely (i.e., without
introducing the possibility of improperly reading an uninitialized scalar)
referencing partially initialized Inputs and Outputs.

The Relaxed_Initialization aspect may be specified for a type, for
a standalone object, for a state abstraction, or (at least in effect - see
below for details) for a parameter or function result of a subprogram or entry.
The prefix of an Initialized attribute reference shall denote an object.

.. centered:: **Static Semantics**

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

   A state abstraction or a type has relaxed initialization if its
   Relaxed_Initialization aspect is True. An expression has relaxed
   initialization if its evaluation yields an object that has relaxed
   initialization.

2. A Relaxed_Initialization aspect specification for a formal parameter
   of a callable entity or for a function's result is expressed syntactically
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
   Relaxed_Initialization and the ``aspect_definition`` follows the
   following grammar for ``profile_aspect_spec``:

   ::

      profile_aspect_spec ::= ( profile_spec_item {, profile_spec_item} )
      profile_spec_item   ::= parameter_name [=> aspect_definition]
                            | function_name'Result [=> aspect_definition]

3. Relaxed_Initialization aspect specifications are inherited by
   a derived type (if the aspect is specified for the ancestor type)
   and by an inherited subprogram (if the aspect is specified for the
   corresponding primitive subprogram of the ancestor type).

4. For a prefix *X* that denotes an object, the following attribute is defined:

   ::

      X'Initialized

   X'Initialized is True if and only if every scalar reachable element of X
   has been initialized. [It typicallly follows as a consequence of this
   definition and the other rules of |SPARK| that if X'Initialized is True,
   then for every reachable element Y of X (scalar or not), Y belongs to its
   subtype. There are pathological counterexamples, such as a componentless
   record declared with "Dynamic_Predicate => False".] An Initialized attribute
   reference is never a static expression.

.. centered:: **Legality Rules**

5. The following rules apply to the profile_aspect_spec of a
   Relaxed_Initialization aspect specification for a subprogram, a
   generic subprogram, or an entry.

   * Each parameter_name shall name a parameter of the given callable
     entity and no parameter shall be named more than once. It is not
     required that every parameter be named.

   * Each aspect_definition within a profile_aspect_spec shall be as for a
     Boolean aspect.

   * The form of profile_spec_item that includes a Result
     attribute reference shall only be provided if the given callable
     entity is a function or generic function; in that case, the prefix
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

6. A constituent of a state abstraction shall have relaxed initialization
   if and only if the state abstraction has relaxed initialization.

7. No part of a tagged type, or of a tagged object, shall have relaxed
   initialization.

8. No part of an effectively volatile type, or of an effectively volatile
   object, shall have relaxed initialization.

9. No part of an Unchecked_Union type shall have relaxed initialization.
   No part of the type of the prefix of an Initialized attribute reference
   shall be of an Unchecked_Union type.

10. A Relaxed_Initialization aspect specification which applies to a
    declaration occuring in the visible part of a package [(e.g., the
    declaration of a private type or of a deferred constant)] shall not
    occur in the private part of that package.

11. A formal parameter of a dispatching operation shall not have relaxed
    initialization; the result of a dispatching function shall not have
    relaxed initialization.

.. centered:: **Verification Rules**

12. At the point of a read of a scalar object X that has relaxed initialization,
    a verification condition is introduced to ensure that X is initialized.
    This includes the case where X is a subcomponent of a composite object
    that is passed as an argument in a call to a predefined relational
    operator (e.g., "=" or "<"). Such a verification condition is also
    introduced in the case where X is a reachable element of the [source]
    expression of an assignment operation and the target of the assignment
    does not have relaxed initialization, where X is a reachable element of
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

13. For any object X, evaluation of X'Initialized includes the evaluation
    of Y'Initialized for every scalar reachable element Y of X (excluding
    "hidden" components of tagged objects - see :ref:`type_invariants`).
    Evaluation of X'Initialized for a scalar object X is considered to be a
    read of X if and only if X does not have relaxed initialization. If X has
    relaxed initialization, then an evaluation of X'Initialized is instead
    treated like an evaluation of X'Valid [, which is not a read
    of X]. If X does not have relaxed initialization, then this implies
    that evaluation of X'Initialized introduces the same initialization
    requirements as would be introduced for any other read of X; as a result
    of meeting these requirements, X'Initialized will always return
    True for such an object.
