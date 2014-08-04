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
a subprogram.

.. centered:: **Static Semantics**

1. The *exit* value of a global item or parameter of a subprogram is its
   value immediately following the successful call of the subprogram.

2. The *entry* value of a global item or parameter of a subprogram is its
   value at the call of the subprogram.

3. An *output* of a subprogram is a global item or parameter whose final value
   may be updated by a successful call to the subprogram.  The result of a
   function is also an output.  A global item or parameter which is an external
   state with the property Async_Readers => True, and for which intermediate
   values are written during an execution leading to a successful call, is also
   an output even if the final state is the same as the initial state. (see
   :ref:`external_state`). [On the contrary, a global item or parameter is not
   an output of the subprogram if is updated only on paths that lead to an
   explicit ``raise_statement`` or to a ``pragma Assert (statically_False)`` or
   to a call to a subprogram marked ``No_Return``.]

4. An *input* of a subprogram is a global item or parameter whose
   initial value may be used in determining the exit value of an
   output of the subprogram.  For a global item or parameter which is
   an external state with Async_Writers => True, each successive value
   read from the external state is also an input of the subprogram
   (see :ref:`external_state`).  As a special case, a global item or
   parameter is also an input if it is mentioned in a
   ``null_dependency_clause`` in the Depends aspect of the subprogram
   (see :ref:`depends-aspects`).

.. centered:: **Legality Rules**

.. _tu-fe-subprogram_declarations-05:

5. A function declaration shall not have a ``parameter_specification``
   with a mode of **out** or **in out**. This rule also applies to
   a ``subprogram_body`` for a function for which no explicit declaration
   is given.

.. _etu-subprogram_declarations:

.. _preconditions-and-postconditions:

Preconditions and Postconditions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-nt-preconditions_and_postconditions-01:

1. As indicated by the ``aspect_specification`` being part of a
   ``subprogram_declaration`` or ``subprogram_body``, a subprogram is
   in |SPARK| only if its specific contract expressions (introduced by
   Pre and Post), if any, are in |SPARK|.

.. _etu-preconditions_and_postconditions-lr:

.. centered:: **Static Semantics**

.. _tu-nt-preconditions_and_postconditions-02:

2. For an ``expression_function_declaration``, F, without an explicit
   Postcondition, the expression, E, implementing the function acts as
   its Postcondition, that is the default postcondition is F'Result =
   E.

.. _etu-preconditions_and_postconditions-ss:

In general the expression, E, of a postcondition of a function may be used as
the expression of an ``expression_function_declaration`` instead making E both
the implementation of the function and the expression of its [default]
postcondition.

Subprogram Contracts
~~~~~~~~~~~~~~~~~~~~

In order to extend Ada's support for specification of subprogram contracts
(e.g., the Pre and Post) by providing more precise and/or concise contracts, the
|SPARK| aspects, Global, Depends, and Contract_Cases are defined.

.. centered:: **Legality Rules**

.. _tu-nt-subprogram_contracts-01:

1. The Global, Depends and Contract_Cases aspects may be
   specified for a subprogram with an ``aspect_specification``. More
   specifically, such aspect specifications are allowed in the same
   contexts as Pre or Post aspect specifications except for two cases:
   unlike Pre or Post, these aspects shall not be specified for a generic
   subprogram but may be specified for an instance of a generic subprogram.

.. _etu-subprogram_contracts:

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

.. _tu-fe-contract_cases-01:

1. A Contract_Cases aspect may have at most one **others**
   ``contract_case`` and if it exists it must be the last one in the
   ``contract_case_list``.

.. _tu-fe-contract_cases-02:

2. A ``consequence`` expression is considered to be a postcondition
   expression for purposes of determining the legality of Old or
   Result ``attribute_references``.

.. _etu-contract_cases-lr:

.. centered:: **Static Semantics**

.. _tu-fe-contract_cases-03:

3. A Contract_Cases aspect is an assertion (as defined in RM
   11.4.2(1.1/3)); its assertion expressions are as described
   below. Contract_Cases may be specified as an
   ``assertion_aspect_mark`` in an Assertion_Policy pragma.

.. _etu-contract_cases-ss:

.. centered:: **Dynamic Semantics**

.. _tu-fe-contract_cases-04:

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

.. _tu-fe-contract_cases-05:

5. If an Old ``attribute_reference`` occurs within a ``consequence``
   other than the ``consequence`` selected for (later) evaluation
   as described above, then the associated implicit constant declaration
   (see Ada RM 6.1.1) is not elaborated. [In particular, the prefix of the
   Old ``attribute_reference`` is not evaluated].

.. _etu-contract_cases-ds:


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

The Global aspect may only be specified for the initial declaration of a
subprogram (which may be a declaration, a body or a body stub).
The implementation of a subprogram body must be consistent with the
subprogram's Global aspect.

Note that a Refined_Global aspect may be applied to a subprogram body when
using state abstraction; see section :ref:`refined-global-aspect` for further
details.

The Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Global and the ``aspect_definition`` must
follow the grammar of ``global_specification``

.. centered:: **Syntax**

.. _tu-fe-global_aspects-syntax:

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

.. _etu-global_aspects-syntax:

.. centered:: **Static Semantics**

.. _tu-fa-global_aspects-01:

1. A ``global_specification`` that is a ``global_list`` is shorthand for a
   ``moded_global_list`` with the ``mode_selector`` Input.

.. _tu-cbatu-global_aspects-02:

2. A ``global_item`` is *referenced* by a subprogram if:

   * It denotes an input or an output of the subprogram, or;

   * Its entry value is used to determine the value of an assertion
     expression within the subprogram, or;

   * Its entry value is used to determine the value of an assertion
     expression within another subprogram that is called either directly or
     indirectly by this subprogram.

.. _tu-fa-global_aspects-03:

3. A ``null_global_specification`` indicates that the subprogram does not
   reference any ``global_item`` directly or indirectly.

.. _etu-global_aspects-ss:

.. centered:: **Name Resolution Rules**

.. _tu-fe-global_aspects-04:

4. A ``global_item`` shall denote an entire object or a state abstraction.
   [This is a name resolution rule because a ``global_item`` can unambiguously
   denote a state abstraction even if a function having the same fully qualified
   name is also present].

.. _etu-global_aspects-nr:

.. centered:: **Legality Rules**

.. _tu-fe-global_aspects-05:

5. The Global aspect may only be specified for the initial declaration of a
   subprogram (which may be a declaration, a body or a body stub).

.. _tu-fe-global_aspects-06:

6. A ``global_item`` occurring in a Global aspect specification of a subprogram
   shall not denote a formal parameter of the subprogram.

.. _tu-fe-global_aspects-07:

7. A ``global_item`` shall not denote a constant object other than a formal
   parameter [of an enclosing subprogram] of mode **in** or a *constant
   with variable input*.

.. _tu-fe-global_aspects-08:

8. A ``global_item`` shall not denote a state abstraction whose
   refinement is visible. [A state abstraction cannot be named within
   its enclosing package's body other than in its refinement. Its
   constituents must be used rather than the state abstraction.]

.. _tu-fe-global_aspects-09:

9. Each ``mode_selector`` shall occur at most once in a single
   Global aspect.

.. _tu-fe-global_aspects-10:

10. A function subprogram shall not have a ``mode_selector`` of
    Output or In_Out in its Global aspect.

.. _tu-fe-global_aspects-11:

11. The ``global_items`` in a single Global aspect specification shall denote
    distinct entities.

.. _tu-fe-global_aspects-12:

12. If a subprogram is nested within another and if the
    ``global_specification`` of the outer subprogram has an entity
    denoted by a ``global_item`` with a ``mode_specification`` of
    Input or the entity is a formal parameter with a mode of **in**,
    then a ``global_item`` of the ``global_specification`` of the
    inner subprogram shall not denote the same entity with a
    ``mode_selector`` of In_Out or Output.

.. _etu-global_aspects-lr:

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Global aspect as it
is used purely for static analysis purposes and is not executed.

.. centered:: **Verification Rules**

.. _tu-fa-global_aspects-13:

13. For a subprogram that has a ``global_specification``, an object or
    state abstraction that is declared outside the scope of the
    subprogram, shall only be referenced within its implementation if
    it is a ``global_item`` in the ``global_specification``.

.. _tu-fa-global_aspects-14:

14. A ``global_item`` shall occur in a Global aspect of a subprogram
    if and only if it denotes an entity that is referenced by the
    subprogram.

.. _tu-cbatu-global_aspects-15:

15. Where the refinement of a state abstraction is not visible (see
    :ref:`state_refinement`) and a subprogram references one or more
    of its constituents the constituents may be represented by a
    ``global_item`` that denotes the state abstraction in the
    ``global_specification`` of the subprogram. [The state abstraction
    encapsulating a constituent is known from the Part_Of indicator on
    the declaration of the constituent.]

.. _tu-fa-global_aspects-16:

16. Each entity denoted by a ``global_item`` in a
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

      - is always *fully initialized* (that is, all parts of the
        ``global_item`` are initialized) as a result of any successful
        execution of a call of the subprogram. A state abstraction
        whose refinement is not visible is not fully initialized by
        only updating one or more of its constituents [because it may
        have other constituents that are not visible];

    * otherwise the ``global_item`` denotes both an input and an output, and
      has a ``mode_selector`` of In_Out.

.. _tu-fa-global_aspects-16.1:

   [For purposes of determining whether an output of a subprogram shall have a
   ``mode_selector`` of Output or In_Out, reads of array bounds, discriminants,
   or tags of any part of the output are ignored. Similarly, for purposes of
   determining whether an entity is fully initialized as a result of any
   successful execution of the call", only nondiscriminant parts are considered.
   This implies that given an output of a discriminated type that is not known
   to be constrained ("known to be constrained" is defined in Ada RM 3.3), the
   discriminants of the output might or might not be updated by the call.]

.. _tu-fa-global_aspects-17:

17. An entity that is denoted by a ``global_item`` which is referenced
    by a subprogram but is neither an input nor an output but is only
    referenced directly, or indirectly in assertion expressions has a
    ``mode_selector`` of Proof_In.

.. _tu-fa-global_aspects-18:

18. The ``mode_selector`` of a ``global_item`` denoting a *constant with
    variable input* must be ``Input`` or ``Proof_In``.

.. _etu-global_aspects-vr:

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

Unlike a post condition, the functional behavior of a subprogram is
not specified by the Depends aspect but the Depends aspect has to be
complete in the sense that every input and output of the subprogram
must appear in it.  Whereas, a postcondition may be partial and only
specify properties of particular interest.

Like a postcondition, the dependency relation may be omitted from a
subprogram declaration in when it defaults to the conservative
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
  (see section  :ref:`external_state`).

This is written *X => Y*. As in UML, the entity at the tail of the
arrow depends on the entity at the head of the arrow.

If an output does not depend on any input this is indicated
using a **null**, e.g., *X =>* **null**. An output may be
self-dependent but not dependent on any other input. The shorthand
notation denoting self-dependence is useful here, X =>+ **null**.

Note that a Refined_Depends aspect may be applied to a subprogram body when
using state abstraction; see section :ref:`refined-depends-aspect` for further
details.

The Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Depends and the ``aspect_definition`` must follow
the grammar of ``dependency_relation`` given below.


.. centered:: **Syntax**

.. _tu-fe-depends_aspects-syntax:

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

.. _etu-depends_aspects-syntax:

.. centered:: **Name Resolution Rules**

.. _tu-fe-depends_aspects-01:

1. An ``input`` or ``output`` of a ``dependency_relation`` shall denote only
   an entire object or a state abstraction. [This is a name resolution rule
   because an ``input`` or ``output`` can unambiguously denote a state
   abstraction even if a function having the same fully qualified name is also
   present.]

.. _etu-depends_aspects-nr:

.. centered:: **Legality Rules**

.. _tu-fe-depends_aspects-02:

2. The Depends aspect shall only be specified for the initial declaration of a
   subprogram (which may be a declaration, a body or a body stub).

.. _tu-fe-depends_aspects-03:

3. An ``input`` or ``output`` of a ``dependency_relation`` shall not denote a
   state abstraction whose refinement is visible [a state abstraction cannot be
   named within its enclosing package's body other than in its refinement].

.. _tu-fe-depends_aspects-04:

4. The *explicit input set* of a subprogram is the set of formal parameters of
   the subprogram of mode **in** and **in out** along with the entities denoted
   by ``global_items`` of the Global aspect of the subprogram with a
   ``mode_selector`` of Input and In_Out.

.. _tu-fe-depends_aspects-05:

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

.. _tu-fe-depends_aspects-06:

6. The *output set* of a subprogram is the set of formal parameters of the
   subprogram of mode **in out** and **out** along with the entities denoted by
   ``global_items`` of the Global aspect of the subprogram with a
   ``mode_selector`` of In_Out and Output and (for a function) the
   ``function_result``.

.. _tu-fe-depends_aspects-07:

7. The entity denoted by each ``input`` of a ``dependency_relation`` of a
   subprogram shall be a member of the input set of the subprogram.

.. _tu-fe-depends_aspects-08:

8. Every member of the explicit input set of a subprogram shall be denoted by
   at least one ``input`` of the ``dependency_relation`` of the subprogram.

.. _tu-fe-depends_aspects-09:

9. The entity denoted by each ``output`` of a ``dependency_relation`` of a
   subprogram shall be a member of the output set of the subprogram.

.. _tu-fe-depends_aspects-10:

10. Every member of the output set of a subprogram shall be denoted by exactly
    one ``output`` in the ``dependency_relation`` of the subprogram.

.. _tu-fa-depends_aspects-11:

11. For the purposes of determining the legality of a Result
    ``attribute_reference``, a ``dependency_relation`` is considered
    to be a postcondition of the function to which the enclosing
    ``aspect_specification`` applies.

.. _tu-fe-depends_aspects-12:

12. In a ``dependency_relation`` there can be at most one
    ``dependency_clause`` which is a ``null_dependency_clause`` and if
    it exists it must be the last ``dependency_clause`` in the
    ``dependency_relation``.

.. _tu-fe-depends_aspects-13:

13. An entity denoted by an ``input`` which is in an ``input_list`` of
    a ``null_dependency_clause`` shall not be denoted by an ``input``
    in another ``input_list`` of the same ``dependency_relation``.

.. _tu-fe-depends_aspects-14:

14. The ``inputs`` in a single ``input_list`` shall denote distinct entities.

.. _tu-fe-depends_aspects-15:

15. A ``null_dependency_clause`` shall not have an ``input_list`` of **null**.

.. _etu-depends_aspects-lr:

.. centered:: **Static Semantics**

.. _tu-fa-depends_aspects-16:

16. A ``dependency_clause`` with a "+" symbol in the syntax
    ``output_list`` =>+ ``input_list`` means that each ``output`` in
    the ``output_list`` has a *self-dependency*, that is, it is
    dependent on itself. [The text (A, B, C) =>+ Z is shorthand for
    (A => (A, Z), B => (B, Z), C => (C, Z)).]

.. _tu-cbatu-depends_aspects-17:

17. A ``dependency_clause`` of the form A =>+ A has the same meaning
    as A => A.  [The reason for this rule is to allow the short hand:
    ((A, B) =>+ (A, C)) which is equivalent to (A => (A, C), B => (A,
    B, C)).]

.. _tu-fa-depends_aspects-18:

18. A ``dependency_clause`` with a **null** ``input_list`` means that
    the final value of the entity denoted by each ``output`` in the
    ``output_list`` does not depend on any member of the input set of
    the subprogram (other than itself, if the ``output_list`` =>+
    **null** self-dependency syntax is used).

.. _tu-fa-depends_aspects-19:

19. The ``inputs`` in the ``input_list`` of a
    ``null_dependency_clause`` may be read by the subprogram but play
    no role in determining the values of any outputs of the
    subprogram.

.. _tu-fa-depends_aspects-20:

20. A Depends aspect of a subprogram with a **null**
    ``dependency_relation`` indicates that the subprogram has no
    ``inputs`` or ``outputs``.  [From an information flow analysis
    viewpoint it is a null operation (a no-op).]

.. _tu-cbatu-depends_aspects-21:

21. A function without an explicit Depends aspect specification has
    the default ``dependency_relation`` that its result is dependent
    on all of its inputs. [Generally an explicit Depends aspect is
    not required for a function declaration.]

.. _tu-fa-depends_aspects-22:

22. A procedure without an explicit Depends aspect specification has a
    default ``dependency_relation`` that each member of its output set
    is dependent on every member of its input set. [This conservative
    approximation may be improved by analyzing the body of the
    subprogram if it is present.]

.. _etu-depends_aspects-ss:

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Depends aspect
as it is used purely for static analysis purposes and is not executed.

.. centered:: **Verification Rules**

.. _tu-fa-depends_aspects-23:

23. Each entity denoted by an ``output`` given in the Depends aspect
    of a subprogram must be an output in the implementation of the
    subprogram body and the output must depend on all, but only, the
    entities denoted by the ``inputs`` given in the ``input_list``
    associated with the ``output``.

.. _tu-fa-depends_aspects-24:

24. Each output of the implementation of the subprogram body is denoted by
    an ``output`` in the Depends aspect of the subprogram.

.. _tu-fa-depends_aspects-25:

25. Each input of the implementation of a subprogram body is denoted by an
    ``input`` of the Depends aspect of the subprogram.

.. _tu-fa-depends_aspects-26:

26. If only part of an entire object or state abstraction (only some
    of its constituents) is updated then the updated entity is
    dependent on itself as the parts that are not updated have their
    current value preserved. [Where a constituent of a state
    abstraction is updated but the refinement of the state abstraction
    is not visible, it is not known if all of the constituents have
    been updated by the subprogram and in such cases the the update is
    represented as the the update of the encapsulating state
    abstraction with a self dependency.]

.. _etu-depends_aspects-vr:

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


.. _extensions-visible-aspects:

Extensions_Visible Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~

The Extensions_Visible aspect provides a mechanism for ensuring that
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

Extensions_Visible is a Boolean-valued aspect which may be specified for a
subprogram. If directly specified, the aspect_definition shall be a static
[Boolean] expression. The aspect is inherited by an inherited primitive
subprogram. If the aspect is neither inherited nor directly specified
for a subprogram, then the aspect is False.

.. centered:: **Legality Rules**

If the Extensions_Visible aspect is False for a subprogram, then
certain restrictions are imposed on the use of any parameter of the
subprogram which is of a specific tagged type (or of a private type
whose full view is a specific tagged type).

Such a parameter shall not be converted (implicitly or explicitly) to
a class-wide type. Such a parameter shall not be passed as an actual
parameter in a call to a subprogram whose Extensions_Visible aspect is
True. These restrictions also apply to any parenthesized expression,
qualified expression, or type conversion whose operand is subject to
these restrictions, and to any conditional expression having at least
one dependent_expression which is subject to these restrictions.

[A subcomponent of a parameter is not itself a parameter and is therefore
not subject to these restrictions. A parameter whose type is class-wide
is not subject to these restrictions.]

[The restriction disallowing implicit conversion to a class-wide type
applies, in particular, in the case described in Ada RM 6.1.1:

  Within the expression for a Pre'Class or Post'Class aspect for a primitive
  subprogram of a tagged type T, a name that denotes a formal parameter of type
  T is interpreted as having type T'Class.

.]

A subprogram whose Extensions_Visible aspect
is True shall not override an inherited primitive operation of a
tagged type whose Extensions_Visible aspect is False.
[The reverse is allowed.]

The Extensions_Visible aspect shall not be specified for a subprogram
which has no parameters of either a specific tagged type or a private
type unless the subprogram is declared in an instance of a generic
unit and the corresponding subprogram in the generic unit satisfies
this rule. [Such an aspect specification, if allowed, would be ineffective.]

[These rules ensure that the value of the underlying tag (at run time) of
the actual parameter of a call to an "Extensions_Visible => False"
subprogram will have no effect on the behavior of that call. In particular,
if the actual parameter has any additional components which are not components
of the type of the formal parameter, then these components are unreferenced by
the execution of the call.]

.. centered:: **Verification Rules**

|SPARK| requires that an actual parameter corresponding
to an in mode or in out mode formal parameter in a call must be fully
initialized before the call; similarly, the callee is responsible
for fully initializing any out-mode parameters before returning.

In the case of a formal parameter of a specific tagged type T (or of a
private type whose full view is a specific tagged type), the set of
components which must be initialized in order to meet these requirements
depends on the Extensions_Visible aspect of the callee.

If the aspect is False, then that set of components is the
[statically known] set of non-discriminant components of T.

If the aspect is True, then this set is the set of non-discriminant
components of the specific type associated with the tag of the
corresponding actual parameter. [In general, this is not statically known.
This set will always include the non-discriminant components of T, but
it may also include additional components.]

[To put it another way, if the applicable Extensions_Visible aspect
is True, then the initialization requirements (for both the caller and
the callee) for a parameter of a specific tagged type T are the same as
if the formal parameter's type were T'Class. If the aspect is False,
then components declared in proper descendants of T need not be initialized.
In the case of an out mode parameter, such initialization by the callee
is not only not required, it is effectively forbidden because
such an out-mode parameter could not be fully initialized
without some form of dispatching (e.g., a class-wide assignment or a
dispatching call in which an out-mode parameter is a controlling operand).
Such a dispatching call will always fully initialize its controlling
out-mode parameters, regardless of the Extensions_Visible aspect
of the callee. An assignment statement whose target is of a class-wide
type T'Class is treated, for purposes of formal verification, like a call to a
procedure with two parameters of type T'Class, one of mode out and
one of mode in.]

[In the case of an actual parameter of a call to a subprogram whose
Extensions_Visible aspect is False where the corresponding formal parameter
is of a specific tagged type T, these rules imply that formal verificaiton can
safely assume that any components of the actual parameter which are not
components of T will be neither read nor written by the call.]


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

.. _tu-fa-formal_parameter_modes-01:

1. A subprogram formal parameter of a composite type which is updated
   but not fully initialized by the subprogram shall have a mode of
   **in out**.

.. _tu-fa-formal_parameter_modes-02:

2. A subprogram formal parameter of mode **out** shall not be read by
   the subprogram until it has been updated by the subprogram.  The
   use of a discriminant or an attribute related to a property, not
   its value, of the formal parameter is not considered to be a read
   of the formal parameter. [Examples of attributes that may be used
   are A'First, A'Last and A'Length; examples of attributes that are
   dependent on the value of the formal parameter and shall not be
   used are X'Old and X'Update.]

.. _etu-formal_parameter_modes:

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

1. Objects are assumed to have overlapping locations if it cannot be established
   statically that they do not.

.. todo:: This definition of overlapping is necessary since
          these anti-aliasing checks are implemented by flow analysis;
          If checks are implemented by the proof engine instead, these static
          checking may be suppressed.

.. centered:: **Dynamic Semantics**

No extra dynamic semantics are associated with anti-aliasing.

.. centered:: **Verification Rules**

.. _tu-anti_aliasing-02:

2. A procedure call shall not pass actual parameters which denote objects
   with overlapping locations, when at least one of the corresponding formal
   parameters is of mode **out** or **in out**, unless the other corresponding
   formal parameter is of mode **in** and is of a by-copy type.

.. _tu-anti_aliasing-03:

3. A procedure call shall not pass an actual parameter, whose corresponding
   formal parameter is mode **out** or **in out**, that denotes an object which
   overlaps with any ``global_item`` referenced by the subprogram.

.. _tu-anti_aliasing-04:

4. A procedure call shall not pass an actual parameter which denotes an object
   which overlaps a ``global_item`` of mode **out** or **in out** of the subprogram,
   unless the corresponding formal parameter is of mode **in** and by-copy.

.. _tu-anti_aliasing-05:

5. Where one of these rules prohibits the occurrence of an object V or any of its subcomponents
   as an actual parameter, the following constructs are also prohibited in this context:

   * A type conversion whose operand is a prohibited construct;

   * A call to an instance of Unchecked_Conversion whose operand is a prohibited construct;

   * A qualified expression whose operand is a prohibited construct;

   * A prohibited construct enclosed in parentheses.

.. _etu-anti_aliasing:

.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/anti_aliasing.adb
   :language: ada
   :linenos:


Return Statements
-----------------

No extensions or restrictions.

Nonreturning Procedures
~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-sf-nonreturning_procedures-01:

1. For a call to a nonreturning procedure to be in |SPARK|, it must be either

   * immediately enclosed by an if statement which encloses no other
     statement; or

   * the last statement of a subprogram.

.. _etu-nonreturning_procedures-lr:

.. centered:: **Verification Rules**

.. _tu-nonreturning_procedures-02:

2. A call to a nonreturning procedure introduces an obligation to prove that the statement
   will not be executed, much like the verification condition associated with

       ``pragma Assert (False);``

   [In other words, the verification conditions introduced for a call to a nonreturning procedure
   are the same as those introduced for a runtime check which fails
   unconditionally. See also section :ref:`exceptions`, where a similar restriction is
   imposed on ``raise_statements``.]

.. _etu-nonreturning_procedures-vr:


Overloading of Operators
------------------------

No extensions or restrictions.

Null Procedures
---------------

No extensions or restrictions.


Expression Functions
--------------------

.. centered:: **Legality Rules**

.. _tu-expression-functions-01:

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

Ghost Functions
---------------

Ghost functions are intended for use in discharging verification conditions and in
making it easier to express assertions about a program. The essential property
of ghost functions is that they have no effect on the dynamic behavior of a
valid SPARK program other than, depending on the assertion policy, the execution
of known to be true assertion expressions. More specifically, if one were to
take a valid SPARK program and remove all ghost function declarations from it
and all assertions containing references to those functions, then the resulting
program might no longer be a valid SPARK program (e.g., it might no longer be
possible to discharge all the program's verification conditions) but its dynamic
semantics (when viewed as an Ada program) should be unaffected by this
transformation other than evaluating fewer known to be true assertion
expressions.

The rules below are given in general terms in relation to "ghost
entities" to allow room for ghost types and ghost variables.
Currently, however, only ghost functions are allowed and so an additional
legality rule is provided that allows only functions to be explicitly
declared as a ghost (though entities declared within a ghost function are
regarded implicitly as ghost entities).

.. todo::
   Add ghost types and ghost variables to |SPARK|. To be completed in
   a post-Release 1 version of this document.

.. centered:: **Static Semantics**

.. _tu-cbatu-ghost_functions-01:

1. |SPARK| defines the ``convention_identifier`` Ghost.
   An entity (e.g., a subprogram or an object) whose Convention aspect is
   specified to have the value Ghost is said to be a ghost entity (e.g., a ghost
   function or a ghost variable).

.. _tu-nt-ghost_functions-02:

2. The Convention aspect of an entity declared inside of a ghost entity (e.g.,
   within the body of a ghost function) is defined to be Ghost.

.. _tu-nt-ghost_functions-03:

3. The Link_Name aspect of an imported ghost entity is defined
   to be a name that cannot be resolved in the external environment.

.. _etu-ghost_functions-ss:

.. centered:: **Legality Rules**

.. _tu-fe-ghost_functions-04:

4. Only functions can be explicitly declared with the Convention aspect Ghost.
   [This means that the scope of the following rules is restricted to functions,
   even though they are stated in more general terms.]

.. _tu-fe-ghost_functions-05:

5. A ghost entity shall only be referenced:

   * from within an assertion expression; or

   * within or as part of the declaration or completion of a
     ghost entity (e.g., from within the body of a ghost function); or

   * within a statement which does not contain (and is not itself) either an
     assignment statement targeting a non-ghost variable or a procedure call
     which passes a non-ghost variable as an out or in out mode actual
     parameter.

.. _tu-fe-ghost_functions-06:

6. Within a ghost procedure, the view of any non-ghost variable is
   a constant view. Within a ghost procedure, a volatile object shall
   not be read. [In a ghost procedure we do not want to allow assignments to
   non-ghosts either via assignment statements or procedure calls.]

.. _tu-fe-ghost_functions-07:

7. A ghost entity shall not be referenced from within the expression of a
   predicate specification of a non-ghost subtype [because such predicates
   participate in determining the outcome of a membership test].

.. _tu-nt-ghost_functions-08:

8. Rule removed.

   .. todo:: Is the following rule needed?  8. All subcomponents of a
        ghost object shall be initialized by the elaboration of the
        declaration of the object.  Make worst-case assumptions about
        private types for this rule, or blast through privacy? To be
        decided in a post-Release 1 version of this document.

.. _tu-fe-ghost_functions-09:

9. A ghost instantiation shall not be an instantiation of a non-ghost
   generic package. [This is a conservative rule until we have more precise
   rules about the side effects of elaborating an instance of a generic package.
   We will need the general rule that the elaboration of a ghost declaration of
   any kind cannot modify non-ghost state.]

.. _tu-nt-ghost_functions-10:

10. The Link_Name or External_Name aspects of an imported ghost entity
    shall not be specified. A Convention aspect specification for an
    entity declared inside of a ghost entity shall be confirming [(in
    other words, the specified Convention shall be Ghost)].

.. _tu-nt-ghost_functions-11:

11. Ghost tagged types are disallowed. [This is because just the
    existence of a ghost tagged type (even if it is never referenced)
    changes the behavior of Ada.Tags operations. Note overriding is
    not a problem because the Convention aspect participates in conformance
    checks (so ghost can't override non-ghost and vice versa).]

.. _tu-fe-ghost_functions-12:

12. The Convention aspect of an External entity shall not be Ghost.

.. _etu-ghost_functions-lr:

[We are ignoring interactions between ghostliness and freezing. Adding a ghost
variable, for example, could change the freezing point of a non-ghost type. It
appears that this is ok; that is, this does not violate the
ghosts-have-no-effect-on-program-behavior rule.]

.. todo::
   Can a ghost variable be a constituent of a non-ghost state
   abstraction, or would this somehow allow unwanted dependencies?
   If not, then we presumably need to allow ghost state abstractions
   or else it would be illegal for a library level package body to
   declare a ghost variable. To be completed in a post-Release 1
   version of this document.

.. todo::
   Do we want an implicit Ghost convention for an entity declared
   within a statement whose execution depends on a ghost value?
   To be completed in a post-Release 1 version of this document.

.. centered:: **Dynamic Semantics**

.. _tu-nt-ghost_functions-13:

13. The effects of specifying a convention of Ghost on the runtime
    representation, calling conventions, and other such dynamic
    properties of an entity are the same as if a convention of Ada had
    been specified.

    [If it is intended that a ghost entity should not have any runtime
    representation (e.g., if the entity is used only in discharging
    verification conditions and is not referenced (directly or indirectly)
    in any enabled (e.g., via an Assertion_Policy pragma) assertions),
    then the Import aspect of the entity may be specified to be True.]

.. _etu-ghost_functions-ds:

.. centered:: **Verification Rules**

.. _tu-cbatu-ghost_functions-14:

14. A non-ghost output shall not depend on a ghost input.

.. _tu-fe-ghost_functions-15:

15. A ghost entity shall not be referenced

    * within a call to a procedure which has a non-ghost output; or

    * within a control flow expression (e.g., the condition of an if
      statement, the selecting expression of a case statement, the
      bounds of a for loop) of a compound statement which contains
      such a procedure call. [The case of a non-ghost-updating
      assignment statement is handled by a legality rule; this rule is
      needed to prevent a call to a procedure which updates a
      non-ghost via an up-level reference, as opposed to updating a
      parameter.]

      [This rule is intended to ensure an update of a non-ghost entity
      shall not have a control flow dependency on a ghost entity.]

.. _tu-cbatu-ghost_functions-16:

16. A ghost procedure shall not have a non-ghost output.

.. _etu-ghost_functions-vr:

.. centered:: **Examples**

.. code-block:: ada

   function A_Ghost_Expr_Function (Lo, Hi : Natural) return Natural is
     (if Lo > Integer'Last - Hi then Lo else ((Lo + Hi) / 2))
     with Pre        => Lo <= Hi,
          Post       => A_Ghost_Expr_Function'Result in Lo .. Hi,
          Convention => Ghost;

   function A_Ghost_Function (Lo, Hi : Natural) return Natural
     with Pre        => Lo <= Hi,
          Post       => A_Ghost_Function'Result in Lo .. Hi,
          Convention => Ghost;
   -- The body of the function is declared elsewhere.

   function A_Nonexecutable_Ghost_Function (Lo, Hi : Natural) return Natural
     with Pre        => Lo <= Hi,
          Post       => A_Nonexecutable_Ghost_Function'Result in Lo .. Hi,
          Convention => Ghost,
          Import;
   -- The body of the function is not declared elsewhere.
