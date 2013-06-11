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
global variable or a state abstraction (see :ref:`abstract-state`). Global items
are presented in Global aspects (see :ref:`global-aspects`).

An *entire object* is an object which is not a subcomponent of a larger
containing object.  More specifically, an *entire object* is
an object declared by an ``object_declaration`` (as opposed to, for example,
a slice or the result object of a function call) or a formal parameter of
a subprogram.

.. centered:: **Static Semantics**

#. The *exit* value of a global item or parameter of a subprogram is its
   value immediately following the successful call of the subprogram.

#. The *entry* value of a global item or parameter of a subprogram is its
   value at the call of the subprogram.

#. An *output* of a subprogram is a global item or parameter whose final
   value may be updated by a call to the subprogram.  The result of a function
   is also an output.

#. An *input* of a subprogram is a global item or parameter whose initial
   value may be used in determining the exit value of an output of the
   subprogram. As a special case, a global item or parameter is also an input if
   it is mentioned in a ``null_dependency_clause`` in the Depends
   aspect of the subprogram (see :ref:`depends-aspects`).

.. centered:: **Verification Rules**

#. A function declaration shall not have a ``parameter_specification``
   with a mode of **out** or **in out**. This rule also applies to
   a ``subprogram_body`` for a function for which no explicit declaration
   is given.

Preconditions and Postconditions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As indicated by the ``aspect_specification`` being part of a
``subprogram_declaration``, a subprogram is in |SPARK| only if its specific
contract expressions (introduced by Pre and Post), if any, are in |SPARK|.

For an ``expression_function_declaration``, F, without an explicit
Postcondition, the expression, E, implementing the function acts as its
Postcondition, that is the default postcondition is F'Result = E.

In general the expression, E,  of a postcondition of a function may be used as
the expression of an ``expression_function_declaration`` instead making E both
the implementation of the function and the expression of its [default]
postcondition.

Subprogram Contracts
~~~~~~~~~~~~~~~~~~~~

In order to extend Ada's support for specification of subprogram contracts
(e.g., the Pre and Post) by providing more precise and/or concise contracts, the
|SPARK| aspects, Global, Depends, and Contract_Cases are defined.

.. centered:: **Legality Rules**

#. The Global, Depends and Contract_Cases aspects may be
   specified for a subprogram with an ``aspect_specification``.  More
   specifically, these aspects are allowed in the same
   contexts as a Pre or Post aspect.

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
                   and then Exactly_One_Of(A1,A2...An),
         Post => General_Postcondition
                   and then (if A1'Old then B1)
                   and then (if A2'Old then B2)
                   and then ...
                   and then (if An'Old then Bn);


where

  A1 .. An are Boolean expressions involving the entry values of
  formal parameters and global variables and

  B1 .. Bn are Boolean expressions that may also use the exit values of
  formal parameters, global variables and results.

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

#. A Contract_Cases aspect may have at most one **others**
   ``contract_case`` and if it exists it must be the last one in the
   ``contract_case_list``.
#. A ``consequence`` expression is considered to be a postcondition
   expression for purposes of determining the legality of Old or
   Result ``attribute_references``.

.. centered:: **Static Semantics**

#. A Contract_Cases aspect is an assertion (as defined in RM
   11.4.2(1.1/3)); its assertion expressions are as described
   below. Contract_Cases may be specified as an
   ``assertion_aspect_mark`` in an Assertion_Policy pragma.

.. centered:: **Dynamic Semantics**

#. Upon a call of a subprogram or entry which is subject to an enabled
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
     every ``condition``\ 's evaluation yielded False).  A check
     is performed that the evaluation of the selected ``consequence``
     evaluates to True; Assertions.Assertion_Error is raised if this
     check fails.

.. centered:: **Verification Rules**

#. Each ``condition`` in a Contract_Cases aspect has to be proven to
   be mutually exclusive, that is only one ``condition`` can be
   True with any set of inputs conformant with the formal parameters
   and satisfying the specific precondition.
#. At the point of call a check that a single ``condition`` of the
   Contract_Cases aspect is True has to be proven, or if no
   ``condition`` is True then the Contract_Cases aspect must have an
   **others** ``contract_case``.
#. For every ``contract_case``, when its ``condition`` is True, or the
   **others** ``contract_case`` when none of the conditions are True,
   the implementation of the body of the subprogram must be proven to
   satisfy the ``consequence`` of the ``contract_case``.

.. note:: (TJJ 29/11/12) Do we need this verification rule?  Could it
   be captured as part of the general statement about proof?

.. _global-aspects:

Global Aspect
~~~~~~~~~~~~~

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

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 6.1.4 Syntax

.. centered:: **Static Semantics**

#. A ``global_specification`` that is a ``global_list`` is shorthand for a
   ``moded_global_list`` with the ``mode_selector`` Input.

#. A ``global_item`` is *referenced* by a subprogram if:

   * It denotes an input or an output of the subprogram, or;

   * Its entry value is used to determine the value of an assertion
     expression within the subprogram, or;

   * Its entry value is used to determine the value of an assertion
     expression within another subprogram that is called either directly or
     indirectly by this subprogram.

#. A ``null_global_specification`` indicates that the subprogram does not
   reference any ``global_item`` directly or indirectly.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.4 SS no global_item referenced when null_global_specification

.. centered:: **Name Resolution Rules**

#. A ``global_item`` shall denote an entire object [which must be a variable] or
   a state abstraction.
   [This is a name resolution rule because a ``global_item`` can unambiguously
   denote a state abstraction even if a function having the same fully qualified
   name is also present].

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: NRR global_item shall denote entire object

.. centered:: **Legality Rules**

#. The Global aspect may only be specified for the initial declaration of a
   subprogram (which may be a declaration, a body or a body stub).

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.4 LR

#. A ``global_item`` shall not denote a state abstraction whose refinement
   is visible [(a state abstraction cannot be named within its enclosing
   package's body other than in its refinement)].

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.4 LR global_item shall not denote state abstraction with visible refinement

#. Each ``mode_selector`` shall occur at most once in a single
   Global aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.4 LR Each mode_selector shall occur at most once

#. A function subprogram shall not have a ``mode_selector`` of
   Output or In_Out in its Global aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.4 LR functions cannot have Output or In_Out as mode_selector

#. The ``global_items`` in a single Global aspect specification shall denote
   distinct entities.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.4 LR global_items shall denote distinct entities

#. A ``global_item`` occurring in a Global aspect specification of a subprogram
   shall not denote a formal parameter of the subprogram.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.4 LR global_item shall not denote formal parameter

#. If a subprogram is nested within another and if the ``global_specification``
   of the outer subprogram has an entity denoted by a ``global_item`` with a
   ``mode_specification`` of Input, then a ``global_item`` of the
   ``global_specification`` of the inner subprogram shall not denote the same
   entity with a ``mode_selector`` of In_Out or Output.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.4 LR nested subprograms cannot have mode_specification
                   of In_Out or Output if enclosing subprogram's mode_specification
                   is Input

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Global aspect.

.. centered:: **Verification Rules**

#. A ``global_item`` shall occur in a Global aspect of a
   subprogram if and only if it denotes an entity that is referenced by the
   subprogram.

#. Each entity denoted by a ``global_item`` in a ``global_specification`` of a
   subprogram that is an input or output of the subprogram shall satisfy the
   following mode specification rules [which are checked during analysis of the
   subprogram body]:

   * a ``global_item`` that denotes an input but not an output
     has a ``mode_selector`` of Input;

   * a ``global_item`` that denotes an output but not an input and is always
     fully initialized as a result of any successful execution of a call of the
     subprogram has a ``mode_selector`` of Output;

   * otherwise the ``global_item`` denotes both an input and an output, is
     has a ``mode_selector`` of In_Out.

For purposes of determining whether an output of a subprogram shall have a
``mode_selector`` of Output or In_Out, reads of array bounds, discriminants,
or tags of any part of the output are ignored. Similarly, for purposes of
determining whether an entity is "fully initialized as a result of any
successful execution of the call", only nondiscriminant parts are considered.
[This implies that given an output of a discriminated type that is not known
to be constrained ("known to be constrained" is defined in Ada RM 3.3),
the discriminants of the output might or might not be updated by the call.]

#. An entity that is denoted by a ``global_item`` which is referenced by a
   subprogram but is neither an input nor an output but is only referenced
   directly, or indirectly in assertion expressions has a ``mode_selector`` of
   Proof_In.

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

Depends Aspect
~~~~~~~~~~~~~~

A Depends aspect defines a *dependency relation* for a
subprogram which may be given in the ``aspect_specification`` of the
subprogram.  The dependency relation is used in information flow
analysis.

A Depends aspect for a subprogram specifies for each output every input on
which it depends. The meaning of *X depends on Y* in this context is that the
exit value of output, X, on the completion of the subprogram is at least partly
determined from the entry value of input, *Y* and is written *X => Y*. As in
UML, the entity at the tail of the arrow depends on the entity at the head of
the arrow.

If an output does not depend on any input this is indicated
using a **null**, e.g., *X =>* **null**.  An output may be
self-dependent but not dependent on any other input.  The shorthand
notation denoting self-dependence is useful here, X =>+ **null**.

The functional behavior of a subprogram is not specified by the Depends
aspect but, unlike a postcondition, the Depends aspect has
to be complete in the sense that every input and output of the subprogram must
appear in the Depends aspect.

The Depends aspect may only be specified for the initial declaration of a
subprogram (which may be a declaration, a body or a body stub).
The implementation of a subprogram body must be consistent with the
subprogram's Depends Aspect.

Note that a Refined_Depends aspect may be applied to a subprogram body when
using state abstraction; see section :ref:`refined-depends-aspect` for further
details.

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

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 6.1.5 Syntax

.. centered:: **Name Resolution Rules**

#. An ``input`` or ``output`` of a ``dependency_relation`` shall denote only
   an entire variable or a state abstraction. [This is a name resolution rule
   because an ``input`` or ``output`` can unambiguously denote a state
   abstraction even if a function having the same fully qualified name is also
   present.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 NRR input or outputs of a dependency_relation shall denote
                   entire variable or state abstraction

.. centered:: **Legality Rules**

#. The Depends aspect shall only be specified for the initial declaration of a
   subprogram (which may be a declaration, a body or a body stub).

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Depends aspect shall be on subprogram's declaration

#. An ``input`` or ``output`` of a ``dependency_relation`` shall not denote a
   state abstraction whose refinement is visible [a state abstraction cannot be
   named within its enclosing package's body other than in its refinement].

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR dependency_relation shall not denote a state
                   abstraction with visible refinement

#. The *explicit input set* of a subprogram is the set of formal parameters of
   the subprogram of mode **in** and **in out** along with the entities denoted
   by ``global_items`` of the Global aspect of the subprogram with a
   ``mode_selector`` of Input and In_Out.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR The input set consists of formal parameters of mode "in"
                   and "in out" and global_items with mode_selector Input or In_Out

#. The *input set* of a subprogram is the *explicit input set* of the
   subprogram augmented with those formal parameters of mode **out**
   having discriminants, array bounds, or a tag which can be read and
   whose values are not implied by the subtype of the parameter.
   More specifically, it includes formal parameters of mode **out** which are
   of an unconstrained array subtype, an unconstrained discriminated subtype,
   a tagged type, or a type having a subcomponent of an unconstrained
   discriminated subtype. [Tagged types are mentioned in this rule in
   anticipation of a later version of |SPARK| in which the current
   restriction on uses of the 'Class attribute is relaxed; currently
   there is no way to read or otherwise depend on the underlying tag of an
   **out** mode formal parameter of a tagged type.]

#. The *output set* of a subprogram is the set of formal parameters of the
   subprogram of mode **in out** and **out** along with the entities denoted by
   ``global_items`` of the Global aspect of the subprogram with a
   ``mode_selector`` of In_Out and Output and (for a function) the
   ``function_result``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR The output set consists of formal parameters of mode "out"
                   and "in out" and global_item with mode_selector Output or In_Out
                   and for a function the function_result

#. The entity denoted by each ``input`` of a ``dependency_relation`` of a
   subprogram shall be a member of the input set of the subprogram.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Entity denoted by input shall be member of input set

#. Every member of the explicit input set of a subprogram shall be denoted by
   at least one ``input`` of the ``dependency_relation`` of the subprogram.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Every member of the input set shall be denoted by
                   at least one input of the dependency_relation

#. The entity denoted by each ``output`` of a ``dependency_relation`` of a
   subprogram shall be a member of the output set of the subprogram.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Entity denoted by output shall be member of output set

#. Every member of the output set of a subprogram shall be denoted by exactly
   one ``output`` in the ``dependency_relation`` of the subprogram.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Every member of the output set shall be denoted by
                   at least one output of the dependency_relation

#. For the purposes of determining the legality of a Result
   ``attribute_reference``, a ``dependency_relation`` is considered to be
   a postcondition of the function to which the enclosing
   ``aspect_specification`` applies.


#. In a ``dependency_relation`` there can be at most one ``dependency_clause``
   which is a ``null_dependency_clause`` and if it exists it must be the
   last ``dependency_clause`` in the ``dependency_relation``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR null_dependency_clause shall be the last
                   dependency_clause in the dependency_relation

#. An entity denoted by an ``input`` which is in an ``input_list`` of a
   **null** ``output_list`` shall not be denoted by an ``input`` in another
   ``input_list`` of the same ``dependency_relation``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR an input of a null output_list shall not appear
                   as an input in another input_list

#. The ``inputs`` in a single ``input_list`` shall denote distinct entities.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR input entities shall be distinct entities

#. A ``null_dependency_clause`` shall not have an ``input_list`` of **null**.


   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR null_dependency_clause shall not have input_list
                   of null

.. centered:: **Static Semantics**

#. A ``dependency_clause`` with a "+" symbol in the syntax ``output_list`` =>+
   ``input_list`` means that each ``output`` in the ``output_list`` has a
   *self-dependency*, that is, it is dependent on itself.
   [The text (A, B, C) =>+ Z is shorthand for
   (A => (A, Z), B => (B, Z), C => (C, Z)).]

#. A ``dependency_clause`` of the form A =>+ A has the same meaning as A => A.
   [The reason for this rule is to allow the short hand:
   ((A, B) =>+ (A, C)) which is equivalent to (A => (A, C), B => (A, B, C)).]

#. A ``dependency_clause`` with a **null** ``input_list`` means that the final
   value of the entity denoted by each ``output`` in the ``output_list`` does
   not depend on any member of the input set of the subrogram
   (other than itself, if the ``output_list`` =>+ **null** self-dependency
   syntax is used).

#. The ``inputs`` in the ``input_list`` of a ``null_dependency_clause`` may be
   read by the subprogram but play no role in determining the values of any
   outputs of the subprogram.

#. A Depends aspect of a subprogram with a **null** ``dependency_relation``
   indicates that the subprogram has no ``inputs`` or ``outputs``.
   [From an information flow analysis viewpoint it is a
   null operation (a no-op).]

#. [A function without an explicit Depends aspect specification
   is assumed to have the ``dependency_relation``
   that its result is dependent on all of its inputs.
   Generally an explicit Depends aspect is not required for functions.]

#. [A subprogram which has an explicit Depends aspect specification
   and lacks an explicit Global aspect specification is assumed to have
   the [unique] Global aspect specification that is consistent with the
   subprogram's Depends aspect.]

#. [A subprogram which has an explicit Global aspect specification
   but lacks an explicit Depends aspect specification and, as yet, has no
   implementation of its body is assumed to have the conservative
   ``dependency_relation`` that each member of the output set is dependent on
   every member of the input set.]

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Depends aspect
as it is used purely for static analysis purposes and is not executed.

.. centered:: **Verification Rules**

#. Each entity denoted by an ``output`` given in the Depends aspect of a
   subprogram must be an output in the implementation of the subprogram body and
   the output must depend on all, but only, the entities denoted by the
   ``inputs`` given in the ``input_list`` associated with the ``output``.

#. Each output of the implementation of the subprogram body is denoted by
   an ``output`` in the Depends aspect of the subprogram.

#. Each input of the implementation of a subprogram body is denoted by an
   ``input`` of the Depends aspect of the subprogram.

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


Ghost Functions
~~~~~~~~~~~~~~~

Ghost functions are intended for use in discharging proof obligations and in
making it easier to express assertions about a program. The essential property
of ghost functions is that they have no effect on the dynamic behavior of a
valid SPARK program other than, depending on the assertion policy, the execution
of known to be true assertion expressions. More specifically, if one were to
take a valid SPARK program and remove all ghost function declarations from it
and all assertions containing references to those functions, then the resulting
program might no longer be a valid SPARK program (e.g., it might no longer be
possible to discharge all the program's proof obligations) but its dynamic
semantics (when viewed as an Ada program) should be unaffected by this
transformation other than evaluating fewer known to be true assertion
expressions.

The rules below are in given in general terms in relation to "ghost entities"
since in future it is intended that ghost types and ghost variables
will be allowed. Currently, however, only ghost functions are allowed
and so an additional legality rule is provided that allows only
functions to be explicitly declared as a ghost (though entities declared within
a ghost function are regarded implicitly as ghost entities). When the full scope of ghost
entities is allowed, the rules given in this section may be moved to
other sections as appropriate, since they will refer to more than just subprograms.

.. todo:: Add ghost types and ghost variables to SPARK 2014.

.. centered:: **Static Semantics**

|SPARK| defines the ``convention_identifier`` Ghost.
An entity (e.g., a subprogram or an object) whose Convention aspect
is specified to have the value Ghost is said to be a ghost
entity (e.g., a ghost function or a ghost variable).

The Convention aspect of an entity declared inside of a ghost entity (e.g.,
within the body of a ghost function) is defined to be Ghost.

The Link_Name aspect of an imported ghost entity is defined
to be a name that cannot be resolved in the external environment.

.. centered:: **Legality Rules**

Only functions can be explicitly declared with the Convention aspect Ghost.
[This means that the scope of the following rules is restricted to functions, even
though they are stated in more general terms.]

A ghost entity shall only be referenced:

- from within an assertion expression; or
- within or as part of the declaration or completion of a
  ghost entity (e.g., from within the body of a ghost function); or
- within a statement which does not contain (and is not itself) either an
  assignment statement targeting a non-ghost variable or
  a procedure call which passes a non-ghost variable as an
  out or in out mode actual parameter.

Within a ghost procedure, the view of any non-ghost variable is
a constant view. Within a ghost procedure, a volatile non-global
object shall not be read. [In a ghost procedure we do not want to
allow assignments to non-ghosts either via assignment statements or
procedure calls.]

A ghost entity shall not be referenced from
within the expression of a predicate specification of a non-ghost
subtype [because such predicates participate in determining
the outcome of a membership test].

All subcomponents of a ghost object shall be initialized by the
elaboration of the declaration of the object.

.. todo::
   Make worst-case assumptions about private types for this rule,
   or blast through privacy?

A ghost instantiation shall not be an instantiation of a non-ghost
generic package. [This is a conservative rule until we have more precise rules
about the side effects of elaborating an instance of a generic package.
We will need the general rule that the elaboration of a
ghost declaration of any kind cannot modify non-ghost state.]

The Link_Name or External_Name aspects of an imported ghost
entity shall not be specified. A Convention aspect specification
for an entity declared inside of a ghost entity shall be confirming
[(in other words, the specified Convention shall be Ghost)].

Ghost tagged types are disallowed. [This is because just the existence
of a ghost tagged type (even if it is never referenced) changes the
behavior of Ada.Tags operations. Note overriding is not a problem because
Convention participates in
conformance checks (so ghost can't override non-ghost and vice versa).]

The Convention aspect of an External entity shall not be Ghost.

[We are ignoring interactions between ghostliness and freezing.
Adding a ghost variable, for example, could change the freezing point
of a non-ghost type. It appears that this is ok; that is, this does
not violate the ghosts-have-no-effect-on-program-behavior rule.]

.. todo::
   Can a ghost variable be a constituent of a non-ghost state
   abstraction, or would this somehow allow unwanted dependencies?
   If not, then we presumably need to allow ghost state abstractions
   or else it would illegal for a library level package body to
   declare a ghost variable.

.. todo::
   Do we want an implicit Ghost convention for an entity declared
   within a statement whose execution depends on a ghost value?

.. code-block:: ada

  if My_Ghost_Counter > 0 then
     declare
        X : Integer; -- implicitly Ghost?

.. centered:: **Dynamic Semantics**

The effects of specifying a convention of Ghost
on the runtime representation, calling conventions, and other such
dynamic properties of an entity are the same as if a convention of
Ada had been specified.

[If it is intended that a ghost entity should not have any runtime
representation (e.g., if the entity is used only in discharging proof
obligations and is not referenced (directly or indirectly) in any
enabled (e.g., via an Assertion_Policy pragma) assertions),
then the Import aspect of the entity may be specified to be True.]

.. centered:: **Verification Rules**

A non-ghost output shall not depend on a ghost input.

A ghost entity shall not be referenced

- within a call to a procedure which has a non-ghost output; or

- within a control flow expression (e.g., the condition of an
  if statement, the selecting expression of a case statement, the
  bounds of a for loop) of a compound statement which contains
  such a procedure call. [The case of a non-ghost-updating
  assignment statement is handled by a legality rule; this rule is
  needed to prevent a call to a procedure which updates a
  non-ghost via an up-level reference, as opposed to updating a parameter.]

[This rule is intended to ensure an update of a non-ghost entity shall not have a
control flow dependency on a ghost entity.]

A ghost procedure shall not have a non-ghost output.

   .. centered:: **Examples**

.. code-block:: ada

   function A_Ghost_Expr_Function (Lo, Hi : Natural) return Natural is
      (if Lo > Integer'Last - Hi then Lo else ((Lo + Hi) / 2))
      with Pre        => Lo <= Hi,
           Post       => A_Ghost_Function'Result in Lo .. Hi,
           Convention => Ghost;

   function A_Ghost_Function (Lo, Hi : Natural) return Natural
      with Pre        => Lo <= Hi,
           Post       => A_Ghost_Function'Result in Lo .. Hi,
           Convention => Ghost;
   -- The body of the function is declared elsewhere.

   function A_Nonexecutable_Ghost_Function (Lo, Hi : Natural) return Natural
      with Pre        => Lo <= Hi,
           Post       => A_Ghost_Function'Result in Lo .. Hi,
           Convention => Ghost,
           Import;
   -- The body of the function is not declared elsewhere.


Formal Parameter Modes
----------------------

No extensions or restrictions.

.. todo::
   The modes of a subprogram in Ada are not as strict as S2005 and there
   is a difference in interpretation of the modes as viewed by flow analysis.
   For instance in Ada a formal parameter of mode out of a composite type need
   only be partially updated, but in flow analysis this would have mode in out.
   Similarly an Ada formal parameter may have mode in out but not be an input.
   In flow analysis it would be regarded as an input and give rise to
   flow errors.

   In deciding whether a parameter is only partially updated, discriminants
   (including discriminants of subcomponents) are ignored. For example,
   given an *out* mode parameter of a type with defaulted discriminants,
   a subprogram might or might not modify those discriminants (if it does,
   there will of course be an associated proof obligation to show that the
   parameter's 'Constrained attribute is False in that path).

   Perhaps we need an aspect to describe the strict view of a parameter
   if it is different from the specified Ada mode of the formal parameter?
   To be completed in the Milestone 3 version of this document.


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

A call is in |SPARK| only if it resolves statically to a subprogram whose
declaration view is in |SPARK| (whether the call is dispatching or not).

Parameter Associations
~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Anti-Aliasing
~~~~~~~~~~~~~

An alias is a name which refers to the same object as another name.
The presence of aliasing is inconsistent with the underlying flow
analysis and proof models used by the tools which assume that
different names represent different entities.  In general, it is not
possible or is difficult to deduce that two names refer to the same
object and problems arise when one of the names is used to update the
object.

A common place for aliasing to be introduced is through the actual
parameters and between actual parameters and
global variables in a procedure call.  Extra verification rules are
given that avoid the possibility of aliasing through actual
parameters and global variables.  A function is not allowed to have
side-effects and cannot update an actual parameter or global
variable.  Therefore, function calls cannot introduce aliasing and
are excluded from the anti-aliasing rules given below for procedure
calls.

.. centered:: **Syntax**

No extra syntax is associated with anti-aliasing.

.. centered:: **Legality Rules**

No extra legality rules are associated with anti-aliasing.

.. centered:: **Static Semantics**

#. Objects are assumed to have overlapping locations if it cannot be established
   statically that they do not. [This definition of overlapping is necessary since
   these anti-aliasing checks will initially be implemented by flow analysis;
   in a future tool release it is intended that these checks will be implemented by
   the proof engine and so the static checking may be suppressed.]

.. centered:: **Dynamic Semantics**

No extra dynamic semantics are associated with anti-aliasing.

   .. centered:: **Verification Rules**

#. In |SPARK|, a procedure call shall not pass actual parameters
   which denote objects with overlapping locations, when at least one of
   the corresponding formal parameters is of mode **out** or **in out**,
   unless the other corresponding formal parameter is of mode **in**
   and is of a by-copy type.

#. In |SPARK|, a procedure call shall not pass an actual parameter, whose
   corresponding formal parameter is mode **out** or **in out**,
   that denotes an object which overlaps with any ``global_item`` referenced
   by the subprogram.

#. In |SPARK|, a procedure call shall not pass an actual parameter which
   denotes an object which overlaps a ``global_item`` of mode
   **out** or **in out** of the subprogram, unless the corresponding formal
   parameter is of mode **in** and by-copy.

#. Where one of these rules prohibits the occurrence of an object V or any of its subcomponents
   as an actual parameter, the following constructs are also prohibited in this context:

   * A type conversion whose operand is a prohibited construct;

   * A call to an instance of Unchecked_Conversion whose operand is a prohibited construct;

   * A qualified expression whose operand is a prohibited construct;

   * A prohibited construct enclosed in parentheses.


Return Statements
-----------------

Use of ``extended_return_statement`` is not allowed in |SPARK|.

.. todo:: Update LRM to allow extended return statements in a future release.


Nonreturning Procedures
~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Syntax**

There is no additional syntax associated with nonreturning procedures in |SPARK|.

.. centered:: **Legality Rules**

#. For a call to a nonreturning procedure to be in |SPARK|, it must be immediately
   enclosed by an if statement which encloses no other statement.

.. centered:: **Static Semantics**

There are no additional static semantics associated with nonreturning procedures in |SPARK|.

.. centered:: **Dynamic Semantics**

There are no additional dynamic semantics associated with nonreturning procedures in |SPARK|.

.. centered:: **Verification Rules**

#. A call to a nonreturning procedure introduces an obligation to prove that the statement
   will not be executed, much like the proof obligation associated with

       ``pragma Assert (False);``

   [In other words, the proof obligations introduced for a call to a nonreturning procedure
   are the same as those introduced for a runtime check which fails
   unconditionally. See also section :ref:`exceptions`, where a similar restriction is
   imposed on ``raise_statements``.]
   
#. The body of a non-returning procedure should not be subjected to formal verification or
   flow analysis.

Overloading of Operators
------------------------

No extensions or restrictions.

Null Procedures
---------------

No extensions or restrictions.


Expression Functions
--------------------

Contract_Cases, Global and Depends aspects may be applied to an expression
function as for any other function declaration if it does not have a separate
declaration.  If it has a separate declaration then the aspects are applied to
that.  It may have refined aspects applied (see :ref:`state_refinement`).
