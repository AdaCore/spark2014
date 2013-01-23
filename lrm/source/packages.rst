Packages
========

Package Specifications and Declarations
---------------------------------------

.. _abstract-state:

Abstraction of State
~~~~~~~~~~~~~~~~~~~~

The variables declared immediately within a package Q, its embedded
packages and its private descendants constitute the state of Q.

The variable declarations are only visible to clients of Q if they
are declared in the ``visible_part`` of Q.  The
declarations of all other variables are *hidden* from a client of Q.
Though the variables are hidden they still form part (or all) of the
state of Q and this hidden state cannot be ignored for static analyses
and proof.  *State abstraction* is the means by which this hidden state
is managed for static analyses and proof.

|SPARK| extends the concept of state abstraction to provide
hierarchical data abstraction whereby the hidden state of a package Q
may be refined over a tree of private descendants or embedded packages
of Q.  This provides data refinement similar to the refinement
available to types whereby a record may contain fields which are
themselves records.

State abstraction supports a logical model of volatility.  A *volatile*
state does not behave like a standard non-volatile one as its value
may change between two successive reads without an intervening update,
or successive updates may occur without any intervening reads and
appear to have no effect on the program.  Often volatile states
represent inputs or outputs to external devices or subsystems.

The abstract state aspect provides a way to designate a named abstract state as
being volatile, usually representing an external input or output.

.. _abstract-state-aspect:

Abstract State Aspect
~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Language feature:

    * This language feature provides an abstraction of the hidden state referenced by the package.

#. Needs to be met by language feature:

    * It shall be possible to provide an abstracted view of hidden state that can be referred to
      in specifications of program behaviour.
      *Rationale: this allows modular analysis, since modular is analysis performed
      before all package bodies are available and so before all hidden state is known.
      Abstraction also allows the management of complexity.*

#. Constraints:

   * It shall not be possible to include visible state in the statement of abstract state.
     *Rationale: visible state is already visible in the necessary contexts and by definition
     is not abstract.*

#. Consistency:

    * No further abstract state-specific requirements.

#. Semantics:

    * No further abstract state-specific requirements.

#. General requirements:

    * See also section :ref:`generic_hlrs`.


Language definition
^^^^^^^^^^^^^^^^^^^

State abstraction provides a mechanism for naming, in a package's
``visible_part``, state (typically variable declarations) that will be
declared within the package's body (or ``private_part``, or within private
descendants of the package). For example, a package declares a visible
procedure and we wish to specify the set of global variables that the
procedure reads and writes as part of the specification of the
subprogram. Those variables cannot be named directly in the package
specification. Instead, we introduce a state abstraction which is
visible in the package specification and later, when the package body
is declared, we specify the set of variables that *constitute* or
*implement* that state abstraction. If a package body contains, for
example, a nested package, then a state abstraction of the inner
package may also be part of the implementation of the given state
abstraction of the outer package.

The *hidden* state of a package may be represented
by one or more state abstractions, with each pair of state
abstractions representing disjoint sets of hidden variables.

If a subprogram P with a Global Aspect is declared in the
``visible_part`` of a package and P reads or updates any of the hidden
state of the package then P must include in its Global Aspect the
abstract state names with the correct mode that represent the hidden
state referenced by P.  If P has a Depends aspect then the abstract
state names must appear as inputs and outputs of P, as appropriate, in
the ``dependency_relation`` of the Depends aspect.

The Abstract State Aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is Abstract_State and the
``aspect_definition`` must follow the grammar of
``abstract_state_list`` given below.

.. centered:: **Syntax**

::

  abstract_state_list        ::= null
                               | state_name_with_properties
                               | (state_name_with_properties { , state_name_with_properties } )
  state_name_with_properties ::= state_name
                               | ( state_name with property_list )
  property_list              ::= property { , property }
  property                   ::= simple_property
                               | name_value_property
  simple_property            ::= identifier
  name_value_property        ::= identifier => expression
  state_name                 ::= defining_identifier

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 7.1.2 Syntax

.. centered:: **Legality Rules**

#. The ``identifier`` of a ``simple_property`` shall be Volatile,
   Input, or Output.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR identifier of simple_property shall be Volatile, Input or Output

#. There shall be at most one occurrence of the ``identifiers``
   Volatile, Input and Output in a single ``property_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR At most one occurrence of Volatile, Input and Output in single property_list

#. If a ``property_list`` includes Volatile, then it shall also
   include exactly one of Input or Output.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR If property_list includes Volatile, then it shall also include exactly one of Input or Output

#. If a ``property_list`` includes either Input or Output,
   then it shall also include Volatile.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR If property_list includes Input or Output, it shall also include Volatile

#. The ``identifier`` of a ``name_value_property`` shall be
   Integrity.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR name_value_property identified must be Integrity

#. If a ``property_list`` includes Integrity then it shall be the final
   property in the list. [This eliminates the possibility of a positional
   association following a named association in the property list.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR If property_list has Integrity it must be the final property in the list

#. A package_declaration or generic_package_declaration requires a completion
   [(a body)] if it contains an Abstract State aspect specification.

.. centered:: **Static Semantics**

#. The visible state and state abstractions of a package P consist of:

   * any variables declared immediately within the visible part
     of P; and
   * any state abstractions declared by the Abstract State aspect
     specification (if any) of package P; and
   * the visible state and state abstractions of any packages declared
     immediately within the visible part of P.

#. The hidden state of a package P consists of:

   * any variables declared immediately within the private part or
     body of P; and
   * the visible state and state abstractions of any packages declared
     immediately within the private part or body of P, and of any
     private child units of P or of their public descendants.

#. Each ``state_name`` occurring in an Abstract_State aspect
   specification for a given package P introduces an implicit
   declaration of a *state abstraction* entity. This implicit
   declaration occurs at the beginning of the visible part of P. This
   implicit declaration requires completion.

#. [A state abstraction shall only be named in contexts where this is
   explicitly permitted (e.g., as part of a Globals aspect
   specification), but this is not a name resolution rule.  Thus, the
   declaration of a state abstraction has the same visibility as any
   other declaration.
   A state abstraction is not an object; it does not have a type.  The
   completion of a state abstraction declared in a package
   aspect_specification can only be provided as part of a
   Refined_State aspect specification within the body of the package.]
   
#. A **null** ``abstract_state_list`` specifies that a package contains no 
   hidden state or variables declared in its ``visible_part``.
   [The specification is is checked when the package is analyzed.]

#. A *volatile* state abstraction is one declared with a property list
   which includes the Volatile property, and either Input or Output.

.. centered:: **Verification Rules**

There are no Verification Rules associated with the Abstract State aspect.
   
.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Abstract State
aspect.

.. centered:: **Examples**

.. code-block:: ada

   package Q
   with
      Abstract_State => State           -- Declaration of abstract state name State
   is                                   -- representing internal state of Q.
     function Is_Ready return Boolean   -- Function checking some property of the State.
        with Global => State;           -- State may be used in a global aspect.

        procedure Init                    -- Procedure to initialize the internal state of Q.
        with Global => (Output => State), -- State may be used in a global aspect.
	     Post   => Is_Ready;

        procedure Op_1 (V : Integer)    -- Another procedure providing some operation on State
           with Global => (In_Out => State),
  	        Pre    => Is_Ready,
	        Post   => Is_Ready;
   end Q;

   package X
      with  Abstract_State => (A, B, (C with Volatile, Input))
   is                          -- Three abstract state names are declared A, B & C.
                               -- A and B are non-volatile abstract states
      ...                      -- C is designated as a volatile input.
   end X;

   package Sensor -- simple volatile, input device driver
      with Abstract_State => (Port with Volatile, Input);
   is
      ...
   end Sensor;


Input, Output and Integrity Aspects **To be moved elsewhere?**
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

For variables which are declared directly within the visible part of a
package specification, the Volatile, Input, Output,
and Integrity aspects may be specified directly as part of the
variable's declaration.

.. centered:: **Legality Rules**

#. Input and Output are Boolean aspects, so have no
   ``aspect_definition`` part.
#. Integrity requires an ``aspect_definition`` which is a static
   expression of any integer type.
#. The Input, Output and Integrity aspects may only be applied to a
   variable declaration that appears in the visible part of a package
   specification.
#. If a variable has the Volatile aspect, then it must also have
   exactly one of the Input or Output aspects.

.. centered:: **Examples**

.. code-block:: ada

   package Raw_Input_Port
   is

      Sensor : Integer
         with Volatile,
              Input,
              Address => 16#DEADBEEF#,
              Integrity => 4;

   end Raw_Input_Port;

.. todo: Further semantic detail regarding Volatile state and integrity levels
         needs to be added.


Package-level Global, Depends and Initializes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**High-level detail TBD.**


Package Bodies
--------------

State Refinement
~~~~~~~~~~~~~~~~

A ``state_name`` declared by an Abstract State Aspect in the
specification of a package Q is an abstraction of the non-visible
*variables* declared in the private part, body, or private descendants
of Q, which together form the hidden state, of Q.  In the body of Q
each ``state_name`` has to be refined by showing which *variables* and
subordinate abstract states are represented by the ``state_name`` (its
constituents).  A Refined State Aspect in the body of Q is used
for this purpose.

In the body of a package the constituents of the refined
``state_name``, the refined view, has to be used rather than the
abstract view of the ``state_name``.  Refined global, depends, pre
and post aspects are provided to express the refined view.

In the refined view the constituents of each ``state_name`` have to be
initialized consistently with their appearance or omission from the
Package Depends or Initializes aspect of the package.


Refined State Aspect
~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Needs to be met by language feature:

   * For each state abstraction, it shall be possible to define the set of hidden
     state items that implement or *refine* that abstract state (where the
     hidden state items can either be concrete state or further state abstractions).
     *Rationale: the semantics of properties defined in terms of abstract state
     can only be precisely defined in terms of the corresponding concrete state,
     though nested abstraction is also necessary to manage hierarchies of data.
     Moreover, there may be multiple possible refinements for a given abstract specification
     and so the user should be able to specify what they actually want. This also
     supports stepwise development.*

#. Constraints:

   * Each item of hidden state must map to exactly one state abstraction.
     *Rationale: all hidden state must be covered since otherwise specifications referring to abstract state may
     be incomplete; that state must map to exactly one abstraction to give a clean and easily understandable
     abstraction, and for the purposes of simplicity of analysis.*

   * Each item of abstract state covered by the package shall be mapped to at least one
     item of hidden state (either concrete state or a further state abstraction).
     *Rationale: the semantics of properties defined in terms of abstract state
     can only be precisely defined in terms of the corresponding concrete state.*

#. Consistency:

   * No further Refined state-specific requirements needed.

#. Semantics:

   * No further Refined state-specific requirements needed.

#. General requirements:

    * See also section :ref:`generic_hlrs`.


.. todo:: The consistency rules will be updated as the
          models for volatile variables and integrity levels are defined.

.. todo: Consider whether it should be possible to refine null abstract state onto hidden state.
     *Rationale: this would allow the modelling of programs that - for example - use caches
     to improve performance.*

.. todo:: Consider whether it should be possible to refine abstract onto hidden state without any restrictions,
     although the refinement would be checked and potential issues flagged up to the user.
     *Rationale: there are a number of different possible models of mapping abstract
     to concrete state - especially when volatile state is being used - and it might
     be useful to provide greater flexibility to the user. In addition, if a facility is
     provided to allow users to step outside of the language when refining depends, for example, then it may be
     necessary to relax the abstraction model as well as relaxing the language feature
     of direct relevance.*


Language Definition
^^^^^^^^^^^^^^^^^^^

*To be completed in the Milestone 4 version of this document.*


Abstract State and Package Hierarchy
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: We need to consider the interactions between package hierarchy and abstract state.
   Do we need to have rules restricting access between parent and child packages?
   Can we ensure abstract state encapsulation? Target: D2.

Volatile Variables
~~~~~~~~~~~~~~~~~~

A volatile ``state_name`` may be refined to one or more subordinate
``state_names`` but ultimately a volatile ``state_name`` has to be
refined on to one or more volatile *variables*.  This variable has to
be volatile. The volatile *variable* will be declared in the body of a
package and the declaration will normally be denoted as volatile using
an aspect or a pragma.  Usually it will also have a representation
giving its address.

A volatile variable cannot be mentioned directly in a contract as the
reading of a volatile variable may affect the value of the variable
and for many I/O ports a read and a write affect different registers
of the external device.

.. todo:: Rather than have the current problems with external
   variables in functions should we disallow them in functions?
   Perhaps wait for a more general solution which allows non-pure
   functions in certain situations.

   We need to consider a way of providing features for reasoning about
   external variables different to the broken 'Tail scheme in SPARK 2005.
   This will require some form of attribute as we cannot mention
   volatile variables directly in a contract.

   If we want to reason about successive reads (writes) from a Volatile
   Input (Output) ``state_name`` we need to have a way to refer to
   these individual operations.

   At the very least, if V is a Volatile Input variable should not
   have the following assertion provable:

   T1 := V;
   T2 := V;

   pragma Assert (T1 = T2);

   Target: D2.

.. todo:: May introduce a way to provide a "history" parameter for
   Volatile variables. Target: D2.

.. todo:: Consider a mode selector for the "latched output" pattern - one that can be
   read after writing but need not be. This scheme has been
   requested by secunet.  In this scheme the output would be volatile
   but the input non-volatile. Target: rel2+.


Initialization Refinement
~~~~~~~~~~~~~~~~~~~~~~~~~

**High-level detail TBD.**


.. _refined-global-aspect:

Refined Global Aspect
~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Needs to be met by language feature:

   * Where a global data list referring to abstract state has been specified for a subprogram,
     it shall be possible to provide a refined global data list that takes account of the
     refinement of that abstract state.
     *Rationale: the semantics of properties defined in terms of abstract state
     can only be precisely defined in terms of the corresponding concrete state,
     though nested abstraction is also necessary to manage hierarchies of data.
     Moreover, there may be multiple possible refinements for a given abstract specification
     and so the user should be able to specify what they actually want. This also
     supports stepwise development.*

#. Constraints:

   * No further Refined Global-specific requirements needed.

#. Consistency: **Possibly combine rationale in one block; perhaps also take wording from 2005 LRM.**

   * Let *Abs* be the abstraction function defined by state refinement.
     Let *G* be the global data list and *RG* be the refined global data list. Then

     * Let *Y* be a data item in *G*. If every data item *X* in *RG*
       where *Abs (X) = Y* is such that its mode indicates it is only used in a proof
       context, then *Abs (X)* shall have the same mode in *G*. Otherwise:
       
       *Rationale: In general, modes should be preserved. However, if one refinement
       constituent of a state abstractionn has an input and/or output mode, then
       it is no longer of interest whether another constituent is only used in a
       proof context.*

     * The mode of *X* in *RG* must be a mode of *Abs (X)* in *G*.
       *Rationale: Modes should be preserved by refinement.*

     * If *mode X* is in *RG* but not all constituents of *Abs (X)* are in *RG*
       then *Abs (X)* must appear in *G* with at least input mode.
       *Rationale: In this case, Abs (X) is not fully initialized by the
       subprogram and the relevant components must be intialized prior to calling
       the subprogram.*

     * If *Y* appears in *G*, then at least one *X* such that *Abs (X) = Y*
       must appear in *RG*.
       *Rationale: By definition of abstraction.*
 

#. Semantics:

   * As per Global.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

.. todo: If it ends up being possible to refine null abstract state, then refinements of such
         state could appear in refined globals statements, though they would need
         to have mode in out.

Language Definition
^^^^^^^^^^^^^^^^^^^

*To be completed in the Milestone 4 version of this document.*


.. _refined-depends-aspect:

Refined Depends Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the visible part of a package may have a
Refined Depends aspect applied to its body or body stub. The
Refined Depends aspect defines the ``dependency_relation`` of the
subprogram in terms of the ``constituents`` of a ``state_name`` of the
package rather than the ``state_name``.

The Refined Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Depends" and the ``aspect_definition`` must follow
the grammar of ``dependency_relation``.

.. centered:: **Legality Rules**

#. A Refined Depends aspect may only appear on the body or body
   stub of a subprogram P in a package whose ``visible_part`` contains
   the declaration of a subprogram P.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. A Refined Depends aspect on the body or body stub of a
   subprogram P may only mention a formal parameter of P,
   ``constituents`` of a ``state_name`` of the enclosing package given
   in the Depends aspect in the declaration of P, a *global*
   item that is not a ``state_name`` of the enclosing package or a
   ``constituent`` of a **null** ``abstract_state_name``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**

#. A Refined Depends aspect of a subprogram defines a *refinement*
   of the Depends aspect of the subprogram.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. If the subprogram declaration declared in the visible part of
   package Q has a Depends aspect D then the
   Refined Depends aspect defines a *refinement* D' of D
   then it shall satisfy the following rules:

   * For each ``export`` in D which is not a ``state_name`` of Q,

     * the same item must appear as an ``export`` in D';
     * its ``dependency_list`` will be unchanged except that an
       ``import`` which is a ``state_name`` of Q will be replaced in
       D' by at least one ``constituent`` of the ``state_name`` and a
       ``constituent`` of a **null** , ``abstract_state_name`` may be
       an additional ``import``.

   * for each ``export`` in D which is a ``state_name`` S declared in
     Q,

     * the item is replaced in D' by at least one ``export`` which is a
       ``constituent`` of S,
     * its ``dependency_list`` will be unchanged except that an
       ``import`` which is a ``state_name`` of Q will be replaced in
       D' by at least one ``constituent`` of the ``state_name`` and a
       ``constituent`` of a **null** , ``abstract_state_name`` may be
       an additional ``import``.
     * the union of every ``import`` from the ``dependency_list`` of
       each ``export`` which is a ``constituent`` of S in D', with
       every ``import`` which is a ``constituent`` of a ``state_name``
       of Q replaced by its ``state_name`` (a ``constituent`` of a
       **null** ``abstract_state_name`` is ignored) should give the
       same set as the set of obtained by the union of every
       ``import`` in the ``dependency_list`` of S in D.

   * function may have a Refined Depends aspect D' which
     mentions a ``constituent`` of a **null** ``abstract_name`` but
     the constituent must appear as both an ``import`` and an
     ``export`` in D'.
   * A ``constituent`` of a **null** ``abstract_state_name`` is
     ignored in showing conformance between the Depends aspect
     and the Refined Depends aspect according to the rules
     given for a Depends aspect.

#. If a subprogram has a Refined Depends aspect which satisfies
   the flow analysis rules, it is used in the analysis of the
   subprogram body rather than its Depends aspect.

* If the declaration of a subprogram P in the visible part of package
  Q has a Depends aspect which mentions a ``state_name`` of Q,
  but P does not have a Refined Depends aspect then an implicit
  Refined Depends aspect will be synthesized from the body of P.`

* if the declaration of a subprogram P declared in the visible part of
  a package Q does not have a Depends aspect, an implicit one is
  synthesized from the Refined Depends aspect and the
  Refined State aspect (both of which which may also have been
  synthesized).

.. centered:: **Dynamic Semantics**

Abstractions do not have dynamic semantics.

Refined Precondition Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the visible part of a package may have a
Refined Precondition Aspect applied to its body or body stub.  The
Refined Precondition may be used to restate a precondition given on
the declaration of a subprogram in terms the full view of a private
type or the ``constituents`` of a refined ``state_name``.

The Refined Precondition Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Pre" and the ``aspect_definition`` must be
a Boolean ``expression``.

.. centered:: **Legality Rules**

#. A Refined Precondition may only appear on the body or body stub
   of a subprogram P in a package whose ``visible_part`` contains the
   declaration of P.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The same legality rules apply to a Refined Precondition as for
   a precondition.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**

#. A Refined Precondition of a subprogram defines a *refinement*
   of the precondition of the subprogram.
#. Logically, the precondition of a subprogram must imply its
   Refined Precondition which in turn means that this relation
   cannot be achieved with a default precondition (True) and therefore
   a subprogram with a Refined Precondition will require a
   precondition also in order to perform proofs.
#. The static semantics are otherwise as for a precondition.


.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

#. The precondition of a subprogram declaration shall imply the the
   Refined Precondition

.. centered:: **Dynamic Semantics**

#. When a subprogram with a Refined Precondition is called; first
   the precondition is evaluated as defined in the Ada RM.  If the
   precondition evaluates to True, then the Refined Precondition
   is evaluated.  If either precondition or Refined Precondition
   do not evaluate to True an exception is raised.

Refined Postcondition Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~~~~


A subprogram declared in the visible part of a package may have a
Refined Postcondition Aspect applied to its body or body stub.  The
Refined Postcondition may be used to restate a postcondition given
on the declaration of a subprogram in terms the full view of a private
type or the ``constituents`` of a refined ``state_name``.

The Refined Precondition Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Post" and the ``aspect_definition`` must be
a Boolean ``expression``.

.. centered:: **Legality Rules**

#. A Refined Postcondition may only appear on the body or body stub
   of a subprogram P in a package whose ``visible_part`` contains the
   declaration of P.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The same legality rules apply to a Refined Postcondition as for
   a postcondition.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**

#. A Refined Postcondition of a subprogram defines a *refinement*
   of the postcondition of the subprogram.
#. Logically, the Refined Postcondition of a subprogram must imply
   its postcondition.  This means that it is perfectly logical for the
   declaration not to have a postcondition (which in its absence
   defaults to True) but for the body or body stub to have a
   Refined Postcondition.
#. The static semantics are otherwise as for a postcondition.


.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

#. The precondition of a subprogram declaration with the
   Refined Precondition of its body or body stub and its
   Refined Postcondition together imply the postcondition of the
   declaration, that is:

   ::
     (Precondition and Refined Precondition and Refined Postcondition) -> Postcondition


.. centered:: **Dynamic Semantics**

#. When a subprogram with a Refined Postcondition is called; first
   the subprogram is evaluated.  If it terminates without exception
   the Refined Postcondition is evaluated.  If this evaluates to
   True then the postcondition is evaluated as described in the Ada
   RM.  If either the Refined Postcondition or the postcondition
   do not evaluate to True an exception is raised.

.. todo:: refined contract_cases. Target: D2.


Private Types and Private Extensions
------------------------------------

.. centered:: **Extended Static Semantics**

#. The partial view of a private type or private extension may be in
   |SPARK| even if its full view is not in |SPARK|. The usual rule
   applies here, so a private type without discriminants is in
   |SPARK|, while a private type with discriminants is in |SPARK| only
   if its discriminants are in |SPARK|.

Private Operations
~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Type Invariants
~~~~~~~~~~~~~~~

.. centered:: **Extended Dynamic Semantics**

#. The Ada 2012 RM lists places at which an invariant check is performed. In
   |SPARK|, we add the following places:

   * Before a call on any subprogram or entry that:

     * is explicitly declared within the immediate scope of type T (or
       by an instance of a generic unit, and the generic is declared
       within the immediate scope of type T), and

     * is visible outside the immediate scope of type T or overrides
       an operation that is visible outside the immediate scope of T,
       and

     * has one or more in out or in parameters with a part of type T.

     the check is performed on each such part of type T.

Deferred Constants
------------------

.. todo:: Need to consider here allowing a Global Aspect on a deferred
   constant declaration to indicate the variables from which the
   value is derived.  Will be needed if the completion is not in |SPARK|, for instance.
   Target: D2.

Limited Types
-------------

No extensions or restrictions.

Assignment and Finalization
---------------------------

Controlled types are not permitted in |SPARK|.
