Packages
========

.. centered:: **Verification Rules**

.. _tu-fa-packages-01:

1. In |SPARK| the elaboration of a package shall only update, directly or
   indirectly, variables declared immediately within the package.

.. _etu-packages:

Package Specifications and Declarations
---------------------------------------

.. _abstract-state:

Abstraction of State
~~~~~~~~~~~~~~~~~~~~

The variables declared within a package but not within a subprogram body or
block which does not also enclose the given package constitute the *persistent
state* of the package. A package's persistent state is divided into *visible
state* and *hidden state*. If a declaration that is part of a package's
persistent state is visible outside of the package, then it is a constituent of
the package's visible state; otherwise it is a constituent of the package's
hidden state.

Though the variables may be hidden they still form part (or all) of
the persistent state of the package and the hidden state cannot be
ignored.  *State abstraction* is the means by which this hidden state
is represented and managed. A state abstraction represents one or more
declarations which are part of the hidden state of a package.

|SPARK| extends the concept of state abstraction to provide hierarchical data
abstraction whereby the state abstraction declared in a package may contain the
persistent state of other packages given certain restrictions described in
:ref:`package_hierarchy`. This provides data refinement similar to the
refinement available to types whereby a record may contain fields which are
themselves records.

.. centered:: **Static Semantics**

.. _tu-abstract_state-01:

1. The visible state of a package P consists of:

   * any variables declared immediately within the visible part of
     package P; and

   * the state abstractions declared by the Abstract_State aspect specification
     (if any) of package P; and

   * the visible state of any packages declared immediately within the visible part
     of package P.


2. The hidden state of a package P consists of:

   * any variables or constants *with variable inputs* declared immediately
     in the private part or body of P; and

   * the visible state of any packages declared immediately within
     the private part or body of P.

.. _etu-abstract_state:

.. _external_state:

External State
~~~~~~~~~~~~~~

External state is a state abstraction or variable representing something
external to a program. For instance, an input or output device, or a
communication channel to another subsystem such as another |SPARK| program.

Updating external state might have some external effect. It could be writing
a value to be read by some external device or subsystem which then has a
potential effect on that device or subsystem. Similarly the value read from an
external state might depend on a value provided by some external device or
subsystem.

Ada uses the terms external readers and writers to describe entities external to
a program which interact with the program through reading and writing data. Of
particular concern to |SPARK| are external readers and writers which are not
strictly under control of the program. It is not known precisely when a value
will be written or read by an external reader or writer. These are called
*asynchronous readers* and *asynchronous writers* in |SPARK|.

Each read or update of an external state may be significant for
instance reading or writing a stream of characters to a file or,
individual reads or writes may not be significant, for instance
reading a temperature from a device or writing the same value to a
lamp driver or display. |SPARK| provides a mechanism to indicate
whether a read or write is always significant.

A type is said to be *effectively volatile* if it is either
a volatile type, an array type whose Volatile_Component
aspect is True, or an array type whose component type is
effectively volatile. An *effectively volatile object* is a
volatile object or is of an effectively volatile type.

External state is an effectively volatile object or a state abstraction which
represents one or more effectively volatile objects (or it could be a null state
abstraction; see :ref:`abstract-state-aspect`).

Four Boolean valued *properties* of external states that may be specified are
defined:

  * Async_Readers - A component of the system external to the program might
    read/consume a value written to an external state.

  * Async_Writers - A component of the system external to the program might
    update the value of an external state.

  * Effective_Writes - every update of the external state is significant.

  * Effective_Reads - every read of the external state is significant.

These properties may be specified for an effectively volatile object
as Boolean aspects or as external properties of an external state abstraction.

.. centered:: **Legality Rules**

.. _tu-fe-external_state-01:

1. If an external state is declared without any of the external
   properties specified then all of the properties default to a value
   of True.

.. _tu-fe-external_state-02:

2. If just the name of the property is given then its value defaults
   to True [for instance Async_Readers defaults to Async_Readers =>
   True].

.. _tu-fe-external_state-03:

3. A property may be explicitly given the value False [for instance Async_Readers => False].

.. _tu-fe-external_state-04:

4. If any one property is explicitly defined, all undefined properties default to a value of False.

.. _tu-fe-external_state-05:

5. The expression defining the Boolean valued property shall be static.

.. _tu-fe-external_state-06:

6. Only the following combinations of properties are valid:

   * Async_Readers, Effective_Writes, others => False;

   * Async_Writers, Effective_Reads, others => False;

   * Async_Readers, others => False;

   * Async_Writers, others => False;

   * Async_Readers, Async_Writers, Effective_Writes, others => False;

   * Async_Readers, Async_Writers, Effective_Reads, others => False;

   * Async_Readers, Async_Writers, others => False; and

   * others => True.

     [Another way of expressing this rule is that Effective_Reads can
     only be True if Async_Writers is True and Effective_Writes can only
     be True if Async_Readers is True.]

.. _etu-external_state-lr:

.. centered:: **Static Semantics**

.. _tu-fa-external_state-07:

7. Every update of an external state is considered to be read by
   some external reader if Async_Readers => True.

.. _tu-pr-external_state-08:

8. Each successive read of an external state might have a different
   value [written by some external writer] if Async_Writers => True.

.. _tu-fa-external_state-09:

9. If Effective_Writes => True, then every value written to the
   external state is significant. [For instance writing a sequence of
   values to a port.]

.. _tu-pr-external_state-10:

10. If Effective_Reads => True, then every value read from the
    external state is significant. [For example a value read from a
    port might be used in determining how the next value is
    processed.]

.. _tu-fa-external_state-11:

11. Each update of an external state has no external effect if both
    Async_Readers => False and Effective_Writes => False.

.. _tu-pr-external_state-12:

12. Each successive read of an external state will result in the last
    value explicitly written [by the program] if Async_Writers => False.

.. _tu-fa-external_state-13:

13. Every explicit update of an external state might affect the next value
    read from the external state even if Async_Writers => True.

.. _tu-fa-external_state-14:

14. An external state which has the property Async_Writers => True
    need not be initialized before being read although explicit
    initialization is permitted. [The external state might be
    initialized by an external writer.]

.. _etu-external_state-ss:

.. _external_state-variables:

External State - Variables
~~~~~~~~~~~~~~~~~~~~~~~~~~

In Ada interfacing to an external device or subsystem normally entails
using one or more effectively volatile objects to ensure that writes and reads
to the device are not optimized by the compiler into internal register
reads and writes.

|SPARK| refines the specification of volatility by introducing four new Boolean
aspects which may be applied only to effectively volatile objects. The aspects
may be specified in the aspect specification of an object declaration
(this excludes effectively volatile objects that are formal parameters).

The new aspects are:

  * Async_Readers - as described in :ref:`external_state`.

  * Async_Writers - as described in :ref:`external_state`.

  * Effective_Reads - as described in :ref:`external_state`.

  * Effective_Writes - as described in :ref:`external_state`.

.. centered:: **Static Semantics**

1. Concurrent accesses of an effectively volatile object may cause a run-time
   exception that cannot be proven to be absent by |SPARK|.

   [An example is a strictly 32-bit machine with a 64-bit Long_Float
   type, where some (invalid) floating point values will trap (and
   cause program termination) when loaded into a floating point
   register.  If, on such a system, we have a volatile object X of
   type Long_Float, this variable will have to be stored using two
   memory writes, so concurrent reads/writes could cause the trap, as
   we could be unlucky and see a partially updated value that happens
   to be invalid, even though both the old and new values would be
   valid.]

2. The key difference between accesses to atomic variables (they cause
   expensive memory barriers to be used) and volatile accesses:
   volatile use regular reads and writes, and use multiple memory
   operations for doing so. Atomic accesses cause synchronization and
   must by definition be indivisible.

.. centered:: **Legality Rules**

.. _tu-cbatu-external_state_variables-03:

3. All effectively volatile objects are considered to have one or more external
   state properties, either given explicitly in their declaration or
   implicitly when all the properties are considered to be True. The
   following rules also apply to all effectively volatile objects.

.. _tu-fe-external_state_variables-04:

4. The aspects shall only be specified in the aspect specification of an
   effectively volatile object declaration excluding volatile formal
   parameter declarations.

.. _tu-fe-external_state_variables-05:

5. The declaration of an effectively volatile object (other than as a formal
   parameter) shall be at library level. [That is, it shall not be
   declared within the scope of a subprogram body. An effectively
   volatile object has an external effect and therefore should be global
   even if it is not visible. It is made visible via a state abstraction.]

.. _tu-fe-external_state_variables-06:

6. A constant object, a discriminant or a loop parameter shall not
   be effectively volatile.

.. _tu-fe-external_state_variables-07:

7. A object which is not effectively volatile shall not have a volatile component.

.. _tu-fe-external_state_variables-08:

8. An effectively volatile object shall not be used as an actual parameter in a
   generic instantiation.

.. _tu-fe-external_state_variables-09:

9. An effectively volatile object shall not be a ``global_item`` of a function.

.. _tu-fe-nt-external_state_variables-10:

10. A function shall not have a formal parameter of an effectively
    volatile type.

.. _tu-fe-external_state_variables-11:

11. If an effectively volatile object has set to True any of:

   - Async_Readers, Effective_Writes or Effective_Reads - it may only
     used as an actual parameter of a procedure whose corresponding
     formal parameter is of mode **out** or **in out**; or

   - Async_Writers - it may only used as an actual parameter of a
     procedure whose corresponding formal parameter is of mode **in**
     or **in out**.

.. _tu-fe-nt-external_state_variables-12:

12. A effectively volatile object shall only occur as an actual parameter of a
    subprogram if the corresponding formal parameter is of a
    non-scalar effectively volatile type or as an actual parameter in a call to an
    instance of Unchecked_Conversion.

.. _tu-fe-external_state_variables-13:

13. Contrary to the general |SPARK| rule that expression evaluation
    cannot have side effects, a read of an effectively volatile object with
    the properties Async_Writers or Effective_Reads set to True is
    considered to have an effect when read. To reconcile this
    discrepancy, a name denoting such an object shall only occur in
    a *non-interfering context*. A name occurs in a non-interfering
    context if it is:

   * the name on the left-hand side of an assignment statement; or

   * the [right-hand side] expression of an assignment statement; or

   * the expression of an initialization expression of an object declaration; or

   * the actual parameter in a call to an instance of Unchecked_Conversion
     whose result is renamed [in an object renaming declaration]; or

   * the actual parameter in a procedure call of which the corresponding
     formal parameter is of a non-scalar effectively volatile type; or

   * the prefix of a ``slice``, ``selected_component``, ``indexed_component``,
     or ``attribute_reference`` which is itself a name occurring in a
     non-interfering context; or

   * the expression of a type conversion occurring in a non-interfering context.

.. _etu-external_state_variables-lr:


.. centered:: **Static Semantics**

These are explained in :ref:`external_state`.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with these aspects.

.. centered:: **Verification Rules**

.. _tu-nt-external_state_variables-14:

14. As formal subprogram parameters of an effectively volatile type cannot
    have these aspects specified assumptions have to be made in the body
    of the subprogram of the properties that the formal parameter of a
    given mode may have as follows:

    * mode **in**: the formal parameter cannot be updated by the
      subprogram and is considered to have the properties
      Async_Writers => True and Effective_Reads => False. The actual
      parameter in a call must be effectively volatile and have these properties
      but may also have the properties Async_Readers and
      Effective_Writes set to True.

    * mode **out**: the formal parameter cannot be read by the
      subprogram as it is unknown whether a read will have an external
      effect. The formal parameter is considered to have the
      properties Async_Readers => True and/or Effective_Writes =>
      True. The actual parameter in a call to the subprogram must be
      effectively volatile and have either or both of these properties True
      but may also have Async_Writers and Effective_Reads set to True. If
      the subprogram attempts a read of the formal parameter a flow
      anomaly will be reported.

    * mode **in out**: the formal parameter is considered to have all
      properties; Async_Readers => True, Async_Writers => True,
      Effective_Reads => True, Effective_Writes => True. The actual
      parameter in a subprogram call must be effectively volatile and have
      all of these properties set to True.

.. _etu-external_state_variables-vr:

.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/input_port.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/output_port.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/multiple_ports.ads
   :language: ada
   :linenos:


.. _abstract-state-aspect:

Abstract_State Aspects
~~~~~~~~~~~~~~~~~~~~~~

State abstraction provides a mechanism for naming, in a package’s visible part,
state (typically a collection of variables) that will be declared within the
package’s body (its hidden state). For example, a package declares a visible
procedure and we wish to specify the set of global variables that the procedure
reads and writes as part of the specification of the subprogram. The variables
declared in the package body cannot be named directly in the package
specification. Instead, we introduce a state abstraction which is visible in the
package specification and later, when the package body is declared, we specify
the set of variables that *constitute* or *implement* the state abstraction.

If immediately within a package body, for example, a nested_package is declared,
then a state abstraction of the inner package may also be part of the
implementation of the given state abstraction of the outer package.

The hidden state of a package may be represented by one or more state
abstractions, with each pair of state abstractions representing disjoint sets of
hidden variables.

If a subprogram P with a Global aspect is declared in the visible part of a
package and P reads or updates any of the hidden state of the package then
the state abstractions shall be denoted by P. If P has a Depends aspect then
the state abstractions shall be denoted as inputs and outputs of P, as
appropriate, in the ``dependency_relation`` of the Depends aspect.

|SPARK| facilitates the specification of a hierarchy of state abstractions by
allowing a single state abstraction to contain visible declarations of package
declarations nested immediately within the body of a package, private child or
private sibling units and descendants thereof. Each visible state abstraction or
variable of a private child or descendant thereof has to be specified as being
*part of* a state abstraction of its parent or a public descendant of its parent.

The Abstract_State aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is Abstract_State and the ``aspect_definition``
shall follow the grammar of ``abstract_state_list`` given below.

.. centered:: **Syntax**

..  _tu-fe-abstract_state_aspects-syntax:

::

  abstract_state_list      ::= null
                             | state_name_with_options
                             | ( state_name_with_options { , state_name_with_options } )
  state_name_with_options  ::= state_name
                             | ( state_name with option_list )
  option_list              ::= option { , option }
  option                   ::= simple_option
                             | name_value_option
  simple_option            ::= Ghost
  name_value_option        ::= Part_Of => abstract_state
                             | External [=> external_property_list]
  external_property_list   ::= external_property
                             | ( external_property {, external_property} )
  external_property        ::= Async_Readers [=> expression]
                             | Async_Writers [=> expression]
                             | Effective_Writes [=> expression]
                             | Effective_Reads  [=> expression]
                             | others => expression
  state_name               ::= defining_identifier
  abstract_state           ::= name

.. _etu-abstract_state_aspects-syntax:

.. centered:: **Legality Rules**

.. _tu-fe-abstract_state_aspects-01:

1. An ``option`` shall not be repeated within a single ``option_list``.

.. _tu-fe-abstract_state_aspects-02:

2. If External is specified in an ``option_list`` then there shall be at most
   one occurrence of each of Async_Readers, Async_Writers, Effective_Writes
   and Effective_Reads.

.. _tu-fe-abstract_state_aspects-03:

3. If an ``option_list`` contains one or more ``name_value_option`` items
   then they shall be the final options in the list.
   [This eliminates the possibility of a positional
   association following a named association in the property list.]

.. _tu-fe-abstract_state_aspects-04:

4. A package_declaration or generic_package_declaration that contains a
   non-null Abstract_State aspect must have a completion (i.e. such a
   package requires a body).

.. _tu-abstract_state_aspects-05:

5. A function declaration that overloads a state abstraction has an implicit
   Global aspect denoting the state abstraction with a ``mode_selector`` of
   Input. An explicit Global aspect may be specified which replaces the
   implicit one.

.. _etu-abstract_state_aspects-lr:

.. centered:: **Static Semantics**

.. _tu-cbatu-abstract_state_aspects-06:

6. Each ``state_name`` occurring in an Abstract_State aspect
   specification for a given package P introduces an implicit
   declaration of a state abstraction entity. This implicit
   declaration occurs at the beginning of the visible part of P. This
   implicit declaration shall have a completion and is overloadable.

   [The declaration of a state abstraction has the same visibility as
   any other declaration but a state abstraction shall only be named
   in contexts where this is explicitly permitted (e.g., as part of a
   Global aspect specification). A state abstraction is not an
   object; it does not have a type. The completion of a state
   abstraction declared in a package ``aspect_specification`` can only
   be provided as part of a Refined_State ``aspect_specification``
   within the body of the package.]

.. _tu-fe-abstract_state_aspects-07:

7. A **null** ``abstract_state_list`` specifies that a package contains no
   hidden state.

.. _tu-fe-abstract_state_aspects-08:

8. An External state abstraction is one declared with an ``option_list``
   that includes the External ``option`` (see :ref:`external_state`).

.. _tu-fe-abstract_state_aspects-09:

9. A state abstraction which is declared with an ``option_list`` that includes
   a Part_Of ``name_value_option`` indicates that it is a constituent (see
   :ref:`state_refinement`) exclusively of the state abstraction
   denoted by the ``abstract_state`` of the ``name_value_option`` (see
   :ref:`package_hierarchy`).

.. _tu-fe-abstract_state_aspects-10:

10. A state abstraction for which the ``simple_option`` Ghost is
    specified is said to be a ghost state abstraction.

.. _etu-abstract_state_aspects-ss:

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Abstract_State aspect.

.. centered:: **Verification Rules**

There are no verification rules associated with the Abstract_State aspect.

.. centered:: **Examples**

.. code-block:: ada

   package Q
     with Abstract_State => State         -- Declaration of abstract state named State
                                          -- representing internal state of Q.
   is
      function Is_Ready return Boolean    -- Function checking some property of the State.
        with Global => State;             -- State may be used in a global aspect.

      procedure Init                      -- Procedure to initialize the internal state of Q.
        with Global => (Output => State), -- State may be used in a global aspect.
	     Post   => Is_Ready;

      procedure Op_1 (V : Integer)     -- Another procedure providing some operation on State
        with Global => (In_Out => State),
             Pre    => Is_Ready,
             Post   => Is_Ready;
   end Q;

   package X
     with Abstract_State => (A,
                             B,
                             (C with External => (Async_Writers,
                                                  Effective_Reads => False))
     --  Three abstract state names are declared A, B & C.
     --  A and B are internal abstract states
     --  C is specified as external state which is an external input.
   is
      ...
   end X;

   package Mileage
     with Abstract_State => (Trip,  -- number of miles so far on this trip
                                    -- (can be reset to 0).
                             Total) -- total mileage of vehicle since last factory-reset.
   is
      function Trip  return Natural;  -- Has an implicit Global => Trip.
      function Total return Natural;  -- Has an implicit Global => Total.

      procedure Zero_Trip
        with Global  => (Output => Trip),  -- In the Global and Depends aspects
             Depends => (Trip => null),    -- Trip denotes the state abstraction.
             Post    => Trip = 0;          -- In the Post condition Trip denotes
                                           -- the function.
      procedure Inc
        with Global  => (In_Out => (Trip, Total)),
             Depends => ((Trip, Total) =>+ null),
             Post    => Trip = Trip'Old + 1 and Total = Total'Old + 1;

      -- Trip and Old in the Post conditions denote functions but these
      -- represent the state abstractions in Global and Depends specifications.

   end Mileage;

.. _initializes_aspect:

Initializes Aspects
~~~~~~~~~~~~~~~~~~~

The Initializes aspect specifies the visible variables and state abstractions of
a package that are initialized by the elaboration of the package. In |SPARK|
a package shall only initialize variables declared immediately within the package.

If the initialization of a variable or state abstraction, *V*, during the
elaboration of a package, *P*, is dependent on the value of a visible variable or
state abstraction from another package, then this entity shall be denoted in
the input list associated with *V* in the Initializes aspect of *P*.

The Initializes aspect is introduced by an ``aspect_specification`` where the
``aspect_mark`` is Initializes and the ``aspect_definition`` shall follow the
grammar of ``initialization_spec`` given below.

.. centered:: **Syntax**

.. _tu-fe-initializes_aspects-syntax:

::

  initialization_spec ::= initialization_list
                        | null

  initialization_list ::= initialization_item
                        | ( initialization_item { , initialization_item } )

  initialization_item ::= name [ => input_list]

.. _etu-initializes_aspects-syntax:

.. centered:: **Legality Rules**

.. _tu-fe-initializes_aspects-01:

1. An Initializes aspect shall only appear in the ``aspect_specification`` of a
   ``package_specification``.

.. _tu-fe-initializes_aspects-02:

2. The Initializes aspect shall follow the Abstract_State aspect if one is
   present.

.. _tu-fe-initializes_aspects-03:

3. The ``name`` of each ``initialization_item`` in the Initializes aspect
   definition for a package shall denote a state abstraction of the package
   or an entire variable or constant declared immediately within the
   visible part of the package.

.. _tu-fe-initializes_aspects-04:

4. Each ``name`` in the ``input_list`` shall denote an entire variable, a
   formal parameter, a constant, or a state abstraction but shall not
   denote an entity declared in the package with the
   ``aspect_specification`` containing the Initializes aspect.

.. _tu-fe-initializes_aspects-05:

5. Each entity in a single ``input_list`` shall be distinct.

.. _tu-fe-initializes_aspects-06:

6. An ``initialization_item`` with a **null** ``input_list`` is
   equivalent to the same ``initialization_item`` without an ``input_list``.
   [That is Initializes => (A => **null**) is equivalent to Initializes => A.]

.. _etu-initializes_aspects-lr:

.. centered:: **Static Semantics**

.. _tu-fe-initializes_aspects-07:

7. The Initializes aspect of a package has visibility of the declarations
   occurring immediately within the visible part of the package.

.. _tu-fa-initializes_aspects-08:

8. The Initializes aspect of a package specification asserts which
   state abstractions and visible variables of the package are initialized
   by the elaboration of the package, both its specification and body, and
   any units which have state abstractions or variable declarations that are
   part (constituents) of a state abstraction declared by the package.
   [A package with a **null** ``initialization_list``, or no Initializes aspect
   does not initialize any of its state abstractions or variables.]

.. _tu-fe-initializes_aspects-09:

9. An ``initialization_item`` shall have an ``input_list`` if and
   only if its initialization is dependent on visible variables and
   state anbstractions not declared within the package containing the
   Initializes aspect.  Then the ``names`` in the ``input_list`` shall
   denote variables and state abstractions which are used in
   determining the initial value of the state abstraction or variable
   denoted by the ``name`` of the ``initialization_item`` but are not
   constituents of the state abstraction.

.. _etu-initializes_aspects-ss:

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Initializes aspect.

.. centered:: **Verification Rules**

.. _tu-fa-initializes_aspects-10:

10. If the Initializes aspect is specified for a package, then after
    the body (which may be implicit if the package has no explicit
    body) has completed its elaboration, every (entire) variable and
    state abstraction denoted by a ``name`` in the Initializes aspect
    shall be initialized. A state abstraction is said to be
    initialized if all of its constituents are initialized. An entire
    variable is initialized if all of its components are initialized.
    Other parts of the visible state of the package shall not be
    initialized.

.. _tu-fa-initializes_aspects-11:

11. If an ``initialization_item`` has an ``input_list`` then the
    variables and state abstractions denoted in the input list shall
    be used in determining the initialized value of the entity denoted
    by the ``name`` of the ``initialization_item``.

.. _tu-fa-initializes_aspects-12:

12. All variables and state abstractions which are not declared within
    the package but are used in the initialization of an
    ``initialization_item`` shall appear in an ``input_list`` of the
    ``initialization_item``.

.. _tu-fa-initializes_aspects-13:

13. Any ``initialization_item`` that is a constant must be a *constant with
    variable input*. Any entity in ``input_list`` that is a constant must
    be a parameter or *constant with variable input*.

.. _tu-nt-initializes_aspects-note_1:

[Note: these rules allow a variable or state abstraction to be
initialized by the elaboration of a package but not be denoted in an
Initializes aspect.  In such a case the analysis tools will treat the
variable or state abstraction as uninitialized when analyzing clients
of the package.]

.. _etu-initializes_aspects-note:

.. centered:: **Examples**

.. code-block:: ada

   package Q
     with Abstract_State => State,        -- Declaration of abstract state name State
          Initializes    => (State,       -- Indicates that State
                             Visible_Var) -- and Visible_Var will be initialized
                                          -- during the elaboration of Q.
   is
      Visible_Var : Integer;
      ...
   end Q;


   with Q;
   package R
     with Abstract_State => S1,                   -- Declaration of abstract state name S1
          Initializes    => (S1 => Q.State,       -- Indicates that S1 will be initialized
                                                  -- dependent on the value of Q.State
                             X  => Q.Visible_Var) -- and X dependent on Q.Visible_Var
                                                  -- during the elaboration of Q.
   is
      X : Integer := Q.Visible_Var;
      ...
   end Q;

   package Y
     with Abstract_State => (A, B, (C with External => (Async_Writers, Effective_Reads))),
          --  Three abstract state names are declared A, B & C.
          Initializes    => A
          --  A is initialized during the elaboration of Y.
          --  C is specified as external state with Async_Writers
          --  and need not be explicitly initialized.
          --  B is not initialized.
   is
      ...
   end Y;

   package Z
     with Abstract_State => A,
          Initializes    => null
          --  Package Z has an abstract state name A declared but the
          --  elaboration of Z and its private descendants do not
          --  perform any initialization during elaboration.
   is
      ...
   end Z;

.. _initial_condition_aspect:

Initial_Condition Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~

The Initial_Condition aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Initial_Condition and the ``aspect_definition`` shall
be a *Boolean_*\ ``expression``.

.. centered:: **Legality Rules**

.. _tu-fe-initial_condition_aspects-01:

1. An Initial_Condition aspect shall only be placed in an ``aspect_specification``
   of a ``package_specification``.

.. _tu-fe-initial_condition_aspects-02:

2. The Initial_Condition aspect shall follow the Abstract_State aspect and
   Initializes aspect if they are present.

.. _tu-nt-initial_condition_aspects-03:

3. Rule removed.

.. _etu-initial_condition_aspects-lr:

.. centered:: **Static Semantics**

.. _tu-fe-pf-initial_condition_aspects-04:

4. An Initial_Condition aspect is an assertion and behaves as a
   postcondition for the elaboration of both the specification and
   body of a package. If present on a package, then its assertion
   expression defines properties (a predicate) of the state of the
   package which can be assumed to be true immediately following the
   elaboration of the package. [The expression of the
   Initial_Condition cannot denote a state abstraction. This means
   that to express properties of hidden state, functions declared in
   the visible part acting on the state abstractions of the package
   must be used.]


.. _etu-initial_condition_aspects-ss:

.. centered:: **Dynamic Semantics**

.. _tu-pr-fa-initial_condition_aspects-05:

5. With respect to dynamic semantics, specifying a given expression as
   the Initial_Condition aspect of a package is equivalent to
   specifying that expression as the argument of an Assert pragma
   occurring at the end of the (possibly implicit) statement list of
   the (possibly implicit) body of the package. [This equivalence
   includes all interactions with pragma Assertion_Policy but does not
   extend to matters of static semantics, such as name resolution.] An
   Initial_Condition expression does not cause freezing until the
   point where it is evaluated [, at which point everything that it
   might freeze has already been frozen].

.. _etu-initial_condition_aspects-ds:

.. centered:: **Verification Rules**

.. _tu-pr-initial_condition_aspects-06:

6. [The Initial_Condition aspect gives a verification condition to show that the
   implementation of the ``package_specification`` and its body satisfy the
   predicate given in the Initial_Condition aspect.]

.. _tu-fe-initial_condition_aspects-07:

7. Each variable or indirectly referenced state abstraction in an
   Initial_Condition aspect of a package Q which is declared
   immediately within the visible part of Q shall be initialized
   during the elaboration of Q and be denoted by a ``name`` of an
   ``initialization_item`` of the Initializes aspect of Q.

.. _etu-initial_condition_aspects-vr:

.. centered:: **Examples**

.. code-block:: ada

    package Q
       with Abstract_State    => State,    -- Declaration of abstract state name State
            Initializes       => State,    -- State will be initialized during elaboration
            Initial_Condition => Is_Ready  -- Predicate stating the logical state after
	                                   -- initialization.
    is
       function Is_Ready return Boolean
          with Global => State;
    end Q;

    package X
       with Abstract_State    => A,      -- Declares an abstract state named A
            Initializes       => (A, B), -- A and visible variable B are initialized
	                                 -- during package initialization.
            Initial_Condition => A_Is_Ready and B = 0
	                                 -- The logical conditions that hold
                                         -- after package elaboration.
    is
       ...
       B : Integer;

       function A_Is_Ready return Boolean
          with Global => A;
    end X;

Package Bodies
--------------

.. _state_refinement:

State Refinement
~~~~~~~~~~~~~~~~

A ``state_name`` declared by an Abstract_State aspect in the specification of a
package shall denote an abstraction representing all or part of its hidden
state. The declaration must be completed in the package body by a Refined_State
aspect. The Refined_State aspect defines a *refinement* for each ``state_name``.
The refinement shall denote the variables and subordinate state abstractions
represented by the ``state_name`` and these are known as its *constituents*.

Constituents of each ``state_name`` have to be initialized
consistently with that of their representative ``state_name`` as
determined by its denotation in the Initializes aspect of the package.

A subprogram may have an *abstract view* and a *refined view*. The
abstract view is a subprogram declaration in a package specification
of a package where a subprogram may refer to private types and
state abstractions whose details are not visible. A refined view of a
subprogram is the body or body stub of the subprogram in the package
body whose specification declares its abstract view.

In a refined view a subprogram has visibility of the full type declarations of
any private types declared by the enclosing package and visibility of the
refinements of state abstractions declared by the package. Refined versions of
aspects are provided to express the contracts of a refined view of a subprogram.

.. _refined_state_aspect:

Refined_State Aspects
~~~~~~~~~~~~~~~~~~~~~

The Refined_State aspect is introduced by an ``aspect_specification`` where the
``aspect_mark`` is Refined_State and the ``aspect_definition`` shall follow
the grammar of ``refinement_list`` given below.

.. centered:: **Syntax**

.. _tu-fe-refined_state_aspects-syntax:

::

  refinement_list   ::= ( refinement_clause { , refinement_clause } )
  refinement_clause ::= state_name => constituent_list
  constituent_list  ::= null
                      | constituent
                      | ( constituent { , constituent } )

where

  ``constituent ::=`` *object_*\ ``name | state_name``

.. _etu-refined_state_aspects-syntax:

.. centered:: **Name Resolution Rules**

.. _tu-fe-refined_state_aspects-01:

1. A Refined_State aspect of a ``package_body`` has visibility extended to the
   ``declarative_part`` of the body.

.. _etu-refined_state_aspects-nr:

.. centered:: **Legality Rules**

.. _tu-fe-refined_state_aspects-02:

2. A Refined_State aspect shall only appear in the ``aspect_specification`` of a
   ``package_body``. [The use of ``package_body`` rather than package body
   allows this aspect to be specified for generic package bodies.]

.. _tu-fe-refined_state_aspects-03:

3. If a ``package_specification`` has a non-null Abstract_State aspect its body
   shall have a Refined_State aspect.

.. _tu-fe-refined_state_aspects-04:

4. If a ``package_specification`` does not have an Abstract_State aspect,
   then the corresponding ``package_body`` shall not have a Refined_State
   aspect.

.. _tu-fe-refined_state_aspects-05:

5. Each ``constituent`` shall be either a variable, a constant, or a state
   abstraction.

.. _tu-fe-refined_state_aspects-06:

6. An object which is a ``constituent`` shall be an entire object.

.. _tu-fe-refined_state_aspects-07:

7. A ``constituent`` of a state abstraction of a package shall denote
   either an entity with no Part_Of ``option`` or aspect which is part
   of the hidden state of the package, or an entity whose declaration
   has a Part_Of ``option`` or aspect which denotes this state
   abstraction (see :ref:`package_hierarchy`).

.. _tu-fe-refined_state_aspects-08:

8. Each *abstract_*\ ``state_name`` declared in the package
   specification shall be denoted exactly once as the ``state_name``
   of a ``refinement_clause`` in the Refined_State aspect of the body
   of the package.

.. _tu-fe-refined_state_aspects-09:

9. Every entity of the hidden state of a package shall be denoted as a
   ``constituent`` of exactly one *abstract_*\ ``state_name`` in the
   Refined_State aspect of the package and shall not be denoted more than
   once. [These ``constituents`` are either constants or variables declared
   in the private part or body of the package, or the declarations from the
   visible part of nested packages declared immediately therein.]

.. _tu-cbatu-refined_state_aspects-10:

10. In a package body where the refinement of a state abstraction is
    visible the ``constituents`` of the state abstraction must be
    denoted in aspect specifications rather than the state
    abstraction.

.. _tu-cbatu-refined_state_aspects-11:

11. The legality rules related to a Refined_State aspect given in
    :ref:`package_hierarchy` also apply.

.. _tu-cbatu-refined_state_aspects-12:

12. Each ``constituent`` of a ghost state abstraction shall be either
    a ghost variable or a ghost state abstraction. [The reverse situation
    (i.e., a ghost constituent of a non-ghost state abstraction) is permitted.]

.. _etu-refined_state_aspects-lr:

.. centered:: **Static Semantics**

.. _tu-fe-refined_state_aspects-13:

13. A Refined_State aspect of a ``package_body`` completes the
    declaration of the state abstractions occurring in the
    corresponding ``package_specification`` and defines the objects
    and each subordinate state abstraction that are the
    ``constituents`` of the *abstract_*\ ``state_names`` declared in
    the ``package_specification``.

.. _tu-fe-refined_state_aspects-14:

14. A **null** ``constituent_list`` indicates that the named abstract
    state has no constituents and termed a *null_refinement*. The
    state abstraction does not represent any actual state at
    all. [This feature may be useful to minimize changes to Global and
    Depends aspects if it is believed that a package may have some
    extra state in the future, or if hidden state is removed.]

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with Refined_State aspect.

.. centered:: **Verification Rules**

.. _tu-fe-refined_state_aspects-15:

15. Each ``constituent`` that is a constant must be a constant *with
    variable inputs*.

.. _etu-refined_state_aspects-ss:

.. centered:: **Examples**

.. code-block:: ada

   -- Here, we present a package Q that declares two abstract states:
   package Q
      with Abstract_State => (A, B),
           Initializes    => (A, B)
   is
      ...
   end Q;

   -- The package body refines
   --   A onto three concrete variables declared in the package body
   --   B onto the abstract state of a nested package
   package body Q
      with Refined_State => (A => (F, G, H),
                             B => R.State)
   is
      F, G, H : Integer := 0; -- all initialized as required

      package R
         with Abstract_State => State,
              Initializes    => State -- initialized as required
      is
         ...
      end R;

      ...
   end Q;


Initialization Issues
~~~~~~~~~~~~~~~~~~~~~

Every state abstraction specified as being initialized in the Initializes
aspect of a package has to have all of its constituents initialized. This
may be achieved by initialization within the package, by assumed
pre-initialization (in the case of external state) or, for constituents
which reside in another package, initialization by their declaring package.

.. centered:: **Verification Rules**

.. _tu-fa-initialization_issues-01:

1. For each state abstraction denoted by the ``name`` of an
   ``initialization_item`` of an Initializes aspect of a package, all the
   ``constituents`` of the state abstraction must be initialized by:

   * initialization within the package; or

   * assumed pre-initialization (in the case of external states); or

   * for constituents which reside in another unit [and have a Part_Of
     indicator associated with their declaration (see
     :ref:`package_hierarchy`)] by their declaring package. [It follows
     that such constituents will appear in the initialization clause
     of the declaring unit unless they are external states.]

.. _etu-initialization_issues:

.. _refined-global-aspect:

Refined_Global Aspects
~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the specification of a package may
have a Refined_Global aspect applied to its body or body stub. A
Refined_Global aspect of a subprogram defines a *refinement* of the
Global Aspect of the subprogram; that is, the Refined_Global aspect
repeats the Global aspect of the subprogram except that references to
state abstractions whose refinements are visible at the point of the
subprogram_body are replaced with references to [some or all of the]
constituents of those abstractions.

The Refined_Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Refined_Global and the ``aspect_definition``
shall follow the grammar of ``global_specification`` in :ref:`global-aspects`.

.. centered:: **Static Semantics**

1. The static semantics are equivalent to those given for the Global aspect in
   :ref:`global-aspects`.

.. centered:: **Legality Rules**

.. _tu-fe-refined_global_aspects-02:

2. A Refined_Global aspect is permitted on a body_stub (if one is
   present) or subprogram body if and only if it has a declaration in the
   specification of an enclosing package, the declaration has a
   Global aspect which denotes a state abstraction declared by the package and
   the refinement of the state abstraction is visible.

.. _tu-fe-refined_global_aspects-03:

3. A Refined_Global aspect specification shall *refine* the subprogram's
   Global aspect as follows:

   a. For each ``global_item`` in the Global aspect which denotes a
      state abstraction whose non-**null** refinement is visible at
      the point of the Refined_Global aspect specification, the
      Refined_Global specification shall include one or more
      ``global_items`` which denote ``constituents`` of that state
      abstraction.

   b. For each ``global_item`` in the Global aspect which denotes a
      state abstraction whose **null** refinement is visible at the
      point of the Refined_Global aspect specification, the
      Refined_Global specification shall be omitted, or if required by
      the syntax of a ``global_specification`` replaced by a **null**
      in the Refined_Global aspect.

   c. For each ``global_item`` in the Global aspect which does not
      denote a state abstraction whose refinement is visible, the
      Refined_Global specification shall include exactly one
      ``global_item`` which denotes the same entity as the
      ``global_item`` in the Global aspect.

   d. No other ``global_items`` shall be included in the Refined_Global
      aspect specification.

.. _tu-fe-refined_global_aspects-04:

4. ``Global_items`` in a Refined_Global ``aspect_specification`` shall denote
   distinct entities.

.. _tu-fe-refined_global_aspects-05:

5. The mode of each ``global_item`` in a Refined_Global aspect shall match
   that of the corresponding ``global_item`` in the Global aspect unless:
   the ``mode_selector`` specified in the Global aspect is In_Out;
   the corresponding ``global_item`` of Global aspect shall denote a state
   abstraction whose refinement is visible; and the ``global_item`` in the
   Refined_Global aspect is a ``constituent`` of the state abstraction.

   a. For this special case when the ``mode_selector`` is In_Out, the
      Refined_Global aspect may denote individual ``constituents`` of
      the state abstraction as Input, Output, or In_Out (given that
      the constituent itself may have any of these ``mode_selectors``)
      so long as one or more of the following conditions are
      satisfied:

      * at least one of the ``constituents`` has a ``mode_selector``
        of In_Out; or

      * there is at least one of each of a ``constituent`` with a
        ``mode_selector`` of Input and of Output; or

      * the Refined_Global aspect does not denote all of the
        ``constituents`` of the state abstraction but denotes at least
        one ``constituent`` that has a ``mode_selector`` of Output.

   [This rule ensures that a state abstraction with the ``mode_selector``
   In_Out cannot be refined onto a set of ``constituents`` that are Output or
   Input only. The last condition satisfies this requirement because not all of
   the ``constituents`` are updated, some are preserved, that is the state
   abstraction has a self-dependency.]

.. _tu-fe-refined_global_aspects-06:

6. If the Global aspect specification references a state abstraction with a
   ``mode_selector`` of Output, whose refinement is visible, then every
   ``constituent`` of that state abstraction shall be referenced in the
   Refined_Global aspect specification.

.. _tu-cbatu-refined_global_aspects-07:

7. The legality rules for :ref:`global-aspects` and External states described in
   :ref:`refined_external_states` also apply.

.. _etu-refined_global_aspects-lr:

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Refined_Global aspect.

.. centered:: **Verification Rules**

.. _tu-fa-refined_global_aspects-08:

8. If a subprogram has a Refined_Global aspect it is used in the analysis of the
   subprogram body rather than its Global aspect.

.. _tu-cbatu-refined_global_aspects-09:

9. The verification rules given for :ref:`global-aspects` also apply.

.. _etu-refined_global_aspects-vr:

.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/refined_global_examples.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/refined_global_examples.adb
   :language: ada
   :linenos:


.. _refined-depends-aspect:

Refined_Depends Aspects
~~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the specification of a package may have a Refined_Depends
aspect applied to its body or body stub. A Refined_Depends aspect of a
subprogram defines a *refinement* of the Depends aspect of the subprogram; that
is, the Refined_Depends aspect repeats the Depends aspect of the subprogram
except that references to state abstractions, whose refinements are visible at
the point of the subprogram_body, are replaced with references to [some or all of
the] constituents of those abstractions.

The Refined_Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Refined_Depends and the ``aspect_definition``
shall follow the grammar of ``dependency_relation`` in :ref:`depends-aspects`.

.. centered:: **Static Semantics**

1. The static semantics are equivalent to those given for the Depends aspect in
   :ref:`depends-aspects`.

.. centered:: **Legality Rules**

.. _tu-fe-refined_depends_aspects-02:

2. A Refined_Depends aspect is permitted on a body_stub (if one is
   present) or subprogram body if and only if it has a declaration in the
   specification of an enclosing package and the declaration has a
   Depends aspect which denotes a state abstraction declared by the package and
   the refinement of the state abstraction is visible.

.. _tu-fe-refined_depends_aspects-03:

3. A Refined_Depends aspect specification is, in effect, a copy of the
   corresponding Depends aspect specification except that any
   references in the Depends aspect to a state abstraction, whose
   refinement is visible at the point of the Refined_Depends
   specification, are replaced with references to zero or more direct
   or indirect constituents of that state abstraction. A
   Refined_Depends aspect shall have a ``dependency_relation`` which
   is derivable from the original given in the Depends aspect as
   follows:

   a. A *partially refined dependency relation* is created by first
      copying, from the Depends aspect, each ``output`` that is not
      state abstraction whose refinement is visible at the point of
      the Refined_Depends aspect, along with its ``input_list``, to
      the partially refined dependency relation as an ``output``
      denoting the same entity with an ``input_list`` denoting the
      same entities as the original. [The order of the ``outputs`` and
      the order of ``inputs`` within the ``input_list`` is
      insignificant.]

   b. The partially refined dependency relation is then extended by
      replacing each ``output`` in the Depends aspect that is a state
      abstraction, whose refinement is visible at the point of the
      Refined_Depends, by zero or more ``outputs`` in the partially
      refined dependency relation. It shall be zero only for a
      **null** refinement, otherwise all of the ``outputs`` shall
      denote a ``constituent`` of the state abstraction.

   c. If the ``output`` in the Depends_Aspect denotes a state
      abstraction which is not also an ``input``, then each
      ``constituent`` of the state abstraction shall be denoted as an
      ``output`` of the partially refined dependency relation.

   d. These rules may, for each ``output`` in the Depends aspect,
      introduce more than one ``output`` in the partially refined
      dependency relation. Each of these ``outputs`` has an
      ``input_list`` that has zero or more of the ``inputs`` from the
      ``input_list`` of the original ``output``.  The union of these
      ``inputs`` and the original state abstraction, if it is an
      ``input`` in the ``input_list``, shall denote the same ``inputs``
      that appear in the ``input_list`` of the original ``output``.

   e. If the Depends aspect has a ``null_dependency_clause``, then the
      partially refined dependency relation has a
      ``null_dependency_clause`` added with an ``input_list`` denoting
      the same ``inputs`` as the original.

   f. The partially refined dependency relation is completed by
      replacing each ``input`` which is a state abstraction, whose
      refinement is visible at the point of the Refined_Depends
      aspect, by zero or more ``inputs`` which are its
      constituents.

   g. If a state abstraction is denoted in an ``input_list`` of a
      ``dependency_clause`` of the original Depends aspect and its
      refinement is visible at the point of the Refined_Depends aspect
      (derived via the process described in the rules 3a - 3f above),
      then:

      - at least one of its ``constituents`` shall be denoted as an
        ``input`` in at least one of the ``dependency_clauses`` of the
        Refined_Depends aspect corresponding to the original
        ``dependency_clause`` in the Depends aspect; or

      - at least one of its ``constituents`` shall be denoted in the
        ``input_list`` of a ``null_dependency_clause``; or

      - the state abstraction is both an ``input`` and an ``output``
        and not every ``constituent`` of the state abstraction is an
        ``output`` of the Refined_Depends aspect. [This rule does not
        exclude denoting a ``constituent`` of such a state abstraction
        in an ``input_list``.]

.. _tu-fe-refined_depends_aspects-04:

4. These rules result in omitting each state abstraction whose **null**
   refinement is visible at the point of the Refined_Depends. If and only if
   required by the syntax, the state abstraction shall be replaced by a **null**
   symbol rather than being omitted.

.. _tu-fe-refined_depends_aspects-05:

5. No other ``outputs`` or ``inputs`` shall be included in the Refined_Depends
   aspect specification. ``Outputs`` in the Refined_Depends aspect
   specification shall denote distinct entities. ``Inputs`` in an ``input_list``
   shall denote distinct entities.

.. _tu-cbatu-refined_depends_aspects-06:

6. [The above rules may be viewed from the perspective of checking the
   consistency of a Refined_Depends aspect with its corresponding Depends
   aspect. In this view, each ``input`` in the Refined_Depends aspect that
   is a ``constituent`` of a state abstraction, whose refinement is visible at
   the point of the Refined_Depends aspect, is replaced by its representative
   state abstraction with duplicate ``inputs`` removed.

   Each ``output`` in the Refined_Depends aspect, which is a
   ``constituent`` of the same state abstraction whose refinement is
   visible at the point of the Refined_Depends aspect, is merged along
   with its ``input_list`` into a single ``dependency_clause`` whose
   ``output`` denotes the state abstraction and ``input_list`` is the
   union of all of the ``inputs`` replaced by their encapsulating
   state abstraction, as described above, and the state abstraction
   itself if not every ``constituent`` of the state abstraction
   appears as an ``output`` in the Refined_Depends aspect.]

.. _tu-cbatu-refined_depends_aspects-07:

7. The rules for :ref:`depends-aspects` also apply.

.. _etu-refined_depends_aspects-lr:

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Refined_Depends aspect
as it is used purely for static analysis purposes and is not executed.

.. centered:: **Verification Rules**

.. _tu-fa-refined_depends_aspects-08:

8. If a subprogram has a Refined_Depends aspect it is used in the analysis of
   the subprogram body rather than its Depends aspect.

.. _tu-cbatu-refined_depends_aspects-09:

9. The verification rules given for :ref:`depends-aspects` also apply.

.. _etu-refined_depends_aspects-vr:

.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/refined_depends_examples.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/refined_depends_examples.adb
   :language: ada
   :linenos:

.. _package_hierarchy:

Abstract_State, Package Hierarchy and Part_Of
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In order to avoid aliasing-related problems (see :ref:
`anti-aliasing`), SPARK 2014 must ensure that if a given piece of
state (either a variable or a state abstraction) is going to be a
constituent of a given state abstraction, that relationship must be
known at the point where the constituent is declared.

For a variable declared immediately within a package body, this is not
a problem.  The state refinement in which the variable is specified as
a constituent precedes the declaration of the variable, and so there
is no *window* between the introduction of the variable and its
identification as a constituent. Similarly for a variable or state
abstraction that is part of the visible state of a package that is
declared immediately within the given package body.

For variable declared immediately within the private part of a
package, such an unwanted window does exist (and similarly for a
variable or state abstraction that is part of the visible state of a
package that is declared immediately within the given private part).

In order to cope with this situation, the Part_Of aspect provides a
mechanism for specifying at the point of a constituent's declaration
the state abstraction to which it belongs, thereby closing the window.
The state abstraction's refinement will eventually confirm this
relationship. The Part_Of aspect, in effect, makes visible a preview
of (some of) the state refinement that will eventually be provided in
the package body.

This mechanism is also used in the case of the visible state of a
private child unit (or a public descendant thereof).

.. centered:: **Static Semantics**

.. _tu-nt-abstract_state_package_hierarchy_and_part_of-01:

1. A *Part_Of indicator* is a Part_Of ``option`` of a state
   abstraction declaration in an Abstract_State aspect, a Part_Of
   aspect specification applied to a variable declaration or a Part_Of
   specification aspect applied to a generic package instantiation. The
   Part_Of indicator shall denote the *encapsulating* state abstraction
   of which the declaration is a constituent.

.. _etu-abstract_state_package_hierarchy_and_part_of-ss:

.. centered:: **Legality Rules**

.. _tu-fe-abstract_state_package_hierarchy_and_part_of-02:

2. A variable declared immediately within the private part of a given
   package or a variable or state abstraction that is part of the
   visible state of a package that is declared immediately within the
   private part of the given package shall have its Part_Of indicator
   specified; the Part_Of indicator shall denote a state abstraction
   declared by the given package.

.. _tu-fe-abstract_state_package_hierarchy_and_part_of-03:

3. A variable or state abstraction which is part of the visible state
   of a private child unit (or a public descendant thereof) shall have
   its Part_Of indicator specified; the Part_Of indicator shall denote
   a state abstraction declared by either the parent unit of the
   private unit or by a public descendant of that parent unit.

.. _tu-nt-abstract_state_package_hierarchy_and_part_of-04:

4. A Part_Of aspect specification for a package instantiation applies
   to each part of the visible state of the instantiation. More
   specifically, explicitly specifying the Part_Of aspect of a package
   instantiation implicitly specifies the Part_Of aspect of each part
   of the visible state of that instantiation. The legality rules for
   such an implicit specification are the same as for an explicit
   specification.

.. _tu-cbatu-abstract_state_package_hierarchy_and_part_of-05:

5. No other declarations shall have a Part_Of indicator.

.. _tu-fe-abstract_state_package_hierarchy_and_part_of-06:

6. The refinement of a state abstraction denoted in a Part_Of
   indicator shall denote as ``constituents`` all of the declarations
   that have a Part_Of indicator denoting the state abstraction. [This
   might be performed once the package body has been processed.]

.. _tu-fe-abstract_state_package_hierarchy_and_part_of-07:

7. A state abstraction and a constituent (direct or indirect) thereof
   shall not both be denoted in one Global, Depends, Initializes,
   Refined_Global or Refined_Depends aspect specification.  The
   denotation must be consistent between the Global and Depends or
   between Refined_Global and Refined_Depends aspects of a single
   subprogram.

.. _etu-abstract_state_package_hierarchy_and_part_of-lr:

.. centered:: **Verification Rules**

.. _tu-fe-abstract_state_package_hierarchy_and_part_of-08:

8. For flow analysis, where a state abstraction is visible as well as
   one or more of its ``constituents``, its refinement is not visible
   and the Global and or Depends aspects of a subprogram denote the
   state abstraction, then in the implementation of the subprogram a
   direct or indirect

   * read of a ``constituent`` of the state abstraction shall be
     treated as a read of the encapsulating state abstraction of the
     ``constituent``; or

   * update of a ``constituent`` of the state abstraction shall be
     treated as an update of the encapsulating state abstraction of
     the ``constituent`` .  An update of such a ``constituent`` is
     regarded as updating its enclosing state abstraction with a self
     dependency as it is unknown what other ``constituents`` the state
     abstraction encapsulates.

.. _etu-abstract_state_package_hierarchy_and_part_of-vr:

.. centered:: **Examples**

.. code-block:: ada

   package P
      --  P has no state abstraction
   is
      ...
   end P;

   --  P.Pub is the public package that declares the state abstraction
   package P.Pub --  public unit
     with Abstract_State => (R, S)
   is
      ...
   end P.Pub;

   --  State abstractions of P.Priv, A and B, plus
   --  the concrete variable X, are split up among
   --  two state abstractions within P.Pub, R and S
   with P.Pub;
   private package P.Priv --  private unit
     with Abstract_State => ((A with Part_Of => P.Pub.R),
                             (B with Part_Of => P.Pub.S))
   is
      X : T  --  visible variable which is a constituent of P.Pub.R.
        with Part_Of => P.Pub.R;
   end P.Priv;

   with P.Priv; --  P.Priv has to be with'd because its state is part of
                --  the refined state.
   package body P.Pub
     with Refined_State => (R => (P.Priv.A, P.Priv.X, Y),
                            S => (P.Priv.B, Z))
   is
      Y : T2;  --  hidden state
      Z : T3;  --  hidden state
      ...
   end P.Pub;

   package Outer
     with Abstract_State => (A1, A2)
   is
      procedure Init_A1
        with Global  => (Output => A1),
             Depends => (A1 => null);

      procedure Init_A2
        with Global  => (Output => A2),
             Depends => (A2 => null);

   private
      --  A variable declared in the private part must have a Part_Of aspect
      Hidden_State : Integer
        with Part_Of => A2;

      package Inner
        with Abstract_state => (B1 with Part_Of => Outer.A1)
        --  State abstraction declared in the private
        --  part must have a Part_Of option.
      is
         --  B1 may be used in aspect specifications provided
         --  Outer.A1 is not also used.
         procedure Init_B1
           with Global  => (Output => B1),
                Depends => (B1 => null);

         procedure Init_A2
           --  We can only refer to Outer.Hidden_State which is
           --  a constituent of Outer.A2 if the subprogram does
           --  not also refer to Outer.A2.
           with Global  => (Output => Hidden_State),
                Depends => (Hidden_State => null);
      end Inner;
   end Outer;

   package body Outer
     with Refined_State => (A1 => Inner.B1,
                            A2 => (Hidden_State, State_In_Body))
     --  A1 and A2 cannot be denoted in the body of Outer because their
     --  refinements are visible.
   is
      State_In_Body : Integer;

      package body Inner
        with Refined_State => (B1 => null)  --  Oh, there isn't any state after all
      is
         procedure Init_B1
           with Refined_Global  => null,  --  Refined_Global and
                Refined_Depends => null   --  Refined_Depends of a null refinement
         is
         begin
            null;
         end Init_B1;

         procedure Init_A2
           --  The Global sparct is already in terms of the constituent
           --  Hidden_State which is part of of A2, so no refined
           --  Global or Depends aspects are required.
         is
         begin
            Outer.Hidden_State := 0;
         end Init_A2;

      end Inner;

      procedure Init_A1
        with Refined_Global  => (Output => Inner.B1),
             Refined_Depends => (Inner.B1 => null)
      is
      begin
         Inner.Init_B1;
      end Init_A1;

      procedure Init_A2
        with Refined_Global  => (Output => (Hidden_State, State_In_Body)),
             Refined_Depends => ((Hidden_State, State_In_Body) => null)
      is
      begin
         State_In_Body := 42;
         Inner.Init_A2;
      end Init_A2;

   end Outer;

   package Outer.Public_Child is
      --  Outer.A1 and Outer.A2 are visible but
      --  Outer.Hidden_State is not (by the rules of Ada)
      --  The Global and Depends Aspects are in terms
      --  of the encapsulating state abstraction Outer.A2.
      procedure Init_A2_With (Val : in Integer)
        with Global  => (Output => Outer.A2),
             Depends => (Outer.A2 => Val);
   end Outer.Public_Child;

   package body Outer.Public_Child is
      --  Outer.Hidden is visible here but the
      --  refinement of A2 is not so there are
      --  no Refined_Global or Refined_Depends
      procedure Init_A2_With (Val : in Integer) is
      begin
         Outer.Init_A2;
         Outer.Hidden_State := Val;
      end Init_A2_With;
   end Outer.Public_Child;


   package Q
     with Abstract_State => (Q1, Q2)
   is
      --  Q1 and Q2 may be denoted here
      procedure Init_Q1
        with Global  => (Output => Q1),
             Depends => (Q1 => null);

      procedure Init_Q2
        with Global  => (Output => Q2),
             Depends => (Q2 => null);

   private
      Hidden_State : Integer
        with Part_Of => Q2;
   end Q;

   private package Q.Child
     with Abstract_State => (C1 with Part_Of => Q.Q1)
   is
      --  C1 rather than the encapsulating state abstraction
      --  may be used in aspect specifications provided
      --  Q.Q1 is not also denoted in the same aspect
      --  specification.

      --  Here C1 is used so Q1 cannot also be used in
      --  the aspect specifications of this subprogram
      procedure Init_Q1
        with Global  => (Output => C1),
             Depends => (C1 => null);

      --  Q.Hidden_State which is a constituent of Q.Q2
      --  is visible here so it can be used in a aspect
      --  specification provided Q.Q2 is not also used.
      procedure Init_Q2
         with Global  => (Output => Q.Hidden_State),
              Depends => (Q.Hidden_State => null);
   end Q.Child;

   package body Q.Child
     with Refined_State => (C1 => Actual_State)
   is
      --  C1 shall not be denoted here - only Actual_State
      --  but Q.Q2 and Q.Hidden_State may be denoted.
      Actual_State : Integer;

      procedure Init_Q1
        with Refined_Global  => (Output => Actual_State),
             Refined_Depends => (Actual_State => null)
      is
      begin
         Actual_State := 0;
      end Init_Q1;

      --  The refinement of Q2 is not visible and so Init_Q2
      --  has no Refined_Global or Refined_Depends aspects.
      procedure Init_Q2 is
      begin
         Q.Hidden_State := 0;
      end Init_Q2;

   end Q.Child;

   package body Q
     with Refined_State => (Q1 => Q.Child.C1,
                            Q2 => Hidden_State, State_In_Body)
   is
      --  Q1 and Q2 shall not be denoted here but the constituents
      --  Q.Child.C1, State_In_Body and Hidden_State may be.
      State_In_Body : Integer;

      procedure Init_Q1
        with Refined_Global  => (Output => Q.Child.C1),
             Refined_Depends => (Q.Child.C1 => null)
      is
      begin
         Q.Child.Init_Q1;
      end Init_Q1;

      procedure Init_Q2
        with Refined_Global  => (Output => (Hidden_State, State_in_Body)),
             Refined_Depends => ((Hidden_State, State_in_Body) => null)
      is
      begin
         Sate_In_Body := 42;
         Q.Child.Init_Q2;
      end Init_Q2;
   end Q;

   package R
     with Abstract_State => R1
   is
      -- R1 may be denoted here
      procedure Init_R1
        with Global  => (Output => R1),
             Depends => (R1 => null);

      procedure Op_1 (I : in Integer)
        with Global  => (In_Out => R1),
             Depends => (R1 =>+ I);
   end Q;

   private package R.Child
     with Abstract_State => (R2 with Part_Of => R.R1)
   is
      --  Both R.R1 and R2 are visible.

      --  Here more than just the R2 constituent of R.R1
      --  will be updated and so we use R.R1 in the
      --  aspect specifications rather than R2.
      --  R2 cannot also be used in the aspect
      --  specifications of this subprogram
      procedure Private_Op (I, J : in Integer)
        with Global  => (In_Out => R.R1),
             Depends => (R.R1 =>+ (I, J));
   end R.Child;

   package body R.Child
     with Refined_State => (R2 => Actual_State)
   is
      --  R2 shall not be denoted here - only Actual_State
      --  but R.R1 may be denoted.
      Actual_State : Integer;

      --  The Global and Depends aspects of Private_Op
      --  are in terms of R.R1 and the refinement of
      --  R.R1 is not visible and so Refined_Global
      --  and Refined_Depends are not required.
      procedure Private_Op (I, J : in Integer) is
      begin
         R.Op_1 (I);
         Actual_State := J;
      end Init_Q1;
   end R.Child;

.. _refined-postcondition:

Refined Postcondition Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the specification of a package may have a Refined
Postcondition aspect applied to its body or body stub. The Refined Postcondition
may be used to restate a postcondition given on the declaration of a subprogram
in terms of the full view of a private type or the ``constituents`` of a refined
``state_name``.

The Refined Postcondition aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is "Refined_Post" and the ``aspect_definition`` shall
be a Boolean ``expression``.

.. centered:: **Legality Rules**

.. _tu-fe-refined_postcondition_aspects-01:

1. A Refined_Post aspect may only appear on a body_stub (if one is
   present) or the body (if no stub is present) of a subprogram which is
   declared in the specification of a package, its abstract view. If the
   subprogram declaration in the visible part has no explicit postcondition, a
   postcondition of True is assumed for the abstract view.

.. _tu-cbatu-refined_postcondition_aspects-02:

2. A Refined_Post aspect is an assertion. The same legality rules
   apply to a Refined_Post aspect as for a postcondition (a Post
   aspect).

.. _etu-refined_postcondition_aspects-lr:

.. centered:: **Static Semantics**

.. _tu-cbatu-refined_postcondition_aspects-03:

3. A Refined Postcondition of a subprogram defines a *refinement*
   of the postcondition of the subprogram.

.. _tu-pr-refined_postcondition_aspects-04:

4. Logically, the Refined Postcondition of a subprogram must imply
   its postcondition. This means that it is perfectly logical for the
   declaration not to have a postcondition (which in its absence
   defaults to True) but for the body or body stub to have a
   Refined Postcondition.

.. _tu-cbatu-refined_postcondition_aspects-05:

5. The static semantics are otherwise as for a postcondition.

.. _etu-refined_postcondition_aspects-ss:

.. centered:: **Dynamic Semantics**

.. _tu-fe-refined_postcondition_aspects-07:

7. When a subprogram with a Refined Postcondition is called; first
   the subprogram is evaluated. The Refined Postcondition is evaluated
   immediately before the evaluation of the postcondition or, if there is no
   postcondition, immediately before the point at which a postcondition would
   have been evaluated. If the Refined Postcondition evaluates to
   True then the postcondition is evaluated as described in the Ada
   RM. If either the Refined Postcondition or the postcondition
   do not evaluate to True then the exception Assertions.Assertion_Error is
   raised.

.. _etu-refined_postcondition_aspects-ds:

.. centered:: **Verification Rules**

.. _tu-pr-refined_postcondition_aspects-08:

8. If a subprogram has both a Refined_Postcondition aspect and a
   Postcondition aspect, then the proof obligation associated with
   the Postcondition aspect is discharged in two steps. The success
   of the Refined_Postcondition run-time check must be proven as usual.
   It must also be shown that the precondition (or, in the case of a dispatching
   operation, the class-wide precondition) and the refined postcondition
   together imply the postcondition of the subprogram, that is:

   (Precondition and Refined Postcondition) -> Postcondition

   [Note that this step does not depend on the statements or
   declarations within the subprogram.]

.. _tu-pr-refined_postcondition_aspects-09:

9. If a Refined_Postcondition aspect specification is visible at the
   point of a call to the subprogram, then the Refined_Postcondition
   is used instead of the Postcondition aspect for purposes of formal
   analysis of the call. Similarly for using the Refined_Global aspect
   instead of the Global aspect and the Refined_Depends aspect instead
   of the Depends aspect. [Roughly speaking, the "contract" associated
   with a call is defined by using the Refined_* aspects of the callee
   instead of the corresponding non-refined aspects in the case where
   Refined_* aspect specifications are visible.]

.. _etu-refined_postcondition_aspects-vr:

.. centered:: **Examples**

These examples show the two ways in which the Refined_Post aspect is
useful:

1. To write a postcondition in terms of the full view of a private
   type.

2. To write a postcondition in terms of the constituents of a state
   abstraction.

In either case a postcondition may be strengthened by the Refined_Post
aspect by adding further constraints. The combination of these two
types of usage in a single package is not necessarily common but is
used here for brevity of the example.

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/stacks_1.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/stacks_1.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/stacks_2.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/stacks_2.adb
   :language: ada
   :linenos:

.. todo:: refined contract_cases.
          To be completed in a post-Release 1 version of this document.

.. Refined Precondition Aspect
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: The Refined_Pre aspect will not be implemented in Release 1 of the
     |SPARK| Toolset.  Its usefulness and exact semantics are still to be
     determined.

.. Text commented out until decision on Refined_Pre is finalised.
   A subprogram declared in the specification of a package may have a Refined
   Precondition aspect applied to its body or body stub. The Refined
   Precondition may be used to restate a precondition given on the declaration
   of a subprogram in terms of the full view of a private type or the
   ``constituents`` of a refined ``state_name``.

   The Refined Precondition aspect is introduced by an ``aspect_specification``
   where the ``aspect_mark`` is "Refined_Pre" and the ``aspect_definition``
   shall be a Boolean ``expression``.

   .. centered:: **Legality Rules**

   #. A Refined_Pre aspect may appear only on a body_stub (if one is present) or
      the body (if no stub is present) of subprogram if the subprogram is declared
      in the specification of a package, its abstract view. If the subprogram
      declaration in the visible part has no explicit precondition, a precondition
      of True is assumed for its abstract view.

   #. At the point of call of a subprogram, both its precondition and the
      expression of its Refined_Pre aspect shall evaluate to True.

   #. The same legality rules apply to a Refined Precondition as for
      a precondition.

   .. centered:: **Static Semantics**

   #. A Refined Precondition of a subprogram defines a *refinement*
      of the precondition of the subprogram.

   #. The static semantics are otherwise as for a precondition.

   .. centered:: **Dynamic Semantics**

   #. When a subprogram with a Refined Precondition is called; first
      the precondition is evaluated as defined in the Ada RM. If the
      precondition evaluates to True, then the Refined Precondition
      is evaluated. If either precondition or Refined Precondition
      do not evaluate to True an exception is raised.

   .. centered:: **Verification Rules**

   #. The precondition of the abstract view of the subprogram shall imply its
      Refined_Precondition.

.. _refined_external_states:

Refined External States
~~~~~~~~~~~~~~~~~~~~~~~

External state which is a state abstraction requires a refinement as does any
state abstraction. There are rules which govern refinement of a state
abstraction on to external states which are given in this section.

.. centered:: **Legality Rules**

.. _tu-fe-refined_external_states-01:

1. A state abstraction that is not specified as External shall not have
   ``constituents`` which are External states.

.. _tu-fe-refined_external_states-02:

2. An External state abstraction shall have at least one ``constituent``
   that is External state, or shall have a null refinement.

.. _tu-fe-refined_external_states-03:

3. An External state abstraction shall have each of the properties set to True
   which are True for any of its ``constituents``.

.. _tu-cbatu-refined_external_states-04:

4. Refined_Global aspects must respect the rules related to external
   properties of constituents which are external states given in
   :ref:`external_state` and :ref:`external_state-variables`.

.. _tu-cbatu-refined_external_states-05:

5. All other rules for Refined_State, Refined_Global and Refined_Depends aspect
   also apply.

.. _etu-refined_external_states-lr:

.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/externals.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/externals-temperature.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/externals-pressure.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/externals-main_display.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/externals-secondary_display.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/externals.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/hal.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/hal.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/main_hal.adb
   :language: ada
   :linenos:

Private Types and Private Extensions
------------------------------------

No extensions or restrictions.

Private Operations
~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Type Invariants
~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-type_invariants-01:

1. The ``aspect_specification`` Type_Invariant is not permitted in |SPARK|.

.. _etu-type_invariants:

.. todo:: Add support for type invariants in SPARK 2014.
          To be completed in a post-Release 1 version of this document.

..
   .. centered:: **Syntax**

   There is no additional syntax associated with type invariants.

   .. centered:: **Legality Rules**

   There are no additional legality rules associated with type invariants.

   .. note::
      (SB) This isn't quite right: there is a rule that invariant
         expressions can't read variables, but it isn't stated here.
            Fixup needed.

   .. centered:: **Static Semantics**

   There are no additional static semantics associated with type invariants.

   .. centered:: **Dynamic Semantics**

   There are no additional dynamic semantics associated with type invariants.

   .. centered:: **Verification Rules**

   #. The Ada 2012 RM lists places at which an invariant check is performed. In
      |SPARK|, we add the following places in order to guarantee that an instance
      of a type always respects its invariant at the point at which it is passed
      as an input parameter:

   * Before a call on any subprogram or entry that:

     * is explicitly declared within the immediate scope of type T (or
       by an instance of a generic unit, and the generic is declared
       within the immediate scope of type T), and

     * is visible outside the immediate scope of type T or overrides
       an operation that is visible outside the immediate scope of T,
       and

     * has one or more in out or in parameters with a part of type T.

     the check is performed on each such part of type T.
     [Note that these checks are only performed statically, and this does not create an
     obligation to extend the run-time checks performed in relation to type invariants.]

.. _default_initial_condition_aspect:

Default_Initial_Condition Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The Default_Initial_Condition aspect is introduced by an aspect_specification
   where the aspect_mark is Default_Initial_Condition. The aspect may be
   specified only as part of the aspect_specification of a
   ``private_type_declaration``.
   The ``aspect_definition``, if any, of such an aspect specification
   shall be either a null literal or a *Boolean_*\ ``expression``.

   The ``aspect_definition`` may be omitted; this is semantically
   equivalent to specifying a static *Boolean_*\ ``expression`` having the
   value True.

   An aspect specification of "null" indicates that the partial view of the
   type does not define full default initialization (see :ref:`declarations`).
   [The full view of the type might or might not define full default
   initialization.]

   Conversely, an aspect specification of a *Boolean_*\ ``expression`` indicates
   that the partial view of the type does define full default initialization.
   In this case, the completion of the private type shall define full
   default initialization. [Implementations may provide a mechanism for
   suppressing enforcement of this rule as described; the burden is then on
   the user to ensure that this does not result in undetected uses of
   uninitialized variables.]

   Unlike the null literal case, this case has associated dynamic semantics.
   The *Boolean_*\ ``expression`` (which might typically mention the current
   instance of the type, although this is not required) is an assertion
   which is checked (at run time) after any object of the given type (or of
   any descendant of the given type for which the specified aspect is
   inherited and not overridden), is "initialized by
   default" (see Ada RM 3.3.1).

   The *Boolean_*\ ``expression``, if any, causes freezing in the
   same way as the ``default_expression`` of a ``component_declaration``.
   [If the expresion is non-static, this means that the expression does not
   cause freezing where it occurs, but instead when an object of the type
   is initialized by default.]

   Default_Initial_Condition assertion is an assertion aspect, which means
   that it may be used in an Assertion_Policy pragma.

Deferred Constants
------------------

No extensions or restrictions.

Limited Types
-------------

No extensions or restrictions.

Assignment and Finalization
---------------------------

.. centered:: **Legality Rules**

.. _tu-assignment_and_finalization-01:

1. Controlled types are not permitted in |SPARK|.

.. _etu-assignment_and_finalization:

.. _elaboration_issues:

Elaboration Issues
------------------

|SPARK| imposes a set of restrictions which ensure that a
call to a subprogram cannot occur before the body of the
subprogram has been elaborated. The success of the runtime
elaboration check associated with a call is guaranteed by
these restrictions and so the verification condition associated with
such a check is trivially discharged. Similar restrictions
are imposed to prevent the reading of uninitialized library-level
variables during library unit elaboration, and to prevent
instantiation of a generic before its body has been elaborated.
Finally, restrictions are imposed in order to ensure that the
Initial_Condition (and Initializes aspect) of a library level package
can be meaningfully used.

These restrictions are described in this section. Because all of these
elaboration-related issues are treated similarly, they are
discussed together in one section.

Note that throughout this section an implicit call
(e.g., one associated with default initialization of an
object or with a defaulted parameter in a call) is treated
in the same way as an explicit call, and an explicit call
which is unevaluated at the point where it (textually) occurs is
ignored at that point (but is not ignored later at a point
where it is evaluated). This is similar to the treatment of
expression evaluation in Ada's freezing rules.
This same principle applies to the rules about reading
global variables discussed later in this section.

.. centered:: **Static Semantics**

.. _tu-nt-elaboration_issues-01:

1. A call which occurs within the same compilation_unit as the subprogram_body
   of the callee is said to be an *intra-compilation_unit call*.

.. _tu-nt-elaboration_issues-02:

2. A construct (specifically, a call to a subprogram or a read or write
   of a variable) which occurs in elaboration code for a library level package
   is said to be *executable during elaboration*. If a subprogram call is
   executable during elaboration and the callee's body occurs in the same
   compilation_unit as the call, then any constructs occurring within that body
   are also executable during elaboration. [If a construct is executable during
   elaboration, this means that it could be executed during the elaboration of
   the enclosing library unit and is subject to certain restrictions described
   below.]

   For a given library unit L1 and a given distinct library unit's
   spec or body L2, the elaboration of the body of L1 is said to be
   *known to precede* the elaboration of L2 if either:

   a. L2 references L1 in an Elaborate_All pragma; or

   b. L1's Elaborate_Body aspect is True; or

   c. L1 does not require a body (the terminology is a little odd in this
      case because L1 has no body); or

   d. L1 is preelaborable and L2's library unit is not.

   [If Elaborate pragmas were in |SPARK| then this list would also include the
   case where L2 references L1 in an Elaborate pragma, but they aren't so it
   doesn't - see below.]

.. _etu-elaboration_issues-ss:

.. centered:: **Legality Rules**

.. _tu-nt-elaboration_issues-03:

3. |SPARK| requires that an intra-compilation_unit call which is
   executable during elaboration shall occur after a certain point in the unit
   (described below) where the subprogram's completion is known to have been
   elaborated. The portion of the unit following this point and extending
   to the start of the completion of the subprogram is defined to
   be the *early call region* for the subprogram. An intra-compilation_unit
   call which is executable during elaboration and which occurs (statically)
   before the start of the completion of the callee shall occur within the
   early call region of the callee.

.. _tu-nt-elaboration_issues-04:

4. The start of the early call region is obtained by starting at the
   subprogram's completion (typically a subprogram_body) and then traversing
   the preceding constructs in reverse elaboration order until
   a non-preelaborable statement/declarative_item/pragma
   is encountered. The early call region starts immediately after this
   non-preelaborable construct (or at the beginning of the enclosing block
   (or library unit package spec or body) if no such non-preelaborable construct
   is found).

   [The idea here is that once elaboration reaches the start of the early call
   region, there will be no further expression evaluation or statement
   execution (and, in particular, no further calls) before the subprogram_body
   has been elaborated because all elaborable constructs that will be elaborated
   in that interval will be preelaborable. Hence, any calls that occur
   statically after this point cannot occur dynamically before the elaboration
   of the subprogram body.]

   [These rules allow this example

   .. code-block:: ada

    package body Pkg is
       ...
       procedure P;
       procedure Q;
       X : Integer := Some_Function_Call; -- not preelaborable
       procedure P is ... if Blap then Q; end if; ... end P;
       procedure Q is ... if Blaq then P; end if; ... end Q;
    begin
       P;
    end;

   even though the call to Q precedes the body of Q. The early call region
   for either P or Q begins immediately after the declaration of X.
   Note that because the call to P is executable during elaboration, so
   is the call to Q.]


.. todo:: It would be possible to relax this rule by defining
          a less-restrictive notion of preelaborability which allows, for example,

          .. code-block:: ada

             type Rec is record F1, F2 : Integer; end record;
             X : constant Rec := (123, 456);  -- not preelaborable

          while still disallowing the things that need to be disallowed and
          then defining the above rules in terms of this new notion instead of
          preelaborability. The only disadvantage of this is the added complexity
          of defining this new notion.

          To be considered post release 1.

.. _tu-nt-elaboration_issues-05:

5. For purposes of the above rules, a subprogram completed by a
   renaming-as-body is treated as though it were a wrapper
   which calls the renamed subprogram (as described in Ada RM 8.5.4(7.1/1)).
   [The notional "call" occuring in this wrapper is then subject to the
   above rules, like any other call.]

.. _tu-nt-elaboration_issues-06:

6. If an instance of a generic occurs in the same compilation_unit as the
   body of the generic, the body must precede the instance.

   [If this rule
   were only needed in order to avoid elaboration check failures, a similar
   rule to the rule for calls could be defined. This stricter rule is used
   in order to avoid having to cope with use-before-definition, as in

   .. code-block:: ada

     generic
     package G is
        ...
     end G;

     procedure Proc is
        package I is new G; -- expansion of I includes references to X
     begin ... ; end;

     X : Integer;

     package body G is
        ... <uses of X> ...
     end G;

   This stricter rule applies even if the declaration of the instantiation
   is not "executable during elaboration"].

.. _tu-nt-elaboration_issues-07:

   7. In the case of a dispatching call, the subprogram_body mentioned
   in the above rules is that (if any) of the statically denoted callee.

.. _tu-nt-elaboration_issues-08:

   8. The first freezing point of a tagged type shall occur within the
   early call region of each of its overriding primitive operations.

   [This rule is needed to prevent a dispatching call before the body
   of the (dynamic, not static) callee has been elaborated.
   The idea here is that after the freezing point it would be
   possible to declare an object of the type and then use it as a controlling
   operand in a dispatching call to a primitive operation of an ancestor type.
   No analysis is performed to identify scenarios where this is not the case,
   so conservative rules are adopted.]

   [Ada ensures that the freezing point of a tagged type will always occur after
   both the completion of the type and the declarations of each of its primitive
   subprograms; the freezing point of any type will occur before the
   declaration of any objects of the type or the evaluation of any
   expressions of the type. This is typically all that one needs to know about
   freezing points in order to understand how the above rule applies to a
   particular example.]

.. _tu-nt-elaboration_issues-09:

9. For purposes of defining the early call region, the specification and body
   of a library unit package whose Elaborate_Body aspect is True are treated as
   if they both belonged to some enclosing declaration list with the body
   immediately following the specification. This means that the early call
   region in which a call is permitted can span the specification/body boundary.

   This is important for tagged type declarations.

.. _tu-nt-elaboration_issues-10:

10. For the inter-compilation_unit case, |SPARK| enforces the following static
    elaboration order rule:

    a. If a unit has elaboration code that can directly or indirectly
       make a call to a subprogram in a with'd unit, or instantiate a
       generic unit in a with'd unit, then if the with'd unit does
       not have pragma Pure or Preelaborate, then the client should
       have a pragma Elaborate_All for the with'd unit.

    b. For each call that is executable during elaboration for a given
       library unit package spec or body, there are two cases: it is
       (statically) a call to a subprogram whose body is in the
       current compilation_unit, or it is not. In the latter case, we
       require an Elaborate_All pragma as described above (the pragma
       must be given explicitly; it is not supplied implicitly).

.. _tu-nt-elaboration_issues-11:

11. For an instantiation of a generic which does not occur in the same
    compilation unit as the generic body, the rules are as described
    in the GNAT Pro User's Guide passage quoted above.

.. _tu-nt-elaboration_issues-12:

12. Elaborate pragmas are not in |SPARK|.
    [This rule is needed only because of a detail of GNAT's static
    elaboration model described in section C.7 of the GNAT Pro
    User's Guide. GNAT allows using a Elaborate pragma instead of
    an Elaborate_All pragma at some points where the latter is needed
    to ensure the absence of access-before-elaboration problems; this is
    too permissive for |SPARK|, so Elaborate pragmas are disallowed.
    This rule may be relaxed at some point in the future.]

.. _etu-elaboration_issues-lr:

[These rules correctly prohibit the following example:

.. code-block:: ada

   package P is
      function F return Boolean;
      Flag : Boolean := F; -- would fail elaboration checks
   end; --]

.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/times_2.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/intra_unit_elaboration_order_examples.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/intra_unit_elaboration_order_examples.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/inter_1.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/inter_1.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/inter_2.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/inter_2.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/inter_unit_elaboration_examples.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/inter_unit_elaboration_examples.adb
   :language: ada
   :linenos:

Use of Initial_Condition and Initializes Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Static Semantics**

To ensure the correct semantics of the Initializes and Initial_Condition
aspects, when applied to library units, language restrictions (described below)
are imposed in |SPARK| which have the following consequences:

.. _tu-cbatu-use_of_initial_condition_and_initializes_aspects-01:

1. During the elaboration of a library unit package (spec or body),
   library-level variables declared outside of that package cannot
   be modified and library-level variables declared outside of that
   package can only be read if

   a. the variable (or its state abstraction) is mentioned in the
      Initializes aspect of its enclosing package (from
      :ref:`initializes_aspect`); and

   b. either the variable is declared and initialized during the
      elaboration of the specification of its enclosing library unit package
      or the elaboration of the body of that library unit is
      known to precede the elaboration of the spec or body which reads
      the variable.

.. _tu-cbatu-use_of_initial_condition_and_initializes_aspects-02:

2. From the end of the elaboration of a library package's body to the
   invocation of the main program (i.e., during subsequent library
   unit elaboration), variables declared in the package (and
   constituents of state abstractions declared in the package) remain
   unchanged. The Initial_Condition aspect is an assertion which is
   checked at the end of the elaboration of a package body (but occurs
   textually in the package spec see :ref:`initial_condition_aspect`).
   The initial condition of a library level package will remain true
   from this point until the invocation of the main subprogram
   (because none of the inputs used in computing the condition can
   change during this interval).  This means that a package's initial
   condition can be assumed to be true both upon entry to the main
   subprogram itself and during elaboration of any other unit (spec or body)
   whose elaboration is known to follow that of the body of the package
   (see preceding definition of "known to precede"; *known to follow*
   is, by definition, the inverse relationship). An Initial_Condition which
   depends on no variable inputs can also be assumed to be true throughout
   the execution of the main subprogram.

.. _tu-cbatu-use_of_initial_condition_and_initializes_aspects-03:

3. If a package's Initializes aspect mentions a state abstraction
   whose refinement includes constituents declared outside of that
   package, then the elaboration of bodies of the enclosing packages
   of those constituents will precede the elaboration of the body of
   the package declaring the abstraction (as a consequence of the
   rules given in :ref:`elaboration_issues`). The idea here is that
   all constituents of a state abstraction whose initialization has
   been promised are in fact initialized by the end of the elaboration
   of the body of the abstraction's unit - we don't have to wait for
   the elaboration of other units (e.g., private children) which
   contribute to the abstraction.

.. _etu-use_of_initial_condition_and_initializes_aspects-ss:

.. centered:: **Verification Rules**

.. _tu-nt-use_of_initial_condition_and_initializes_aspects-04:

4. If a read of a variable (or state abstraction, in the case of a
   call to a subprogram which takes an abstraction as an input) declared in
   another library unit is executable during elaboration (as defined above),
   then either

   * the entity being read shall be a variable (i.e., not a state abstraction)
     and shall be initialized (perhaps by default) during the elaboration of
     its enclosing library unit specification; or

   * the elaboration of the compilation unit which performs the read
     shall be known to follow that of the body of the unit declaring
     the variable or state abstraction.

   In either case, the variable or state abstraction shall be specified
   as being initialized in the Initializes aspect of the declaring package.
   [This is needed to ensure that the variable has been initialized at the
   time of the read.]

5. If a variable is declared (immediately or not) within a library unit
   package specification, and if that variable is initialized (perhaps
   by default) during the elaboration of that specification, and if any
   part of that variable is also assigned to during the elaboration of
   the corresponding library unit package body, then that library unit's
   Elaborate_Body aspect shall be True. [This is needed to ensure that
   the variable remains unread between the elaboration of the
   specification and of the body of its enclosing library unit.]

.. _tu-nt-use_of_initial_condition_and_initializes_aspects-05:

5. The elaboration of a package's specification and body shall not
   write to a variable (or state abstraction, in the case of a call to
   a procedure which takes an abstraction as in output) declared
   outside of the package. The output associated with a read of an
   external state with the property Effective_Reads is permitted.
   [This rule applies to all packages: library level or not,
   instantiations or not.] The inputs and outputs of a package's
   elaboration (including the elaboration of any private descendants
   of a library unit package) shall be as described in the Initializes
   aspect of the package.

.. _etu-use_of_initial_condition_and_initializes_aspects-vr:

.. centered:: **Legality Rules**

.. _tu-nt-use_of_initial_condition_and_initializes_aspects-06:

6. The elaboration of a package body shall be known to follow the
   elaboration of the body of each of the
   library units [(typically private children)] which provide
   constituents for a state abstraction denoted in the Initializes
   aspect of the given package.

.. _etu-use_of_initial_condition_and_initializes_aspects-lr:

.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/p.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/p.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/initialization_and_elaboration.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/initialization_and_elaboration-private_child.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/initialization_and_elaboration.adb
   :language: ada
   :linenos:
