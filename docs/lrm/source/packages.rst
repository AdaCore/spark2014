Packages
========

.. centered:: **Verification Rules**


1. The elaboration of a package shall not update, directly or
   indirectly, a reachable element of a variable that is not declared
   immediately within the package. [Roughly speaking, this means that
   the outputs of the notional spec and body elaboration subprograms
   shall all be objects declared immediately within the package.]


2. The elaboration of a package declaration or body shall not leave any
   object in the Moved state unless the object was already in the Moved
   state at the start of that elaboration.


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


1. The visible state of a package P consists of:

   * any variables, or *constants with variable inputs*, declared immediately
     within the visible part of package P; and

   * the state abstractions declared by the Abstract_State aspect specification
     (if any) of package P; and

   * the visible state of any packages declared immediately within the visible
     part of package P.

2. The hidden state of a package P consists of:

   * any variables, or *constants with variable inputs*, declared immediately
     in the private part or body of P; and

   * the visible state of any packages declared immediately within
     the private part or body of P.

3. The preceding two rules notwithstanding, an object or state abstraction
   whose Part_Of aspect refers to a task or protected unit is not (directly)
   part of the visible state or hidden state of any package (see section
   :ref:`tasks-and-synchronization`).


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

Each read or update of an external state might be significant, for
instance reading or writing a stream of characters to a file, or
individual reads or writes might not be significant, for instance
reading a temperature from a device or writing the same value to a
lamp driver or display. |SPARK| provides a mechanism to indicate
whether a read or write is always significant.

A type is said to be *effectively volatile* if it is either
a volatile type, an array type whose Volatile_Component
aspect is True, an array type whose component type is
effectively volatile, a protected type, or a descendant of
the type Ada.Synchronous_Task_Control.Suspension_Object.

A nonvolatile protected type is said to be *nonvolatile during a protected
action* if none of its subcomponent types are effectively volatile. [In other
words, if the only reason that the protected type is effectively volatile
is because it is protected.]

An *effectively volatile object* is a volatile object for which
the property No_Caching (see below) is False, or an object
of an effectively volatile type. There are two exceptions to this rule:

  * the current instance of a protected unit whose (protected) type is
    nonvolatile during a protected action is, by definition, not an
    effectively volatile object. [This exception reflects the fact that
    the current instance cannot be referenced in contexts where
    unsynchronized updates are possible. This means, for example, that the
    Global aspect of a nonvolatile function which is declared inside of a
    protected operation may reference the current instance of the protected
    unit.]

  * a constant object associated with the evaluation of a function
    call, an aggregate, or a type conversion is, by definition,
    not an effectively volatile object. [See Ada RM 4.6 for the rules about
    when a type conversion introduces a new object; in cases where it is
    unspecified whether a new object is created, we assume (for purposes
    of the rules in this section) that no new object is created].
  
External state is an effectively volatile object or a state abstraction which
represents one or more effectively volatile objects (or it could be a null state
abstraction; see :ref:`abstract-state-aspect`). [The term "external" does
not necessarily mean that this state is accessed outside of
the SPARK portion of the program (although it might be); it refers to the
state being potentially visible to multiple tasks (as well as to the outside
world), so that it is externally visible from the perspective of any one task.]

Four Boolean valued *properties* of external states that may be specified are
defined:

  * Async_Readers - a component of the system external to the program might
    read/consume a value written to an external state.

  * Async_Writers - a component of the system external to the program might
    update the value of an external state.

  * Effective_Writes - every update of the external state is significant.

  * Effective_Reads - every read of the external state is significant.

These properties may be specified for an effectively volatile object
as Boolean aspects or as external properties of an external state abstraction.

A fifth property No_Caching can be specified on a volatile object of a
non-effectively volatile type, to express that such a variable can be analyzed
as not volatile in SPARK, but that the compiler should not cache its value
between accesses to the object (e.g. as a defense against fault injection).

The Boolean aspect Volatile_Function may be specified as part of the
(explicit) initial declaration of a function. A function whose
Volatile_Function aspect is True is said to be a *volatile function*.
Volatile functions can read volatile objects; nonvolatile functions
cannot. However note that the rule that a function must not have any
output other than its result still applies; in effect this bans
a volatile function from reading an object with Effective_Reads => True.
As a result, calling a volatile function is considered as having an effect,
and such calls are only allowed in certain contexts
(see :ref:`external_state-variables`).
A protected function is also defined to be a *volatile function*, as is
an instance of Unchecked_Conversion where one or both of the actual
Source and Target types are effectively volatile types.
[Unlike nonvolatile functions, two calls to a volatile function with all
inputs equal need not return the same result.]

A protected function whose corresponding protected type is
nonvolatile during a protected action and whose Volatile_Function aspect is
False is said to be *nonvolatile for internal calls*.

.. centered:: **Legality Rules**


1. If an external state is declared without any of the external
   properties specified then all of the external properties
   [i.e. except No_Caching] default to a value of True.


2. If just the name of the property is given then its value defaults
   to True [for instance Async_Readers defaults to Async_Readers =>
   True].


3. A property may be explicitly given the value False [for instance Async_Readers => False].


4. If any one property is explicitly defined, all undefined properties default to a value of False.


5. The expression defining the Boolean valued property shall be static.


6. Only the following combinations of properties are valid:

   ============= ============= ================ =============== ==========
   Async_Readers Async_Writers Effective_Writes Effective_Reads No_Caching
   ============= ============= ================ =============== ==========
   True          --            True             --              --
   --            True          --               True            --
   True          --            --               --              --
   --            True          --               --              --
   True          True          True             --              --
   True          True          --               True            --
   True          True          --               --              --
   True          True          True             True            --
   --            --            --               --              True
   ============= ============= ================ =============== ==========

   [Another way of expressing this rule is that No_Caching is incompatible
   with the four external properties, that Effective_Reads can
   only be True if Async_Writers is True and Effective_Writes can only
   be True if Async_Readers is True.]


.. centered:: **Static Semantics**


7. Every update of an external state is considered to be read by
   some external reader if Async_Readers => True.


8. Each successive read of an external state might have a different
   value [written by some external writer] if Async_Writers => True.


9. If Effective_Writes => True, then every value written to the
   external state is significant. [For instance writing a sequence of
   values to a port.]


10. If Effective_Reads => True, then every value read from the
    external state is significant. [For example a value read from a
    port might be used in determining how the next value is
    processed.]


11. Each update of an external state has no external effect if both
    Async_Readers => False and Effective_Writes => False.


12. Each successive read of an external state will result in the last
    value explicitly written [by the program] if Async_Writers => False.


13. Every explicit update of an external state might affect the next value
    read from the external state even if Async_Writers => True.


14. An external state which has the property Async_Writers => True
    need not be initialized before being read although explicit
    initialization is permitted. [The external state might be
    initialized by an external writer.]


15. A subprogram whose Volatile_Function aspect is True shall not override
    an inherited primitive operation of a tagged type whose
    Volatile_Function aspect is False. [The reverse is allowed.]


16. A protected object has at least the properties Async_Writers => True
    and Async_Readers => True. If and only if it has at least one Part_Of
    component with Effective_Writes => True or Effective_Reads => True,
    then the protected object also carries this property. [This is
    particularly relevant if a protected object is a constituent of an
    external state, or if a protected object is an input of a volatile
    function.]


.. _external_state-variables:

External State - Variables and Types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In Ada interfacing to an external device or subsystem normally entails
using one or more effectively volatile objects to ensure that writes and reads
to the device are not optimized by the compiler into internal register
reads and writes.

|SPARK| refines the specification of volatility by introducing four new Boolean
aspects which may be applied only to effectively volatile objects or to
volatile types. The aspects
may be specified in the aspect specification of an object declaration
(this effectively excludes volatile objects that are formal parameters, but
allows such aspect specifications for generic formal objects) or
of a type declaration (including a formal_type_declaration).

The new aspects are:

  * Async_Readers - as described in :ref:`external_state`.

  * Async_Writers - as described in :ref:`external_state`.

  * Effective_Reads - as described in :ref:`external_state`.

  * Effective_Writes - as described in :ref:`external_state`.

These four aspects are said to be the *volatility refinement* aspects.
Ada's notion of volatility corresponds to the case where all four
aspects are True. Specifying a volatility
refinement aspect value of False for an object or type
grants permission for the |SPARK| implementation to make additional
assumptions about how the object in question (or, respectively,
about how an object of the type in question) is accessed;
it is the responsibility of the user to ensure that these assumptions hold.
In contrast, specifying a value of True imposes no such obligation on the user.

For example, consider

.. code-block:: ada

   X : Integer with Volatile, Async_Readers => True, Async_Writers => False,
                              Effective_Reads => True, Effective_Writes => True;
   ...
   procedure Proc with ... is
     Y : Integer;
   begin
     X := 0;
     Y := X;
     pragma Assert (Y = 0);
   end Proc;

The verification condition associated with the assertion can be
successfully discharged but this success depends on the
Async_Writers aspect specification.

The volatility refinement aspects of types (as opposed to
those of objects) are type related representation aspects.
The value of a given volatility refinement aspect of a volatile type
is determined as follows:

  * if the aspect's value is explicitly specified, then it is the
    specified value;

  * otherwise, if the type is a derived type whose parent type is volatile then
    the aspect value is inherited from the parent type;

  * otherwise, if at least one other volatility refinement aspect is
    explicitly specified for the type then the given aspect of the type
    is implicitly specified to be False;

  * otherwise, the given aspect of the type is implicitly specified to be True.

[This is similar to the rules for external state abstractions, except that
there is no notion of inheritance in that case.]

The value of a given volatility refinement aspect of an effectively
volatile object is determined as follows:

  * if the object is a reachable element of a stand-alone object or
    of a formal parameter but is not itself such an object, then it is
    the value of the given aspect of that enclosing or owning object
    (see section :ref:`subprogram-declarations` for definitions of
    "reachable element" and "owning object").

  * otherwise, if the object is declared by an object declaration and the
    given aspect is explicitly specified for the object declaration then
    it is the specified value;

  * otherwise, if the object is declared by an object declaration and then
    at least one other volatility refinement aspect is explicitly specified
    for the object declaration then the given aspect of the object is
    implicitly specified to be False;

  * otherwise, it is the value of the given aspect of the type of the object.

Given two entities (each either an object or a type) E1 and E2, E1 is said to
be *compatible with respect to volatility* with E2 if

   * E1 is not effectively volatile; or

   * both E1 and E2 are effectively volatile and each of the four
     volatility refinement aspects is either False for E1 or
     True for E2.
   
.. centered:: **Legality Rules**


1. Any specified value for a volatility refinement aspect shall be static.

   [If a volatility refinement aspect of a derived type is inherited from an
   ancestor type and has the boolean value True, the inherited value shall
   not be overridden to have the value False for the derived type. This
   follows from the corresponding Ada RM 13.1.1 rule and is stated here only
   to clarify the point that there is no exception to that rule for volatility
   refinement aspects. This is consistent with Ada's treatment of the Volatile
   aspect.]

2. The value of a volatility refinement aspect shall only be specified
   for an effectively volatile stand-alone object or for an effectively
   volatile type (which may be a formal type).
   [A formal parameter is not a stand-alone object; see Ada RM 3.3.1 .]
   If specified for a stand-alone object, the declared object shall be
   compatible with respect to volatility with its type.

3. The declaration of an effectively volatile stand-alone object or type
   shall be a library-level declaration. [In particular, it shall not be
   declared within a subprogram.]

4. A constant object (other than a formal parameter of mode **in**)
   shall not be effectively volatile.

5. An effectively volatile type other than a protected type
   shall not have a discriminated part.

6. A component type of a composite type shall be compatible with
   respect to volatility with the composite type. Similarly, the
   [full view of] the designated type of a named nonderived access type
   shall be compatible with respect to volatility with the access type.

7. In a generic instantiation, the actual parameter corresponding to a
   formal type or formal object parameter shall be compatible with
   respect to volatility with the corresponding formal parameter.

8. A ``global_item`` of a nonvolatile function, or of a function which
   is nonvolatile for internal calls, shall not denote either
   an effectively volatile object or an external state abstraction.

9. A formal parameter (or result) of a nonvolatile function, or of a
    function which is nonvolatile for internal calls, shall not be of
    an effectively volatile type. [For a protected function, this rule
    does not apply to the notional parameter denoting the current instance of
    the associated protected unit described in section :ref:`global-aspects`.]

10. Contrary to the general |SPARK| rule that expression evaluation
    cannot have side effects, a read of an effectively volatile object with
    the properties Async_Writers or Effective_Reads set to True is
    considered to have an effect when read. To reconcile this
    discrepancy, a name denoting such an object shall only occur in
    a *non-interfering context*. A name occurs in a non-interfering
    context if it is:

   * the name on the left-hand side of an assignment statement; or

   * the [right-hand side] expression of an assignment statement; or

   * the expression of an initialization expression of an object declaration; or

   * the ``object_name`` of an ``object_renaming_declaration``; or

   * the actual parameter in a call to an instance of Unchecked_Conversion
     whose result is renamed [in an object renaming declaration]; or

   * an actual parameter in a call for which the corresponding
     formal parameter is of a non-scalar effectively volatile type; or

   * the (protected) prefix of a name denoting a protected operation; or

   * the return expression of a ``simple_return_statement`` which applies
     to a volatile function; or

   * the initial value expression of the ``extended_return_object_declaration``
     of an ``extended_return_statement`` which applies to a
     volatile function; or

   * the prefix of a ``slice``, ``selected_component``, ``indexed_component``,
     or ``attribute_reference`` which is itself a name occurring in a
     non-interfering context; or

   * the prefix of an ``attribute_reference`` whose ``attribute_designator`` is
     either Alignment, Component_Size, First, First_Bit, Last, Last_Bit,
     Length, Position, Size, or Storage_Size; or

   * the expression of a type conversion occurring in a non-interfering context; or

   * the expression in a ``delay_statement``.

   [The attributes listed above all have the property that when their prefix
   denotes an object, evaluation of the attribute does not involve the
   evaluation of any part ot the object.]

   The same restrictions also apply to a call to a volatile function
   (except not in the case of an internal call to a protected function
   which is nonvolatile for internal calls)
   and to the evaluation of any attribute which is defined to introduce
   an implicit dependency on a volatile state abstraction [(these are
   the Callable, Caller, Count, and Terminated attributes; see section
   :ref:`tasks-and-synchronization`)]. [An internal call to a protected
   function is treated like a call to a nonvolatile function if the
   function's Volatile_Function aspect is False.]


.. centered:: **Dynamic Semantics**

11. There are no dynamic semantics associated with these aspects.

.. centered:: **Verification Rules**

12. An effectively volatile formal parameter of mode **out** shall not be read,
    even after it has been updated. [This is because the
    Async_Writers aspect of the parameter is True].

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

If immediately within a package body, for example, a nested package is declared,
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


::

  abstract_state_list      ::= null
                             | state_name_with_options
                             | ( state_name_with_options { , state_name_with_options } )
  state_name_with_options  ::= state_name
                             | ( state_name with option_list )
  option_list              ::= option { , option }
  option                   ::= simple_option
                             | name_value_option
  simple_option            ::= Ghost | Synchronous
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


.. centered:: **Legality Rules**


1. An ``option`` shall not be repeated within a single ``option_list``.


2. If External is specified in an ``option_list`` then there shall be at most
   one occurrence of each of Async_Readers, Async_Writers, Effective_Writes
   and Effective_Reads.


3. If an ``option_list`` contains one or more ``name_value_option`` items
   then they shall be the final options in the list.
   [This eliminates the possibility of a positional
   association following a named association in the property list.]


4. A package_declaration or generic_package_declaration that contains a
   non-null Abstract_State aspect shall have a completion (i.e., a body).

   [Ada RM 7.1's rule defining when a package "requires a completion"
   is unaffected by the presence of an Abstract_State aspect
   specification; such an aspect spec does not cause a
   package to "require a completion".
   This rule therefore implies that if an Abstract_State aspect
   specification occurs anywhere within the specification of a library
   unit package or generic package, then that library unit is
   going to have to contain a basic_declarative_item that requires
   a completion (or have an Elaborate_Body pragma) because otherwise
   it would be impossible to  simultaneously satisfy this rule and Ada's
   rule that a library unit cannot have a package body unless it is required
   (Ada RM 7.2(4)). One could imagine a simpler rule that an
   Abstract_State aspect specification causes a package to "require a
   completion", but we want a SPARK program with its SPARK aspects removed
   (or ignored) to remain a legal Ada program.]


.. centered:: **Static Semantics**


5. Each ``state_name`` occurring in an Abstract_State aspect
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


6. A **null** ``abstract_state_list`` specifies that a package contains no
   hidden state.


7. An External state abstraction is one declared with an ``option_list``
   that includes the External ``option`` (see :ref:`external_state`).


8. If a state abstraction which is declared with an ``option_list`` that
   includes a Part_Of ``name_value_option`` whose ``name`` denote a state
   abstraction, this indicates that it is a constituent (see
   :ref:`state_refinement`) of the denoted state abstraction.
   [Alternatively, the name may denote a task or protected unit (see section
   :ref:`tasks-and-synchronization`).]


9. A state abstraction for which the ``simple_option`` Ghost is
   specified is said to be a ghost state abstraction. A state
   abstraction for which the ``simple_option`` Synchronous is
   specified is said to be a synchronized state abstraction.
   [The option name "Synchronous" is used instead of "Synchronized"
   to avoid unnecessary complications associated with the use of an
   Ada reserved word.] Every synchronized state abstraction is
   also (by definition) an external state abstraction. A synchronized
   state abstraction for which the ``simple_option`` External is
   not (explicitly) specified has (by definition) its Async_Readers
   and Async_Writers aspects specified to be True and its
   Effective_Writes and Effective_Reads aspects specified to be False.


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Abstract_State aspect.

.. centered:: **Verification Rules**

There are no verification rules associated with the Abstract_State aspect.

.. centered:: **Examples**

.. code-block:: ada
   :linenos:

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

.. code-block:: ada
   :linenos:

   package X
     with Abstract_State => (A,
                             B,
                             (C with External => (Async_Writers,
                                                  Effective_Reads => False))
     --  Three abstract state names are declared A, B & C.
     --  A and B are internal abstract states.
     --  C is specified as external state which is an external input.
   is
      ...
   end X;

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


::

  initialization_spec ::= initialization_list
                        | null

  initialization_list ::= initialization_item
                        | ( initialization_item { , initialization_item } )

  initialization_item ::= name [ => input_list]


.. centered:: **Legality Rules**


1. An Initializes aspect shall only appear in the ``aspect_specification`` of a
   ``package_specification``.


2. The ``name`` of each ``initialization_item`` in the Initializes aspect
   definition for a package shall denote a state abstraction of the package
   or an entire object declared immediately within the visible part of the
   package.
   [For purposes of this rule, formal parameters of a generic package
   are not considered to be "declared in the package".]


3. Each ``name`` in the ``input_list`` shall denote an object, or a state
   abstraction but shall not denote an entity declared in the package with
   the ``aspect_specification`` containing the Initializes aspect.


4. Each entity in a single ``input_list`` shall be distinct.


5. An ``initialization_item`` with a **null** ``input_list`` is
   equivalent to the same ``initialization_item`` without an ``input_list``.
   [That is Initializes => (A => **null**) is equivalent to Initializes => A.]


.. centered:: **Static Semantics**


6. The Initializes aspect of a package has visibility of the declarations
   occurring immediately within the visible part of the package.


7. The Initializes aspect of a package specification asserts which
   state abstractions and visible variables of the package are initialized
   by the elaboration of the package, both its specification and body, and
   any units which have state abstractions or variable declarations that are
   part (constituents) of a state abstraction declared by the package.
   [A package with a **null** ``initialization_list``, or no Initializes aspect
   does not initialize any of its state abstractions or variables.]


8. An ``initialization_item`` shall have an ``input_list`` if and
   only if its initialization is dependent on visible variables and
   state abstractions not declared within the package containing the
   Initializes aspect.  Then the ``names`` in the ``input_list`` shall
   denote variables and state abstractions which are used in
   determining the initial value of the state abstraction or variable
   denoted by the ``name`` of the ``initialization_item`` but are not
   constituents of the state abstraction.


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Initializes aspect.

.. centered:: **Verification Rules**


9. If the Initializes aspect is specified for a package, then after
   the body (which may be implicit if the package has no explicit
   body) has completed its elaboration, every (entire) variable and
   state abstraction denoted by a ``name`` in the Initializes aspect
   shall be initialized. A state abstraction is said to be
   initialized if all of its constituents are initialized. An entire
   variable is initialized if all of its components are initialized.
   Other parts of the visible state of the package shall not be
   initialized.


10. If an ``initialization_item`` has an ``input_list`` then the
    variables and state abstractions denoted in the input list shall
    be used in determining the initialized value of the entity denoted
    by the ``name`` of the ``initialization_item``.


11. All variables and state abstractions which are not declared within
    the package but are used in the initialization of an
    ``initialization_item`` shall appear in an ``input_list`` of the
    ``initialization_item``.


12. Any ``initialization_item`` that is a constant shall be a *constant
    with variable input*. Any entity in an ``input_list`` that is a
    constant shall be a parameter or *constant with variable input*.


[Note: these rules allow a variable or state abstraction to be
initialized by the elaboration of a package but not be denoted in an
Initializes aspect.  In such a case the analysis tools will treat the
variable or state abstraction as uninitialized when analyzing clients
of the package.]


.. centered:: **Examples**

.. code-block:: ada
   :linenos:

   package Q
     with Abstract_State => State,        -- Declaration of abstract state name State
          Initializes    => (State,       -- Indicates that State
                             Visible_Var) -- and Visible_Var will be initialized
                                          -- during the elaboration of Q.
   is
      Visible_Var : Integer;
      ...
   end Q;

.. code-block:: ada
   :linenos:

   with Q;
   package R
     with Abstract_State => S1,                   -- Declaration of abstract state name S1
          Initializes    => (S1 => Q.State,       -- Indicates that S1 will be initialized
                                                  -- dependent on the value of Q.State
                             X  => Q.Visible_Var) -- and X dependent on Q.Visible_Var
                                                  -- during the elaboration of R.
   is
      X : Integer := Q.Visible_Var;
      ...
   end R;

.. code-block:: ada
   :linenos:

   package Y
     with Abstract_State => (A, B, (C with External => (Async_Writers, Effective_Reads))),
          --  Three abstract state names are declared A, B & C
          Initializes    => A
          --  A is initialized during the elaboration of Y.
          --  C is specified as external state with Async_Writers
          --  and need not be explicitly initialized.
          --  B is not initialized.
   is
      ...
   end Y;

.. code-block:: ada
   :linenos:

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


1. An Initial_Condition aspect shall only be placed in an ``aspect_specification``
   of a ``package_specification``.


.. centered:: **Static Semantics**


2. An Initial_Condition aspect is an assertion and behaves as a
   postcondition for the elaboration of both the specification and
   body of a package. If present on a package, then its assertion
   expression defines properties (a predicate) of the state of the
   package which can be assumed to be true immediately following the
   elaboration of the package. [The expression of the
   Initial_Condition cannot denote a state abstraction or hidden
   state. This means that to express properties of hidden state,
   functions declared in the visible part acting on the state
   abstractions of the package must be used.]


.. centered:: **Dynamic Semantics**


3. With respect to dynamic semantics, specifying a given expression as
   the Initial_Condition aspect of a package is equivalent to
   specifying that expression as the argument of an Assert pragma
   occurring at the end of the (possibly implicit) statement list of
   the (possibly implicit) body of the package. [This equivalence
   includes all interactions with pragma Assertion_Policy but does not
   extend to matters of static semantics, such as name resolution.] An
   Initial_Condition expression does not cause freezing until the
   point where it is evaluated [, at which point everything that it
   might freeze has already been frozen].


.. centered:: **Verification Rules**


4. [The Initial_Condition aspect gives a verification condition to show that the
   implementation of the ``package_specification`` and its body satisfy the
   predicate given in the Initial_Condition aspect.]


5. Each variable or indirectly referenced state abstraction in an
   Initial_Condition aspect of a package Q which is declared
   immediately within the visible part of Q shall be initialized
   during the elaboration of Q and be denoted by a ``name`` of an
   ``initialization_item`` of the Initializes aspect of Q.


.. centered:: **Examples**

.. code-block:: ada
   :linenos:

    package Q
       with Abstract_State    => State,    -- Declaration of abstract state name State
            Initializes       => State,    -- State will be initialized during elaboration
            Initial_Condition => Is_Ready  -- Predicate stating the logical state after
                                           -- initialization.
    is
       function Is_Ready return Boolean
          with Global => State;
    end Q;

.. code-block:: ada
   :linenos:

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


::

  refinement_list   ::= ( refinement_clause { , refinement_clause } )
  refinement_clause ::= state_name => constituent_list
  constituent_list  ::= null
                      | constituent
                      | ( constituent { , constituent } )

where

  ``constituent ::=`` *object_*\ ``name | state_name``


.. centered:: **Name Resolution Rules**


1. A Refined_State aspect of a ``package_body`` has visibility extended to the
   ``declarative_part`` of the body.


.. centered:: **Legality Rules**


2. A Refined_State aspect shall only appear in the ``aspect_specification`` of a
   ``package_body``. [The use of ``package_body`` rather than package body
   allows this aspect to be specified for generic package bodies.]


3. If a ``package_specification`` has a non-null Abstract_State aspect its body
   shall have a Refined_State aspect.


4. If a ``package_specification`` does not have an Abstract_State aspect,
   then the corresponding ``package_body`` shall not have a Refined_State
   aspect.


5. Each ``constituent`` shall be either a variable, a constant, or a state
   abstraction.


6. An object which is a ``constituent`` shall be an entire object.


7. A ``constituent`` of a state abstraction of a package shall denote
   either an entity with no Part_Of ``option`` or aspect which is part
   of the hidden state of the package, or an entity whose declaration
   has a Part_Of ``option`` or aspect which denotes this state
   abstraction (see :ref:`package_hierarchy`).


8. Each *abstract_*\ ``state_name`` declared in the package
   specification shall be denoted exactly once as the ``state_name``
   of a ``refinement_clause`` in the Refined_State aspect of the body
   of the package.


9. Every entity of the hidden state of a package shall be denoted as a
   ``constituent`` of exactly one *abstract_*\ ``state_name`` in the
   Refined_State aspect of the package and shall not be denoted more than
   once. [These ``constituents`` shall be either objects declared in the
   private part or body of the package, or the declarations from the
   visible part of nested packages declared immediately therein.]


10. In a package body where the refinement of a state abstraction is
    visible the ``constituents`` of the state abstraction must be
    denoted in aspect specifications rather than the state
    abstraction.


11. The legality rules related to a Refined_State aspect given in
    :ref:`package_hierarchy` also apply.


12. Each ``constituent`` of a ghost state abstraction shall be either
    a ghost variable or a ghost state abstraction. [The reverse situation
    (i.e., a ghost constituent of a non-ghost state abstraction) is permitted.]


13. A ``constituent`` of a synchronized state abstraction shall be
    either a synchronized object or another synchronized state abstraction.
    A ``constituent`` of a state abstraction which is neither external
    nor synchronized shall be not be an effectively volatile object,
    a synchronized state abstraction, or an external state abstraction.


.. centered:: **Static Semantics**


14. A Refined_State aspect of a ``package_body`` completes the
    declaration of the state abstractions occurring in the
    corresponding ``package_specification`` and defines the objects
    and each subordinate state abstraction that are the
    ``constituents`` of the *abstract_*\ ``state_names`` declared in
    the ``package_specification``.


15. A **null** ``constituent_list`` indicates that the named abstract
    state has no constituents and termed a *null_refinement*. The
    state abstraction does not represent any actual state at
    all. [This feature may be useful to minimize changes to Global and
    Depends aspects if it is believed that a package may have some
    extra state in the future, or if hidden state is removed.]


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with Refined_State aspect.

.. centered:: **Verification Rules**


16. Each ``constituent`` that is a constant shall be a constant *with
    variable inputs*.


17. If the Async_Writers aspect of a state abstraction is True and the
    Async_Writers aspect of a constituent of that state abstraction is
    False, then after the elaboration of the (possibly implicit) body
    of the package which declares the abstraction, the constituent
    shall be initialized.


.. centered:: **Examples**

.. code-block:: ada
   :linenos:

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
constituents of those abstractions. References to a state abstraction
whose refinement is not visible at the point of the subprogram_body
may also be similarly replaced if Part_Of aspect specifications
which are visible at the point of the subprogram body
identify one or more constituents of the abstraction; such a state
abstraction is said to be *optionally refinable* at the point of the
subprogram body.

See section :ref:`global-aspects` regarding how the rules given in this
section apply to protected operations and to task bodies.

The Refined_Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Refined_Global and the ``aspect_definition``
shall follow the grammar of ``global_specification`` in :ref:`global-aspects`.

.. centered:: **Static Semantics**

1. The static semantics are as for those of the Global aspect given in
   :ref:`global-aspects`. [Differences between these two aspects for one
   subprogram stem from differences in state abstraction visibility
   between the points where the two aspects are specified.]

.. centered:: **Legality Rules**


2. A Refined_Global aspect is permitted on a body_stub (if one is
   present), subprogram body, entry body, or task body if and only if
   the stub or body is the completion of a declaration occurring in the
   specification of an enclosing package, the declaration has a
   Global aspect which denotes a state abstraction declared by the package and
   either the refinement of the state abstraction is visible or a Part_Of
   specification specifying a constituent of the state abstraction is visible.


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
      point of the Refined_Global aspect specification, there are no
      corresponding ``global_items`` in the Refined_Global specification.
      If this results in a Refined_Global specification with no
      ``global_items``, then the Refined_Global specification shall
      include a ``null_global_specification``.

   c. For each ``global_item`` in the Global aspect which does not
      denote a state abstraction whose refinement is visible and
      does not denote an optionally refinable state abstraction, the
      Refined_Global specification shall include exactly one
      ``global_item`` which denotes the same entity as the
      ``global_item`` in the Global aspect.

   d. For each ``global_item`` in the Global aspect which designates
      a state abstraction which is optionally refinable, refinement
      of the abstraction is optional in the following sense: either the
      reference to the state abstraction may be replaced with references
      to its constituents (following the rules of case 'a' above) or
      not (in which case the rules of case 'c' above apply). However,
      only the latter option is available if the mode of the state
      abstraction in the Global specification is Output.

   e. No other ``global_items`` shall be included in the Refined_Global
      aspect specification.

   f. At least one state abstraction mentioned in the Global aspect
      specification shall be unmentioned in the Refined_Global
      aspect specification. [This usually follows as a consequence of
      other rules, but not in some cases involving optionally refinable
      state abstractions where the option is declined.]


4. ``Global_items`` in a Refined_Global ``aspect_specification`` shall denote
   distinct entities.


5. The mode of each ``global_item`` in a Refined_Global aspect shall match
   that of the corresponding ``global_item`` in the Global aspect unless
   that corresponding ``global_item`` denotes a state abstraction which
   is not mentioned in the Refined_Global aspect. In that case, the modes
   of the ``global_items`` in the Refined_Global aspect which denote (direct
   or indirect) constituents of that state abstraction collectively determine
   (as described below) an "effective mode" for the abstraction. If there is
   at least one such constituent, then that "effective mode" shall match that
   of the corresponding ``global_item``
   in the Global aspect; it is determined as follows:

   a. If the refinement of the abstraction is visible and every constituent
      of the abstraction is mentioned in the Refined_Global aspect with a mode
      of Output, then the effective mode is Output;

   b. Otherwise, if at least one constituent of the abstraction is mentioned
      in the Refined_Global aspect with a mode of Output or In_Out, then
      the effective mode is In_Out;

   c. Otherwise, if at least one constituent of the abstraction is mentioned
      in the Refined_Global aspect with a mode of Input, then the effective
      mode is Input;

   d. Otherwise, the effective mode is Proof_In.

   [If there is no such consituent (e.g., because a *null* refinement is
   visible) then the mode of the state abstraction in the Global aspect
   plays no role in determining the legality of the Refined_Global aspect.]


6. The legality rules for :ref:`global-aspects` and External states described in
   :ref:`refined_external_states` also apply.


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Refined_Global aspect.

.. centered:: **Verification Rules**


8. If a subprogram has a Refined_Global aspect it is used in the analysis of the
   subprogram body rather than its Global aspect.


9. The verification rules given for :ref:`global-aspects` also apply.


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

See section :ref:`global-aspects` regarding how the rules given in this
section apply to protected operations and to task bodies.

The Refined_Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Refined_Depends and the ``aspect_definition``
shall follow the grammar of ``dependency_relation`` in :ref:`depends-aspects`.

.. centered:: **Static Semantics**

1. The static semantics are as for those of the Depends aspect given in
   :ref:`depends-aspects`. [Differences between these two aspects for one
   subprogram stem from differences in state abstraction visibility
   between the points where the two aspects are specified.]

.. centered:: **Legality Rules**


2. A Refined_Depends aspect is permitted on a body_stub (if one is
   present), subprogram body, entry body, or task body if and only if
   the stub or body is the completion of a declaration in the
   specification of an enclosing package and the declaration has a
   Depends aspect which denotes a state abstraction declared by the package and
   the refinement of the state abstraction is visible.


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

   c. If the ``output`` in the Depends aspect denotes a state
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


4. These rules result in omitting each state abstraction whose **null**
   refinement is visible at the point of the Refined_Depends. If and only if
   required by the syntax, the state abstraction shall be replaced by a **null**
   symbol rather than being omitted.


5. No other ``outputs`` or ``inputs`` shall be included in the Refined_Depends
   aspect specification. ``Outputs`` in the Refined_Depends aspect
   specification shall denote distinct entities. ``Inputs`` in an ``input_list``
   shall denote distinct entities.


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


7. The rules for :ref:`depends-aspects` also apply.


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Refined_Depends aspect
as it is used purely for static analysis purposes and is not executed.

.. centered:: **Verification Rules**


8. If a subprogram has a Refined_Depends aspect it is used in the analysis of
   the subprogram body rather than its Depends aspect.


9. The verification rules given for :ref:`depends-aspects` also apply.


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

In order to avoid aliasing-related problems (see :ref:`anti-aliasing`), |SPARK|
must ensure that if a given piece of state (either an object or a state
abstraction) is going to be a constituent of a given state abstraction, that
relationship must be known at the point where the constituent is declared.

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

The Part_Of aspect can also be used in a different way to indicate
that an object or state abstraction is to be treated as though it
were declared within a protected unit or task unit (see section
:ref:`tasks-and-synchronization`).

.. centered:: **Static Semantics**


1. A *Part_Of indicator* is a Part_Of ``option`` of a state
   abstraction declaration in an Abstract_State aspect, a Part_Of
   aspect specification applied to a variable declaration or a Part_Of
   specification aspect applied to a generic package instantiation. The
   Part_Of indicator shall denote the *encapsulating* state abstraction
   of which the declaration is a constituent, or shall denote a
   task or protected unit (see section :ref:`tasks-and-synchronization`).


.. centered:: **Legality Rules**


2. A variable declared immediately within the private part of a given
   package or a variable or state abstraction that is part of the
   visible state of a package that is declared immediately within the
   private part of the given package shall have its Part_Of indicator
   specified; the Part_Of indicator shall denote a state abstraction
   declared by the given package.


3. A variable or state abstraction which is part of the visible state of a
   non-generic private child unit (or a public descendant thereof) shall have
   its Part_Of indicator specified; the Part_Of indicator shall denote a state
   abstraction declared by either the parent unit of the private unit or by a
   public descendant of that parent unit.


4. A Part_Of aspect specification for a package instantiation applies
   to each part of the visible state of the instantiation. More
   specifically, explicitly specifying the Part_Of aspect of a package
   instantiation implicitly specifies the Part_Of aspect of each part
   of the visible state of that instantiation. The legality rules for
   such an implicit specification are the same as for an explicit
   specification.


5. No other declarations shall have a Part_Of indicator which denotes
   a state abstraction. [Other declarations may have a Part_Of indicator
   which denotes a task or protected unit (see section
   :ref:`tasks-and-synchronization`).]


6. The refinement of a state abstraction denoted in a Part_Of
   indicator shall denote as ``constituents`` all of the declarations
   that have a Part_Of indicator denoting the state abstraction. [This
   might be performed once the package body has been processed.]


7. A state abstraction and a constituent (direct or indirect) thereof
   shall not both be denoted in one Global, Depends, Initializes,
   Refined_Global or Refined_Depends aspect specification.  The
   denotation must be consistent between the Global and Depends or
   between Refined_Global and Refined_Depends aspects of a single
   subprogram.


.. centered:: **Verification Rules**


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
     the ``constituent``.  An update of such a ``constituent`` is
     regarded as updating its encapsulating state abstraction with a self
     dependency as it is unknown what other ``constituents`` the state
     abstraction encapsulates.


.. centered:: **Examples**

.. code-block:: ada
   :linenos:

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

   --  State abstractions of P.Priv, A and B, plus the concrete variable X,
   --  are split up among two state abstractions within P.Pub, R and S.
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

.. code-block:: ada
   :linenos:

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
           --  We can only refer to Outer.Hidden_State which is a constituent
           --  of Outer.A2 if the subprogram does not also refer to Outer.A2.
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
           --  Hidden_State which is part of A2, so no refined
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
      --  Outer.Hidden_State is not (by the rules of Ada).
      --  The Global and Depends Aspects are in terms
      --  of the encapsulating state abstraction Outer.A2.
      procedure Init_A2_With (Val : in Integer)
        with Global  => (Output => Outer.A2),
             Depends => (Outer.A2 => Val);
   end Outer.Public_Child;

   package body Outer.Public_Child is
      --  Outer.Hidden is visible here but the
      --  refinement of A2 is not so there are
      --  no Refined_Global or Refined_Depends.
      procedure Init_A2_With (Val : in Integer) is
      begin
         Outer.Init_A2;
         Outer.Hidden_State := Val;
      end Init_A2_With;
   end Outer.Public_Child;

.. code-block:: ada
   :linenos:

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
      --  the aspect specifications of this subprogram.
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

   with Q.Child;

   package body Q
     with Refined_State => (Q1 => Q.Child.C1,
                            Q2 => (Hidden_State, State_In_Body))
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
         State_In_Body := 42;
         Q.Child.Init_Q2;
      end Init_Q2;
   end Q;

.. code-block:: ada
   :linenos:

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
      --  specifications of this subprogram.
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
      end Private_Op;
   end R.Child;

.. _refined-postcondition:

Refined Postcondition Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the specification of a package may have a Refined_Post
aspect applied to its body or body stub. The Refined_Post aspect
may be used to restate a postcondition given on the declaration of a subprogram
in terms of the full view of a private type or the ``constituents`` of a refined
``state_name``.

The Refined_Post aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is "Refined_Post" and the ``aspect_definition`` shall
be a Boolean ``expression``.

.. centered:: **Legality Rules**


1. A Refined_Post aspect may only appear on a body_stub (if one is
   present) or the body (if no stub is present) of a subprogram or
   entry which is declared in the specification of a package, its
   abstract view. If the initial declaration in the visible part has
   no explicit postcondition, a postcondition of True is assumed for
   the abstract view.


2. A Refined_Post aspect is an assertion. The same legality rules
   apply to a Refined_Post aspect as for a postcondition (a Post
   aspect).


.. centered:: **Static Semantics**


3. [A Refined Postcondition of a subprogram defines a *refinement*
   of the postcondition of the subprogram and is intended for use
   by callers who can see the body of the subprogram.]


4. [Logically, the Refined Postcondition of a subprogram must imply
   its postcondition. This means that it is perfectly logical for the
   declaration not to have a postcondition (which in its absence
   defaults to True) but for the body or body stub to have a
   Refined Postcondition. It also means that a caller who sees the
   Refined Postcondition of a subprogram will always be able to
   prove at least as much about the results of the call as if the
   usual precondition were used instead.]


5. The static semantics are otherwise as for a postcondition.


.. centered:: **Dynamic Semantics**


6. When a subprogram or entry with a Refined Postcondition is called,
   the Refined Postcondition is evaluated
   immediately before the evaluation of the postcondition or, if there is no
   postcondition, immediately before the point at which a postcondition would
   have been evaluated. If the Refined Postcondition evaluates to
   False, then the exception Assertion.Assertion_Error is raised.
   Otherwise, the postcondition is then evaluated and checked
   as described in the Ada RM.


.. centered:: **Verification Rules**


7. If a subprogram has both a Refined_Post aspect and a
   Post (and/or Post'Class) aspect, then the verification condition
   associated with postcondition checking is discharged in two steps.

   First, the success of the Refined_Post run-time check must be proven
   as usual (i.e., just like any other run-time check).

   Next, an additional proof obligation is generated which relates
   the Refined_Post to the Post (and Post'Class) aspects of
   the subprogram according to a "wrapper" model. Imagine two
   subprograms with the same parameter profile and Global and
   Depends aspects, but with different postconditions P1 and P2
   (neither of these two subprograms has a Refined_Post aspect).
   Suppose further that the first subprogram is a "wrapper" for
   the second; that is, its implementation consists of nothing
   but a call to the second subprogram (for functions,
   the call would occur in a return statement). Consider
   the proof obligation generated for the postcondition
   check of that "wrapper" subprogram; roughly speaking, it
   is a check that P1 is implied by P2. In that sense of the
   word "implied", a verification condition is generated
   that any Post/Post'Class condition for a subprogram is
   implied by its Refined_Post condition. In particular,
   knowledge about the internals of the subprogram
   that was available in proving the Refined_Post condition
   is not available in proving this implication (just
   as, in the "wrapper" illustration, the internal details of
   the second subprogram are not available in proving the postcondition
   of the first).


8. If a Refined_Post aspect specification is visible at the
   point of a call to the subprogram, then the Refined_Post
   is used instead of the Postcondition aspect for purposes of formal
   analysis of the call. Similarly for using the Refined_Global aspect
   instead of the Global aspect and the Refined_Depends aspect instead
   of the Depends aspect. [Roughly speaking, the "contract" associated
   with a call is defined by using the Refined_* aspects of the callee
   instead of the corresponding non-refined aspects in the case where
   Refined_* aspect specifications are visible.]


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

.. Text commented out until decision on Refined_Pre is finalized.
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


1. A state abstraction that is not specified as External shall not have
   ``constituents`` which are External states.


2. An External state abstraction shall have each of the properties set to True
   which are True for any of its ``constituents``.


3. Refined_Global aspects must respect the rules related to external
   properties of constituents which are external states given in
   :ref:`external_state` and :ref:`external_state-variables`.


4. All other rules for Refined_State, Refined_Global and Refined_Depends aspect
   also apply.


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

.. _type_invariants:

Type Invariants
~~~~~~~~~~~~~~~

[Type invariants are supported in SPARK, but are subject to restrictions
which imply that if a type invariant is specified for
a type T, then any new verification conditions which this introduces outside
of the package which defines T are trivially satisified.
These restrictions ensure that any object or value of type T (or a
descendant thereof) which can be named outside of that package
will satisfy the invariant and so, for example, could not fail the runtime
check associated with passing that object or value as a parameter in call
to a procedure for which Ada requires runtime checking of the invariant
(which, in turn, means that the verification condition corresponding
to that runtime check is trivally satisfied).
In order to accomplish this goal, verification conditions for
type invariants are introduced in several contexts where Ada does
not define corresponding runtime checks.]

[As a consequence of this approach, adding or deleting a type invariant for a
private type should have little or no impact on users
outside of the package defining the private type; on the other hand,
such a change could have a great deal of impact on the verification conditions
generated for the implementation of the private type and its operations.]

[Just as a reminder to the reader, text enclosed in square brackets
is non-normative expository text. This is true everywhere in the SPARK
RM, but there is a lot of such expository text in this section and we
don't want anyone to be confused about what is strictly part of the
language definition and what is not.]

.. centered:: **Static Semantics**

1. For a given type-invariant bearing type T, a *boundary* subprogram is a
   subprogram which is declared inside the immediate scope of type T, and
   visible outside the immediate scope of T.

   The point at which a generic is declared plays no role in determining
   whether a subprogram declared as or within an instantiation of that generic
   is a boundary subprogram.

.. centered:: **Legality Rules**


2. The aspect Type_Invariant may be specified in SPARK, but only for
   the completion of a private type. [In other words, the Type_Invariant
   aspect shall not be specified for a partial view of a type, nor for the
   completion of a private extension.]
   The aspect Type_Invariant'Class is not in SPARK.


3. [A Type_Invariant expression shall not have a variable input;
   see :ref:`expressions` for the statement of this rule.]


4. A Type_Invariant shall not apply to an effectively volatile type.

.. centered:: **Verification Rules**

In Ada RM 7.3.2, Ada defines the points at which runtime checking of
type invariants is performed. In SPARK, these rules (or, more precisely,
the verification conditions corresponding to these Ada dynamic semantics
rules) are extended in several ways. In effect, verification conditions
are generated as if Ada defined additional dynamic type invariant checking at
several points (described below) where, in fact, Ada defines no such checks.
[This means that when we talk below about extending invariant checks,
we are only talking about generating additional verification conditions;
we are not talking about any changes in a program's behavior at run-time.]


5. The type invariant expression for a type T shall not include a call
   to a boundary function for type T. [This often means that a type
   invariant expression cannot contain calls to functions declared in
   the visible part of the package in question.]


**Ramification:** It is a consequence of other rules that upon entry
to a boundary subprogram for a type T, every part of every input that
is of type T can be assumed to satisfy T's invariant.


6. Upon returning from a boundary subprogram for a type T, a
   verification condition is introduced for every part of every output
   that is of type T (or a descendant thereof), to ensure that this part
   satisfies T's invariant.


7. For every subprogram declared inside the immediate scope of type T,
   the preceding rule [and ramification] also apply to [any parts of]
   any global input or output and to [any parts of] any tagged
   subprogram parameter.


8. When calling a boundary subprogram for a type T or a subprogram
   declared outside of the immediate scope of T, a verification
   condition is introduced for every part of every input that is of type T
   (or a descendant thereof), to ensure that this part satisfies
   T's invariant. [This
   verification condition is trivially satisfied if the caller is
   outside of the immediate scope of T, or if the input in question is
   subject to rule 5 and constant for the caller. The idea here is to
   prevent invariant-violating values from "leaking out".]


**Ramification:** It is a consequence of other rules that upon return
from a boundary subprogram for a type T or a subprogram declared
outside of the immediate scope of T, every part of every output that
is of type T (or a descendant thereof) can be assumed to satisfy T's invariant.


9. For every subprogram, the preceding rule [and ramification] also
   apply to [any parts of] any global input or output and to [any
   parts of] any tagged subprogram parameter. [The verification
   condition of rule 6 is trivially satisfied if the caller is outside
   of the immediate scope of T, or if the input in question is subject
   to rule 4 and constant for the caller.]


10. At the end of the elaboration of a package (i.e., at the point where the
    Initial_Condition, if any, is checked) a verification condition is
    introduced for the objects (both variables and constants) declared within
    the package. [If one chooses to think of package elaboration as being
    performed by a notional parameterless "elaboration" subprogram, then this
    rule (very roughly speaking) says that the global outputs of this notional
    subprogram follow much the same rules as for other subprograms.]


**Ramification:** In determining whether a dispatching call is a call
to a boundary subprogram or to a subprogram declared outside of the
immediate scope of T, the statically named callee is used.


**Ramification:** It is possible that the underlying tag of a tagged
object (at runtime) may differ from the tag of its nominal (compile
time) type. Suppose that an object X is (statically) of type T1 (or
T1'Class) but has T2'Tag as its underlying tag, and that T2 has one or
more components which are not components of T1. Ada does not define
runtime checking of type invariants for such "hidden" components of
parameters. The rules about tagged inputs and outputs in rules 6 and 8
are introduced in order to deal with technical difficulties that would
otherwise arise in the treatment of these hidden components.

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

   Within the Boolean expression of the Default_Initial_Condition aspect of
   a tagged type T, a name that denotes the current instance of the
   tagged type is interpreted as though it had a (notional) type NT
   that is a formal derived type whose ancestor type is T, with
   directly visible primitive operations. [This name resolution rule
   is similar to the "notional formal derived type" name resolution
   rule introduced in Ada RM 6.1.1 for certain subexpressions of
   class-wide precondition and postcondition expressions.]
   Any operations within a Default_Initial_Condition expression that
   were resolved in this way (i.e., as primitive operations of the (notional)
   formal derived type NT), are in the evaluation of the expression
   (i.e., at run-time) bound to the corresponding operations of the type of the
   object being "initialized by default" (see Ada RM 3.3.1).

Deferred Constants
------------------

No extensions or restrictions.

Limited Types
-------------

No extensions or restrictions.

Assignment and Finalization
---------------------------

.. centered:: **Legality Rules**


1. Controlled types are not permitted in |SPARK|.


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
Initial_Condition (and Initializes aspect) of a library-level package
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


1. A call which occurs within the same compilation_unit as the subprogram_body
   of the callee is said to be an *intra-compilation_unit call*.


2. A construct (specifically, a call to a subprogram or a read or write
   of a variable) which occurs in elaboration code for a library-level package
   is said to be *executable during elaboration*. If a subprogram call is
   executable during elaboration and the callee's body occurs in the same
   compilation_unit as the call, then any constructs occurring within that body
   are also executable during elaboration. [If a construct is executable during
   elaboration, this means that it could be executed during the elaboration of
   the enclosing library unit and is subject to certain restrictions described
   below.]

   For a given library unit L1 and a given distinct library unit's spec or body
   L2 depending on L1 through a chain of ``with_clauses``, the elaboration of
   the body of L1 is said to be *known to precede* the elaboration of L2 if
   either:

   a. L2 references L1 in an Elaborate or Elaborate_All pragma; or

   b. L1's Elaborate_Body aspect is True; or

   c. L1 does not require a body (the terminology is a little odd in this
      case because L1 has no body); or

   d. L1 is preelaborated and L2's library unit is not; or

   e. L2 semantically depends on some library_item L3 such that the
      elaboration of the body of L1 is known to precede the
      elaboration of L3.
      [See Ada RM 10.1.1 for definition of semantic dependence.]


.. centered:: **Legality Rules**


3. |SPARK| requires that an intra-compilation_unit call which is
   executable during elaboration shall occur after a certain point in the unit
   (described below) where the subprogram's completion is known to have been
   elaborated. The portion of the unit following this point and extending
   to the start of the completion of the subprogram is defined to
   be the *early call region* for the subprogram. An intra-compilation_unit
   call which is executable during elaboration and which occurs (statically)
   before the start of the completion of the callee shall occur within the
   early call region of the callee.


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


5. For purposes of the above rules, a subprogram completed by a
   renaming-as-body is treated as though it were a wrapper
   which calls the renamed subprogram (as described in Ada RM 8.5.4(7.1/1)).
   [The notional "call" occuring in this wrapper is then subject to the
   above rules, like any other call.]


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


7. In the case of a dispatching call, the subprogram_body mentioned
   in the above rules is that (if any) of the statically denoted callee.


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


9. For purposes of defining the early call region, the specification and body
   of a library unit package whose Elaborate_Body aspect is True are treated as
   if they both belonged to some enclosing declaration list with the body
   immediately following the specification. This means that the early call
   region in which a call is permitted can span the specification/body boundary.

   This is important for tagged type declarations.


10. For each call that is executable during elaboration for a given
    library unit package spec or body, there are two cases: it is
    (statically) a call to a subprogram whose completion is in the
    current compilation_unit (or in a preelaborated unit), or it is not.
    In the latter case, an Elaborate_All pragma shall be provided to ensure
    that the given library unit spec or body will not be elaborated
    until after the complete semantic closure of the unit in which
    the (statically denoted) callee is declared.


11. For an instantiation of a generic package (excluding a bodiless generic
    package) which does not occur in the same compilation unit as the generic
    body, the same rules apply as described
    above for a call (i.e., an Elaborate_All pragma is required).
    For an instantiation of a generic subprogram which does not occur in
    the same compilation unit as the generic body, the same rules also
    apply except that only an Elaborate (as opposed to an Elaborate_All)
    pragma is required.


12. An implementation is permitted to accept constructs which
    violate the preceding rules in this section (e.g., an
    implementation might choose to behave, for purposes of defining
    an early call region, as though some non-preelaborable construct
    is preelaborable), but only if the
    implementation is able to statically ensure that accepting
    these constructs does not introduce the possibility of
    failing an elaboration check (either for a call or for
    an instantiation), reading an uninitialized variable, or
    unsafe reliance on a package's Initial_Condition. [If an implementation
    chooses to take advantage of this permission, then the burden
    is entirely on the implementation to "get it right".]


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


2. From the end of the elaboration of a library package's body to the
   invocation of the main program (i.e., during subsequent library
   unit elaboration), variables declared in the package (and
   constituents of state abstractions declared in the package) remain
   unchanged. The Initial_Condition aspect is an assertion which is
   checked at the end of the elaboration of a package body (but occurs
   textually in the package spec; see :ref:`initial_condition_aspect`).
   The initial condition of a library-level package will remain true
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


.. centered:: **Verification Rules**


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


6. The elaboration of a package's specification and body shall not
   write to a variable (or state abstraction, in the case of a call to
   a procedure which takes an abstraction as an output) declared
   outside of the package. The output associated with a read of an
   external state with the property Effective_Reads is permitted.
   [This rule applies to all packages: library-level or not,
   instantiations or not.] The inputs and outputs of a package's
   elaboration (including the elaboration of any private descendants
   of a library unit package) shall be as described in the Initializes
   aspect of the package.


.. centered:: **Legality Rules**


7. The elaboration of a package body shall be known to follow the
   elaboration of the body of each of the
   library units [(typically private children)] which provide
   constituents for a state abstraction denoted in the Initializes
   aspect of the given package.


.. centered:: **Examples**

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
