Packages
========

.. centered:: **Verification Rules**

.. _tu-nt-packages-01:

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

   * any variables declared immediately in the private part or body of P; and

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

External state is a variable declared as Volatile or a state abstraction which
represents one or more volatile variables (or it could be a null state
abstraction; see :ref:`abstract-state-aspect`).

Four Boolean valued *properties* of external states that may be specified are
defined:

  * Async_Readers - A component of the system external to the program might
    read/consume a value written to an external state.

  * Async_Writers - A component of the system external to the program might
    update the value of an external state.

  * Effective_Writes - every update of the external state is significant.

  * Effective_Reads - every read of the external state is significant.

These properties may be specified for a Volatile variable as Boolean aspects or
as external properties of an external state abstraction.

.. centered:: **Legality Rules**

.. _tu-fe-external_state-01:

1. If an external state is declared without any of the external
   properties specified then all of the properties default to a value
   of True.

.. _tu-fe-external_state-02:

2. If just the name of the property is given then its value defaults
   to True [; for instance Async_Readers defaults to Async_Readers =>
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
   external state is significant. [For instance writing a sequence
   of values to a port.]

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

14. An external state which has the property Async_Readers => True
    need not be initialized before being read although explicit
    initialization is permitted. [The external state might be
    initialized by an external writer.]

.. _etu-external_state-ss:

.. _external_state-variables:

External State - Variables
~~~~~~~~~~~~~~~~~~~~~~~~~~

In Ada interfacing to an external device or subsystem normally entails
using one or more volatile variables to ensure that writes and reads
to the device are not optimized by the compiler into internal register
reads and writes. A variable is specified as Volatile using the Ada
aspect or pragma Volatile or Atomic.  Additionally a variable is
volatile if its subtype is specified as volatile.

|SPARK| refines the Volatile specification by introducing four new Boolean
aspects which may be applied only to objects declared as Volatile. The aspects
may be specified in the aspect specification of a Volatile object declaration
(this excludes volatile objects that are formal parameters).

The new aspects are:

  * Async_Readers - as described in :ref:`external_state`.

  * Async_Writers - as described in :ref:`external_state`.

  * Effective_Reads - as described in :ref:`external_state`.

  * Effective_Writes - as described in :ref:`external_state`.

.. centered:: **Static Semantics**

1. Concurrent accesses of a volatile variable may cause a run-time
   exception that cannot be proven to be absent by |SPARK|.

   [An example is a strictly 32-bit machine with a 64-bit Long_Float
   type, where some (invalid) floating point values will trap (and
   cause program termination) when loaded into a floating point
   register.  If, on such a system, we have a volatile variable X of
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

3. All Volatile objects are considered to have one or more external
   state properties, either given explicitly in their declaration or
   implicitly when all the properties are considered to be True. The
   following rules also apply to all Volatile objects.

.. _tu-fe-external_state_variables-04:

4. The aspects shall only be specified in the aspect specification of a Volatile
   object declaration excluding Volatile formal parameter declarations.

.. _tu-fe-external_state_variables-05:

5. The declaration of a Volatile object (other than as a formal
   parameter) shall be at library level. [That is, it shall not be
   declared within the scope of a subprogram body. A Volatile variable
   has an external effect and therefore should be global even if it is
   not visible. It is made visible via a state abstraction.]

.. _tu-fe-external_state_variables-06:

6. A constant, a discriminant or a loop parameter shall not be Volatile.

.. _tu-fe-external_state_variables-07:

7. A non-volatile object shall not have a Volatile component.

.. _tu-fe-external_state_variables-08:

8. A Volatile object shall not be used as an actual parameter in a generic instantiation.

.. _tu-fe-external_state_variables-09:

9. A Volatile object shall not be a ``global_item`` of a function.

.. _tu-fe-external_state_variables-10:

10. A function shall not have a formal parameter of a Volatile type.

.. _tu-fe-external_state_variables-11:

11. If a Volatile object has Effective_Reads set to True then it must
    have a ``mode_selector`` of Output or In_Out when denoted as a
    ``global_item``.

.. _tu-fe-external_state_variables-12:

12. A Volatile object shall only occur as an actual parameter of a
    subprogram if the corresponding formal parameter is of a
    non-scalar Volatile type or as an actual parameter in a call to an
    instance of Unchecked_Conversion.

.. _tu-fe-external_state_variables-13:

13. Contrary to the general |SPARK| rule that expression evaluation
    cannot have side effects, a read of a Volatile object with the
    properties Async_Writers or Effective_Reads set to True is
    considered to have an effect when read. To reconcile this
    discrepancy, a name denoting such an object shall only occur in
    the following contexts:

   * as the name on the left-hand side of an assignment statement; or

   * as the [right-hand side] expression of an assignment statement; or

   * as the expression of an initialization expression of an object declaration; or

   * as an actual parameter in a call to an instance of Unchecked_Conversion
     whose result is renamed [in an object renaming declaration]; or

   * as an actual parameter in a procedure call of which the corresponding
     formal parameter is of a non-scalar Volatile type.

.. _etu-external_state_variables-lr:

.. centered:: **Static Semantics**

These are explained in :ref:`external_state`.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with these aspects.

.. centered:: **Verification Rules**

.. _tu-fe-fa-external_state_variables-14:

14. As formal subprogram parameters of a Volatile type cannot have
    these aspects specified assumptions have to be made in the body of
    the subprogram of the properties that the formal parameter of a
    given mode may have as follows:

    * mode **in**: the formal parameter cannot be updated by the
      subprogram and is considered to have the properties
      Async_Writers => True and Effective_Reads => False. The actual
      parameter in a call must be Volatile and have these properties
      but may also have the properties Async_Readers and
      Effective_Writes set to True.

    * mode **out**: the formal parameter cannot be read by the
      subprogram as it is unknown whether a read will have an external
      effect. The formal parameter is considered to have the
      properties Async_Readers => True and/or Effective_Writes =>
      True. The actual parameter in a call to the subprogram must be
      Volatile and have either or both of these properties True but
      may also have Async_Writers and Effective_Reads set to True. If
      the subprogram attempts a read of the formal parameter a flow
      anomaly will be reported.

    * mode **in out**: the formal parameter is considered to have all
      properties; Async_Readers => True, Async_Writers => True,
      Effective_Reads => True, Effective_Writes => True. The actual
      parameter in a subprogram call must be Volatile and have all of
      these properties set to True.

.. _etu-external_state_variables-vr:

.. centered:: **Examples**

.. code-block:: ada

   with System.Storage_Elements;
   package Input_Port
   is
      Sensor : Integer
         with Volatile,
              Async_Writers,
              Address => System.Storage_Elements.To_Address (16#ACECAF0#);
   end Input_Port;

   with System.Storage_Elements;
   package Output_Port
   is
      Sensor : Integer
         with Volatile,
              Async_Readers,
              Address => System.Storage_Elements.To_Address (16#ACECAF0#);
   end Output_Port;

   with System.Storage_Elements;
   package Multiple_Ports
   is
      type Volatile_Type is record
        I : Integer;
      end record with Volatile;

.. code-block:: ada

      -- This type declaration indicates all objects
      -- of this type will be volatile.
      -- We can declare a number of objects of this type
      -- with different properties.

      -- V_In_1 is essentially an external input since it
      -- has Async_Writers => True but Async_Readers => False.
      -- Reading a value from V_In_1 is independent of other
      -- reads of the same object. Two successive reads might
      -- not have the same value.
      V_In_1 : Volatile_Type
         with Async_Writers,
              Address => System.Storage_Elements.To_Address (16#A1CAF0#);

      -- V_In_2 is similar to V_In_1 except that each value read is
      -- significant. V_In_2 can only be used as a Global with a
      -- mode_Selector of Output or In_Out or as an actual parameter
      -- whose corresponding formal parameter is of a Volatile type and
      -- has mode out or in out.
      V_In_2 : Volatile_Type
         with Async_Writers,
              Effective_Reads,
              Address => System.Storage_Elements.To_Address (16#ABCCAF0#);


      -- V_Out_1 is essentially an external output since it
      -- has Async_Readers => True but Async_Writers => False.
      -- Writing the same value successively might not have an
      -- observable effect.
      V_Out_1 : Volatile_Type
         with Async_Readers,
              Address => System.Storage_Elements.To_Address (16#BBCCAF0#);

      -- V_Out_2 is similar to V_Out_1 except that each write to
      -- V_Out_2 is significant.
      V_Out_2 : Volatile_Type
         with Async_Readers,
              Effective_Writes,
              Address => System.Storage_Elements.To_Address (16#ADACAF0#);

      -- This declaration defaults to the following properties:
      -- Async_Readers => True,
      -- Async_Writers => True,
      -- Effective_Reads => True,
      -- Effective_Writes => True;
      -- That is the most comprehensive type of external interface
      -- which is bi-directional and each read and write has an
      -- observable effect.
      V_In_Out : Volatile_Type
         with Address => System.Storage_Elements.To_Address (16#BEECAF0#);

      -- These volatile variable declarations may be used in specific ways
      -- as global items and actual parameters of subprogram calls
      -- dependent on their properties.

      procedure Read (Value : out Integaer)
         with Global  => (Input => V_In_1),
              Depends => (Value => V_in_1);
         -- V_In_1, V_Out_1 and V_Out_2 are compatible with a mode selector
         -- of Input as this mode requires Effective_Reads => False.

      procedure Write (Value : in Integaer)
         with Global  => (Output => V_Out_1),
              Depends => (V_Out_1 => Value);
         -- Any Volatile Global is compatible with a mode selector of Output.
         -- A flow error will be raised if the subprogram attempts to
         -- read a Volatile Global with Async_Writers and or
         -- Effective_Reads set to True.

      procedure Read_With_Effect (Value : out Integer)
         with Global  => (In_Out => V_In_2),
              Depends => (Value  => V_In_2,
                          V_In_2 => null);
         -- Any Volatile Global is compatible with a mode selector of In_Out.
         -- The Depends aspect is used to specify how the Volatile Global
         -- is intended to be used and this is checked by flow analysis
         -- to be compatible with the properties specified for the Volatile Global.

      -- When a formal parameter is volatile assumptions have to be made in
      -- the body of the subprogram as to the possible properties that the actual
      -- volatile parameter might have dependent on the mode of the formal parameter.

      procedure Read_Port (Port : in Volatile_Type; Value : out Integer)
         with Depends => (Value => Port,);
         -- Port is Volatile and of mode in.  Assume that the formal parameter
         -- has the properties Async_Writers => True and Effective_Reads => False
         -- The actual parameter in a call of the subprogram must have
         -- Async_Writers_True and Effective_Reads => False
         -- and may have Async_Writers and/or Effective_Writes True.
         -- As an in mode parameter it can only be read by the subprogram.
         -- Eg. Read_Port (V_In_1, Read_Value).

      procedure Write_Port (Port : out Volatile_Type; Value : in Integer)
         with Depends => (Port => Value);
         -- Port is volatile and of mode out.  Assume the formal parameter
         -- has the properties Async_Readers => True, Effective_Writes => True
         -- The actual parameter in a call to the subprogram must have
         -- Async_Readers and/or Effective_Writes True, and may have
         -- Async_Writers and Effective_Reads True.
         -- As the mode of the formal parameter is mode out, it is
         -- incompatible with reading the parameter because this could read
         -- a value from an Async_Writer.
         -- A flow error will be signalled if a read of the parameter occurs
         -- in the subprogram.
         -- Eg. Write_Port (V_Out_1, Output_Value) and Write_Port (V_Out_2, Output_Value).

      -- A Volatile formal parameter type of mode in out is
      -- assume to have all the properties True:
      -- Async_Readers => True,
      -- Async_Writers => True,
      -- Effective_Reads => True,
      -- Effective_Writes => True;
      -- The corresponding actual parameter in a subprogram call must be
      -- volatile with all of the properties set to True.
      procedure Read_And_Ack (Port : in out Volatile_Type; Value : out Integer)
         with Depends => (Value => Port,
                          Port => Port);
         -- Port is Volatile and reading a value may require the sending of an
         -- acknowledgement, for instance.
         -- Eg. Read_And_Ack (V_In_Out, Read_Value).

  end Multiple_Ports;


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
  simple_option            ::= identifier
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

Currently no ``simple_options`` are defined.

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

.. _etu-abstract_state_aspects-ss:

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Abstract_State aspect.

.. centered:: **Verification Rules**

There are no verification rules associated with the Abstract_State aspect.

.. centered:: **Examples**

.. code-block:: ada

   package Q
      with Abstract_State => State          -- Declaration of abstract state named State
                                            -- representing internal state of Q.
   is
      function Is_Ready return Boolean      -- Function checking some property of the State.
         with Global => State;              -- State may be used in a global aspect.

      procedure Init                        -- Procedure to initialize the internal state of Q.
         with Global => (Output => State),  -- State may be used in a global aspect.
	      Post   => Is_Ready;

      procedure Op_1 (V : Integer)          -- Another procedure providing some operation on State
         with Global => (In_Out => State),
              Pre    => Is_Ready,
              Post   => Is_Ready;
   end Q;

   package X
      with Abstract_State => (A, B, (C with External => (Async_Writers, Effective_Reads => False))
           -- Three abstract state names are declared A, B & C.
           -- A and B are internal abstract states
           -- C is specified as external state which is an external input.
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
   definition for a package shall denote a state abstraction of the package or
   an entire variable declared immediately within the visible part of the
   package.

.. _tu-fe-initializes_aspects-04:

4. Each ``name`` in the ``input_list`` shall denote an entire variable or a state
   abstraction but shall not denote an entity declared in the package with the
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

9. An ``initialization_item`` shall have a an ``input_list`` if and
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
            -- Three abstract state names are declared A, B & C.
            Initializes    => A
            -- A is initialized during the elaboration of Y.
            -- C is specified as external state with Async_Writers
            -- and need not be explicitly initialized.
            -- B is not initialized.
    is
       ...
    end Y;

    package Z
       with Abstract_State => A,
            Initializes    => null
            -- Package Z has an abstract state name A declared but the
            -- elaboration of Z and its private descendants do not
            -- perform any initialization during elaboration.
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

4. An Initial_Condition aspect is a sort of postcondition for the
   elaboration of both the specification and body of a package. If
   present on a package, then its *Boolean_*\ ``expression`` defines
   properties (a predicate) of the state of the package which can be
   assumed to be true immediately following the elaboration of the
   package. [The expression of the Initial_Condition cannot denote a
   state abstraction. This means that to express properties of hidden
   state, functions declared in the visible part acting on the state
   abstractions of the package must be used.]


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

6. [The Initial_Condition aspect gives a proof obligation to show that the
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

A subprogram may have an *abstract view* and a *refined view*. The abstract
view is a subprogram declaration in the visible part of a package where a
subprogram may refer to private types and state abstractions whose details are
not visible. A refined view of a subprogram is the body or body stub of the
subprogram in the package body whose visible part declares its abstract view.

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

  refinement_list   ::= refinement_clause
                      | ( refinement_clause { , refinement_clause } )
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

5. Each ``constituent`` shall be either a variable or a state abstraction.

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
   Refined_State aspect of the package and shall not be denoted more than once.
   [These ``constituents`` are either variables declared in the private part or
   body of the package, or the declarations from the visible part of
   nested packages declared immediately therein.]

.. _tu-cbatu-refined_state_aspects-10:

10. In a package body where the refinement of a state abstraction is
    visible the ``constituents`` of the state abstraction must be
    denoted in aspect specifications rather than the state
    abstraction.

.. _tu-cbatu-refined_state_aspects-11:

11. The legality rules related to a Refined_State aspect given in
    :ref:`package_hierarchy` also apply.

.. _etu-refined_state_aspects-lr:

.. centered:: **Static Semantics**

.. _tu-fe-refined_state_aspects-12:

12. A Refined_State aspect of a ``package_body`` completes the
    declaration of the state abstractions occurring in the
    corresponding ``package_specification`` and defines the objects
    and each subordinate state abstraction that are the
    ``constituents`` of the *abstract_*\ ``state_names`` declared in
    the ``package_specification``.

.. _tu-fe-refined_state_aspects-13:

13. A **null** ``constituent_list`` indicates that the named abstract
    state has no constituents and termed a *null_refinement*. The
    state abstraction does not represent any actual state at
    all. [This feature may be useful to minimize changes to Global and
    Depends aspects if it is believed that a package may have some
    extra state in the future, or if hidden state is removed.]

.. _etu-refined_state_aspects-ss:

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with Refined_State aspect.

.. centered:: **Verification Rules**

There are no verification rules associated with Refined_State aspect.

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

A subprogram declared in the visible part of a package may have a Refined_Global
aspect applied to its body or body stub. A Refined_Global aspect of a subprogram
defines a *refinement* of the Global Aspect of the subprogram; that is, the
Refined_Global aspect repeats the Global aspect of the subprogram except that
references to state abstractions whose refinements are visible at the point
of the subprogram_body are replaced with references to [some or all of the]
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
   visible part of an enclosing package, the declaration has a
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

.. code-block:: ada

    package Refined_Global_Examples
    with Abstract_State => (S1, S2),
	 Initializes =>(S1, V1)
    is
       V1 : Integer := 0;  -- Visible state variables

       procedure P1_1 (I : in Integer)
	 with Global => (In_Out => S1);

       procedure P1_2 (I : in Integer)
	 with Global => (In_Out => S1);

       procedure P1_3 (Result : out Integer)
	 with Global => (Input => S1);

       procedure P1_4 (I : in Integer)
	 with Global => (Output => S1);

       procedure P2
	 with Global => (Input  => V1,
			 In_Out => S2);

       procedure P3 (J : in Integer)
	 with Global => (Output => V1);

       procedure P4
	 with Global => (Input => (S1, V1),
			 In_Out => S2);
    end Refined_Global_Examples;

    package body Refined_Global_Examples
      with Refined_State => (S1 => (A, B),
                             S2 => (X, Y, Z))
    is
       A : Integer := 1;  -- The constituents of S1
       B : Integer := 2;  -- Initialized as promised

       X, Y, Z : Integer; -- The constituents of S2
			  -- Not initialized

       procedure P1_1 (I : in Integer)
	 with Refined_Global =>
	   (In_Out => A,  -- Refined onto constituents of S1
	    Output => B)  -- B is Output but A is In_Out and so
       is                 --  Global S1 is also In_Out
       begin
	  B := A;
	  A := I;
       end P1_1;

       procedure P1_2 (I : in Integer)
	 with Refined_Global =>
	   (Output => A)     -- Not all of the constituents of S1 are updated
       is                    -- and so the Global S1 must In_Out
       begin
	  A := I;
       end P1_2;

       procedure P1_3 (Result : out Integer)
	 with Refined_Global =>
	   (Input => B)      -- Not all of the constituents of S1 are read but none
       is                    -- of them are updated so the Global S1 is Input
       begin
	 Result := B;
       end P1_3;

       procedure P1_4 (I : in Integer)
	 with Refined_Global =>
	   (Output => (A, B))-- The constituents of S1 are not read but they are all
       is                    -- updated and so the mode selector of S1 is Output
       begin
	  A := I;
	  B := A;
       end P1_4;

       procedure P2
	 with Refined_Global =>
	   (Input  => V1,    -- V1 has no constituents and not subject to refinement
	    Output => Z)     -- Only the constituent Z of S2 is updated and so the
       is                    -- the mode selector of the Global S2 is In_Out
       begin
	 Z := V1;
       end P2;

       procedure P3 (J : in Integer)
       is                    -- No Refined_Global aspect here because V1 has no
       begin                 -- refinement.
	 V1 := J;
       end P3;

       procedure P4
	 with Refined_Global =>
	   (Input  => (A, V1),-- The refinment of both S1 and S2 are visible
	    Output => (X, Y)) -- and cannot be denoted here.  Their constituents
       is                     -- must be used instead.
       begin
	 X := V1;
	 Y := A;
       end P4;

    end Refined_Global_Examples;

.. _refined-depends-aspect:

Refined_Depends Aspects
~~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the visible part of a package may have a Refined_Depends
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
   visible part of an enclosing package and the declaration has a
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
      then either:

      - at least one of its ``constituents`` shall be denoted as an
        ``input`` in at least one of the ``dependency_clauses`` of the
        Refined_Depends aspect corresponding to the original
        ``dependency_clause`` in the Depends aspect; or

      - the state abstraction is both an ``input`` and an ``output``
        and not every ``constituent`` the state abstraction is an
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

.. code-block:: ada

    package Refined_Depends_Examples
      with Abstract_State => (S1, S2),
           Initializes    => (S1, V1)
    is
       V1 : Integer := 0;  -- Visible state variables

       procedure P1_1 (I : in Integer)
	 with Global  => (In_Out => S1),
	      Depends => (S1 =>+ I);

       procedure P1_2 (I : in Integer)
	 with Global  => (In_Out => S1),
	      Depends => (S1 =>+ I);

       procedure P1_3 (Result : out Integer)
	 with Global  => (Input => S1),
	      Depends => (Result => S1);

       procedure P1_4 (I : in Integer)
	 with Global  => (Output => S1),
	      Depends => (S1 => I);

       procedure P2
	 with Global  => (Input  => V1,
			  In_Out => S2),
	      Depends => (S2 =>+ V1);

       procedure P3 (J : in Integer)
	 with Global  => (Output => V1),
	      Depends => (V1 => J);

       procedure P4
	 with Global  => (Input => (S1, V1),
			 In_Out => S2),
	      Depends => (S2 =>+ (S1, V1));
    end Refined_Depends_Examples;

    package body Refined_Depends_Examples
      with Refined_State => (S1 => (A, B),
	                     S2 => (X, Y, Z))
    is
       A : Integer := 1;  -- The constituents of S1
       B : Integer := 2;  -- Initialized as promised

       X, Y, Z : Integer; -- The constituents of S2
			  -- Not initialized

       procedure P1_1 (I : in Integer)
	 with Refined_Global  => (In_Out => A,
				  Output => B),
	      Refined_Depends =>
		(A => I,  -- A and B are the constituents of S1 both are outputs
		 B => A)  -- A is dependent on I but A is also an input and B
       is                 -- depends on A.  Hence the Depends => (S1 =>+ I)
       begin
	  B := A;
	  A := I;
       end P1_1;

       procedure P1_2 (I : in Integer)
	 with Refined_Global  => (Output => A),
	      Refined_Depends =>
		 (A => I) -- One but not all of the constituents of S1 is updated
       is                 -- hence the Depends =>  (S1 =>+ I)
       begin
	  A := I;
       end P1_2;

       procedure P1_3 (Result : out Integer)
	 with Refined_Global  => (Input => B),
	      Refined_Depends =>
		 (Result => B) -- Not all of the constituents of S1 are read but
       is                      -- none of them are updated, hence
       begin                   --  Depends => (Result => S1)
	 Result := B;
       end P1_3;

       procedure P1_4 (I : in Integer)
	 with Refined_Global  => (Output => (A, B)),
	      Refined_Depends =>
		((A, B) => I)  -- The constituents of S1 are not inputs but all of
       is                      -- the constituents of S1 are updated, hence,
       begin                   -- Depends => (S1 => I)
	  A := B;
	  B := A;
       end P1_4;

       procedure P2
	 with Refined_Global  => (Input  => V1,
				  Output => Z),
	      Refined_Depends =>
		(Z => V1)      -- Only the constituent Z of S2 is an output but the
       is                      -- other constituents of S2 are preserved, hence,
       begin                   -- Depends => (S2 =>+ V1);
	 Z := V1;
       end P2;

       procedure P3 (J : in Integer)
       is                      -- No Refined_Depends aspect here because V1 has no
       begin                   -- refinement.
	 V1 := J;
       end P3;

       procedure P4
	 with Refined_Global  => (Input => (A, V1),
				  Output => (X, Y)),
	      Refined_Depends =>
		(X => V1,      -- Only the constituents X and Y of S2 are updated
		 Y => A)       -- Z is not updated and so S2 must have a self-
       is                      -- dependency. The constituent A of S1 is read
       begin                   -- and none of the constituents of S1 are updated,
	 X := V1;              -- hence, Depends => (S2 =>+ (S1, V1))
	 Y := A;
       end P4;

    end Refined_Depends_Examples;


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
       -- P has no state abstraction
    is
       ...
    end P;

    -- P.Pub is the public package that declares the state abstraction
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
       X : T  -- visible variable which is a constituent of P.Pub.R.
          with Part_Of => P.Pub.R;
    end P.Priv;

    with P.Priv; -- P.Priv has to be with'd because its state is part of the
                 -- refined state.
    package body P.Pub
       with Refined_State => (R => (P.Priv.A, P.Priv.X, Y),
                              S => (P.Priv.B, Z))
    is
       Y : T2;  -- hidden state
       Z : T3;  -- hidden state
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
       -- A variable declared in the private part must have a Part_Of aspect
       Hidden_State : Integer
          with Part_Of => A2;

       package Inner
          with Abstract_state => (B1 with Part_Of => Outer.A1)
                        -- State abstraction declared in the private
                        -- part must have a Part_Of option.
       is
          -- B1 may be used in aspect specifications provided
          -- Outer.A1 is not also used.
          procedure Init_B1
             with Global  => (Output => B1),
                  Depends => (B1 => null);

          procedure Init_A2
             -- We can only refer to Outer.Hidden_State which is
             -- a constituent of Outer.A2 if the subprogram does
             -- not also refer to Outer.A2.
             with Global  => (Output => Hidden_State),
                  Depends => (Hidden_State => null);

       end Inner;
    end Outer;

   package body Outer
      with Refined_State => (A1 => Inner.B1,
                             A2 => (Hidden_State, State_In_Body))
                             -- A1 and A2 cannot be denoted in the
                             -- body of Outer because their refinements are visible.
   is
      State_In_Body : Integer;

      package body Inner
         with Refined_State => (B1 => null)  -- Oh, there isn't any state after all
      is
         procedure Init_B1
            with Refined_Global  => null,  -- Refined_Global and
                 Refined_Depends => null   -- Refined_Depends of a null refinement
         is
         begin
            null;
         end Init_B1;

         procedure Init_A2
            -- The Global sparct is already in terms of the constituent
            -- Hidden_State which is part of of A2, so no refined
            -- Global or Depends aspects are required.
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

   package Outer.Public_Child
   is
      -- Outer.A1 and Outer.A2 are visible but
      -- Outer.Hidden_State is not (by the rules of Ada)
      -- The Global and Depends Aspects are in terms
      -- of the encapsulating state abstraction Outer.A2.
      procedure Init_A2_With (Val : in Integer)
         with Global  => (Output => Outer.A2),
              Depends => (Outer.A2 => Val);
   end Outer.Public_Child;

   package body Outer.Public_Child
   is
      -- Outer.Hidden is visible here but the
      -- refinement of A2 is not so there are
      -- no Refined_Global or Refined_Depends
      procedure Init_A2_With (Val : in Integer)
      is
      begin
         Outer.Init_A2;
         Outer.Hidden_State := Val;
      end Init_A2_With;
   end Outer.Public_Child;


   package Q
      with Abstract_State => (Q1, Q2)
   is
      -- Q1 and Q2 may be denoted here
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
      -- C1 rather than the encapsulating state abstraction
      -- may be used in aspect specifications provided
      -- Q.Q1 is not also denoted in the same aspect
      -- specification.

      -- Here C1 is used so Q1 cannot also be used in
      -- the aspect specifications of this subprogram
      procedure Init_Q1
         with Global  => (Output => C1),
              Depends => (C1 => null);

      -- Q.Hidden_State which is a constituent of Q.Q2
      -- is visible here so it can be used in a aspect
      -- specification provided Q.Q2 is not also used.
      procedure Init_Q2
         with Global  => (Output => Q.Hidden_State),
              Depends => (Q.Hidden_State => null);
   end Q.Child;

   package body Q.Child
      with Refined_State => (C1 => Actual_State)
   is
      -- C1 shall not be denoted here - only Actual_State
      -- but Q.Q2 and Q.Hidden_State may be denoted.
      Actual_State : Integer;

      procedure Init_Q1
         with Refined_Global  => (Output => Actual_State),
              Refined_Depends => (Actual_State => null)
      is
      begin
         Actual_State := 0;
      end Init_Q1;

      -- The refinement of Q2 is not visible and so Init_Q2
      -- has no Refined_Global or Refined_Depends aspects.
      procedure Init_Q2
      is
      begin
         Q.Hidden_State := 0;
      end Init_Q2;

   end Q.Child;

   package body Q
      with Refined_State => (Q1 => Q.Child.C1,
                             Q2 => Hidden_State, State_In_Body)
   is
      -- Q1 and Q2 shall not be denoted here but the constituents
      -- Q.Child.C1, State_In_Body and Hidden_State may be.
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
      -- Both R.R1 and R2 are visible.

      -- Here more than just the R2 constituent of R.R1
      -- will be updated and so we use R.R1 in the
      -- aspect specifications rather than R2.
      -- R2 cannot also be used in the aspect
      -- specifications of this subprogram
      procedure Private_Op (I, J : in Integer)
         with Global  => (In_Out => R.R1),
              Depends => (R.R1 =>+ (I, J));
   end R.Child;

   package body R.Child
      with Refined_State => (R2 => Actual_State)
   is
      -- R2 shall not be denoted here - only Actual_State
      -- but R.R1 may be denoted.
      Actual_State : Integer;

      -- The Global and Depends aspects of Private_Op
      -- are in terms of R.R1 and the refinement of
      -- R.R1 is not visible and so Refined_Global
      -- and Refined_Depends are not required.
      procedure Private_Op (I, J : in Integer)
      is
      begin
         R.Op_1 (I);
         Actual_State := J;
      end Init_Q1;

   end R.Child;


Refined Postcondition Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the visible part of a package may have a Refined
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
   declared in the visible part of a package, its abstract view. If the
   subprogram declaration in the visible part has no explicit postcondition, a
   postcondition of True is assumed for the abstract view.

.. _tu-cbatu-refined_postcondition_aspects-02:

2. The same legality rules apply to a Refined Postcondition as for
   a postcondition.

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

.. _tu-pr-refined_postcondition_aspects-05:

5. The default Refined_Post for an expression function, F, is
   F'Result = ``expression``, where ``expression`` is the expression defining
   the body of the function.

.. _tu-cbatu-refined_postcondition_aspects-06:

6. The static semantics are otherwise as for a postcondition.

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

8. The precondition of a subprogram declaration and its Refined Postcondition
   together imply the postcondition of the declaration, that is:

   (Precondition and Refined Postcondition) -> Postcondition

.. _etu-refined_postcondition_aspects-vr:

.. centered:: **Examples**

.. code-block:: ada

    -- This example shows the two ways in which the Refined_Post aspect is useful.
    -- (1) To write a postcondition in terms of the full view of a private type.
    -- (2) To write a postcondition in terms of the constituents of a state abstraction.
    -- In either case a postcondition may be strengthened by the Refined_Post
    -- aspect by adding further constraints.
    -- The combination of these two types of usage in a single package is not
    -- necessarily common but is used here for brevity of the example.
    package Stacks with
      Abstract_State => The_Stack,   -- State abstraction used for usage (2).
      Initializes    => The_Stack
    is
       type Stack_Type is private;   -- Abstract type used for usage (1).

    ----------------------------- Usage (1) ----------------------------------------
       function Is_Empty (S : Stack_Type) return Boolean;
       -- Default postcondition is True.

       function Is_Full (S : Stack_Type) return Boolean;
       -- Default postcondition is True.

       procedure Push (S : in out Stack_Type; I : in Integer) with
	 Pre  => not Is_Full (S),
	 Post => not Is_Empty (S);

       procedure Pop (S : in out Stack_Type) with
	 Post => not Is_Full (S);

       function Top (S : Stack_Type) return Integer with
	 Pre => not Is_Empty (S);

    ----------------------------- Usage (2) ----------------------------------------
       function Is_Empty return Boolean with
	 Global => The_Stack;
       -- Default postcondition is True.

       function Is_Full return Boolean with
	 Global => The_Stack;
       -- Default postcondition is True.

       procedure Push (I : Integer) with
	 Global => (In_Out => The_Stack),
	 Pre    => not Is_Full,
	 Post   => not Is_Empty;

       procedure Pop with
	 Global => (In_Out => The_Stack),
	 Post   => not Is_Full;

       function Top return Integer with
	 Global => The_Stack,
	 Pre    => not Is_Empty;
       -- Default postcondition is True.
    private
       -- Full type declaration of private type for usage (1).
       Stack_Size : constant := 100;

       type Pointer_Type is range 0 .. Stack_Size;
       subtype Stack_Index is Pointer_Type range 1 .. Pointer_Type'Last;
       type Stack_Array is array (Stack_Index) of Integer;

       -- All stack objects have default initialization.
       type Stack_Type is record
	  Pointer : Pointer_Type := 0;
	  Vector  : Stack_Array := (others => 0);
       end record;
    end Stacks;

    package body Stacks with
      Refined_State => (The_Stack => (A_Pointer, A_Vector))
    is
       -- Constituents of state abstraction The_Stack for usage (2)
       -- We promised to initialize The_Stack
       A_Pointer : Pointer_Type := 0;
       A_Vector  : Stack_Array := (others => 0);


    ----------------------------- Usage (1) ----------------------------------------
       function Is_Empty (S : Stack_Type) return Boolean is (S.Pointer = 0);
       -- Default Refined_Post => Is_Empty'Result = S.Pointer = 0
       -- refines the postcondition of True in terms of the full view of Stack_Type.

       function Is_Full (S : Stack_Type) return Boolean is (S.Pointer = Stack_Size);
       -- Default Refined_Post => Is_Full'Result = S.Pointer = Stack_Size
       -- refines the postcondition of True in terms of the full view of Stack_Type.

       procedure Push (S : in out Stack_Type; I : in Integer) with
	 Refined_Post => S.Pointer = S.Pointer'Old + 1 and
			 S.Vector = S.Vector'Old'Update (Pointer => I)
	 -- Refined_Post in terms of full view of Stack_Type and a further
	 -- constraint added specifying what is required by the implementation.
       is
       begin
	  S.Pointer := S.Pointer + 1;
	  S.Vector (S.Pointer) := I;
       end Push;

       procedure Pop (S : in out Stack_Type) with
	 Refined_Post => S.Pointer = S.Pointer'Old - 1
	 -- Refined_Post in terms of full view of Stack_Type and also
	 -- specifies what is required by the implementation.
       is
       begin
	  if S.Pointer > 0 then
	     S.Pointer := S.Pointer - 1;
	  end if;
       end Pop;

       function Top (S : Stack_Type) return Integer is  (S.Vector (S.Pointer));
       -- Default Refined_Post => Top'Result = S.Vector (S.Pointer (S.Pointer))
       -- refines the postcondition of True in terms of the full view of Stack_Type.

    ----------------------------- Usage (2) ----------------------------------------

       -- Is_Empty could have been written as a expression function as was done
       -- for Is_Empty (S : Stack_Type) but is presented here as a subproram body
       -- to contrast the two approaches
       function Is_Empty return Boolean with
	 Refined_Global => A_Pointer,
	 Refined_Post   => Is_Empty'Result = (A_Pointer = 0)
	 -- Refines the postcondition of True in terms of the constituent A_Pointer.
       is
       begin
	  return A_Pointer = 0;
       end Is_Empty;

       -- Could be written as an expression function
       function Is_Full return Boolean with
	 Refined_Global => A_Pointer,
	 Refined_Post   => Is_Full'Result = (A_Pointer = Stack_Size)
	 -- Refines the postcondition of True in terms of the constituent A_Pointer.
       is
       begin
	  return A_Pointer = Stack_Size;
       end Is_Full;

       procedure Push (I : Integer) with
	 Refined_Global => (In_Out => (A_Pointer, A_Vector)),
	 Refined_Post   => A_Pointer = A_Pointer'Old + 1 and
			   A_Vector = A_Vector'Old'Update (A_Pointer => I)
	 -- Refined_Post in terms of constituents A_Pointer and A_Vector and a further
	 -- constraint added specifying what is required by the implementation.
       is
       begin
	  A_Pointer := A_Pointer + 1;
	  A_Vector (A_Pointer) := I;
       end Push;

       procedure Pop with
	 Refined_Global => (In_Out => A_Pointer),
	 Refined_Post   => A_Pointer = A_Pointer'Old - 1
	 -- Refined_Post in terms of constituents A_Pointer and also
	 -- specifies what is required by the implementation.
       is
       begin
	  A_Pointer := A_Pointer - 1;
       end Pop;

       function Top return Integer is (A_Vector (A_Pointer)) with
	 Refined_Global => (A_Pointer, A_Vector);
       -- Default Refined_Post => Top'Result = A_Vector (S.Pointer)
       -- refines the postcondition of True in terms of the constituents
       -- A_Pointer and A_Vector.

    end Stacks;

.. todo:: refined contract_cases.
          To be completed in a post-Release 1 version of this document.

.. Refined Precondition Aspect
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: The Refined_Pre aspect will not be implemented in Release 1 of the
     |SPARK| Toolset.  Its usefulness and exact semantics are still to be
     determined.

.. Text commented out until decision on Refined_Pre is finalised.
   A subprogram declared in the visible part of a package may have a Refined
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
      in the visible part of a package, its abstract view. If the subprogram
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

.. code-block:: ada

   package Externals
      with Abstract_State => ((Combined_Inputs with External => Async_Writers),
                              (Displays with External => Async_Readers),
                              (Complex_Device with External => (Async_Readers,
                                                                Effective_Writes,
                                                                Async_Writers))),
           Initializes    => Complex_Device
   is
      procedure Read (Combined_Value : out Integer)
         with Global  => Combined_Inputs,  -- Combined_Inputs is an Input;
                                           -- it does not have Effective_Reads and
                                           -- may be an specified just as an
                                           -- Input in Global and Depends aspects.
              Depends => (Combined_Value => Combined_Inputs);

      procedure Display (D_Main, D_Secondary : in String)
         with Global  => (Output => Displays), -- Displays is an Output and may
                                               -- be specified just as an
                                               -- Output in Global and Depends
                                               -- aspects.
              Depends => (Displays => (D_Main, D_Secondary));

      function Last_Value_Sent return Integer
         with Global => Complex_Device;  -- Complex_Device is an External
                                         -- state.  It can be a global_item of
                                         -- a function provided the Refined_Global
                                         -- aspect only refers to non-volatile
                                         -- constituents and to external
                                         -- state abstractions via calls to
                                         -- functions defined on them.

      procedure Output_Value (Value : in Integer)
         with Global  => (In_Out => Complex_Device),
              Depends => (Complex_Device => (Complex_Device, Value));
         -- Output_Value only sends out a value if it is not the same
         -- as the last value sent.  When a value is sent it updates
         -- the saved value and has to check a status port.
         -- The subprogram must be a procedure.

   end Externals;

   private package Externals.Temperature
      with Abstract_State => (State with External => Async_Writers,
                                         Part_Of  => Externals.Combined_Inputs)
   is
      procedure Read (Temp : out Integer)
         with Global  => State,
              Depends => (Temp => State);
   end Externals.Temperature;

   private package Externals.Pressure
      with Abstract_State => (State with External => Async_Writers,
                                         Part_Of  => Externals.Combined_Inputs)
   is
      procedure Read (Press : out Integer)
         with Global  => State,
              Depends => (Press => State);
   end Externals.Pressure;

   private package Externals.Main_Display
      with Abstract_State => (State with External => Async_Readers,
                                         Part_Of  => Externals.Displays)
   is
      procedure Display (Text: in String)
         with Global => (Output => State),
              Depends => (State => Text);
   end Externals.Main_Display;

   private package Externals.Secondary_Display
      with Abstract_State => (State with External => Async_Readers,
                                         Part_Of  => Externals.Displays)
   is
      procedure Display (Text: in String)
         with Global => (Output => State),
              Depends => (State => Text);
   end Externals.Secondary_Display;

   with System.Storage_Elements,
        Externals.Temperature,
        Externals.Pressure,
        Externals.Main_Display,
        Externals.Secondary_Display;
   package body Externals
      with Refined_State => (Combined_Inputs => (Externals.Temperature.State,
                                                 Externals.Pressure.State),
                          -- Both Temperature and
                          -- Pressure are inputs only.

                             Displays => (Externals.Main_Display.State,
                                          Externals.Secondary_Display.State),
                          -- Both Main_Display and
                          -- Secondary_Display are outputs only.

                             Complex_Device => (Saved_Value,
                                                Out_Reg,
                                                In_Reg))
                          -- Complex_Device is a mixture of inputs, outputs and
                          -- non-volatile constituents.
   is
      procedure Read (Combined_Value : out Integer)
         with Refined_Global  => (Temperature.State, Pressure.State),
              Refined_Depends => (Combined_Value =>
                                     (Temperature.State, Pressure.State))
      is
        Temp,
        Press : Integer;
        K : constant := 1234;
      begin
        Temperature.Read (Temp);
        Pressure.Read (Press);
        Combined_Value := Press + Temp * K;-- Some_Function_Of (Temp, Pressure);
      end Read;

      procedure Display (D_Main, D_Secondary : in String)
         with Refined_Global  => (Output => (Main_Display.State,
                                     Secondary_Display.State)),
              Refined_Depends => ((Main_Display.State,
                                   Secondary_Display.State) => (D_Main, D_Secondary))
      is
      begin
        Main_Display.Display (D_Main);
        Secondary_Display.Display (D_Secondary);
      end Display;

      -------------------- Complex Device --------------------

      Saved_Value : Integer := 0;  -- Initialized as required.

      Out_Reg : Integer
         with Volatile,
              Async_Readers,
              Effective_Writes, -- Every value written to the port is significant.
              Address  => System.Storage_Elements.To_Address (16#ACECAF0#);

      In_Reg : Integer
         with Volatile,
              Async_Writers,
              Address  => System.Storage_Elements.To_Address (16#A11CAF0#);

      function Last_Value_Sent return Integer
         with Refined_Global => Saved_Value -- Refined_Global aspect only
                                            -- refers to a non-volatile
                                            -- constituent.
      is
      begin
         return Saved_Value;
      end Last_Value_Sent;

      procedure Output_Value (Value : in Integer)
         with Refined_Global  => (Input  => In_Reg,
                                  Output => Out_Reg,
                                  In_Out => Saved_Value),
              -- Refined_Global aspect refers to both volatile
              -- and non-volatile constituents.

              Refined_Depends => ((Out_Reg,
                                   Saved_Value) => (Saved_Value,
                                                    Value),
                                  null => In_Reg)
      is
         Ready  : constant Integer := 42;
         Status : Integer;
      begin
         if Saved_Value /= Value then
            loop
               Status := In_Reg;  -- In_Reg has the property Async_Writers
                                  -- and may appear on RHS of assignment
                                  -- but not in a condition.
               exit when Status = Ready;
            end loop;

            Out_Reg := Value;  -- Out_Reg has the property Async_Readers
                               -- and the assigned value will be consumed.
            Saved_Value := Value;  -- Writing to the Out_Reg also results
                                   -- in updating Saved_Value.
         end if;
      end Output_Value;

   -- ...

   end Externals;


   -- This is a hardware abstraction layer (HAL)
   -- which handles input and output streams over serial interfaces
   -- and monitors and resets an area of shared memory used
   -- as a watchdog.
   package HAL
      with Abstract_State =>
              ((FIFO_Status
                  with External => Async_Writers),
               (Serial_In
                  with External => (Async_Writers, Effective_Reads)),
                  -- Each value received is significant
               (FIFO_Control
                  with External => Async_Readers),
               (Serial_Out
                  with External => (Async_Readers, Effective_Writes)),
               (Wdog_State
                  with External => (Async_Readers,
                                    Async_Writers)))
   is
      type Byte_T is mod 256;

      -- This procedure reads the next byte available on
      -- the serial input port using a FIFO buffer.
      procedure Get_Byte (A_Byte : out Byte_T)
         with Global  => (In_Out => Serial_In),
              Depends => (A_Byte    => Serial_In,
                          Serial_In => null);

      -- This procedure skips input bytes until
      -- the byte matches the given pattern or the input
      -- FIFO is empty.
      procedure Skip_To (Pattern : in Byte_T; Found : out Boolean)
         with Global  => (Input  => FIFO_Status,
                          In_Out => Serial_In),
              Depends => ((Found,
                           Serial_In) => (FIFO_Status, Pattern, Serial_In));

      -- This procedure reads the status of the input and output FIFOs.
      procedure Get_FIFO_Status (A_Byte : out Byte_T)
         with Global  => (Input  => FIFO_Status),
              Depends => (A_Byte => FIFO_Status);

      -- This procedure writes a byte to the serial
      -- output port using a FIFO buffer.
      procedure Put_Byte (A_Byte : Byte_T)
         with Global  => (Output => Serial_Out),
              Depends => (Serial_Out => A_Byte);


      -- This procedure clears the input FIFO.
      procedure Clear_In_FIFO
         with Global  => (Output => FIFO_Control),
              Depends => (FIFO_Control => null);


      -- This procedure clears the output FIFO.
      procedure Clear_Out_FIFO
         with Global  => (Output => FIFO_Control),
              Depends => (FIFO_Control => null);


      -- This procedure checks and then resets the status of
      -- the watchdog state.
      procedure Wdog_Timed_Out (Result : out Boolean)
         with Global  => (In_Out => Wdog_State),
              Depends => (Result     => Wdog_State,
                          Wdog_State => Wdog_State);

   end HAL;

   with System.Storage_Elements;
   package body HAL
      with Refined_State => (Serial_In    => Read_FIFO,
                             Serial_Out   => Write_FIFO,
                             FIFO_Status  => Status,
                             FIFO_Control => Control,
                             Wdog_State   => Wdog_Shared_memory)
   is

      -- Each byte read is significant, it is a sequence of bytes
      -- and so Effective_Reads => True.
      Read_FIFO: Byte_T
         with Volatile,
              Async_Writers,
              Effective_Reads,
              Address => System.Storage_Elements.To_Address(16#A1CAF0#);

      -- Each byte written is significant, it is a sequence of bytes
      -- and so Effective_Writes => True.
      Write_FIFO: Byte_T
         with Volatile,
              Async_Readers,
              Effective_Writes,
              Address => System.Storage_Elements.To_Address(16#A2CAF0#);

      -- The read of the FIFO status is a snap shot of the current status
      -- individual reads are independent of other reads of the FIFO status
      -- and so Effective_Reads => False.
      Status: Byte_T
         with Volatile,
              Async_Writers,
              Address => System.Storage_Elements.To_Address(16#A3CAF0#);

      -- The value written to the FIFO control register are independent
      -- of other value written to the control register and so
      -- Effective_Writes => False.
      Control: Byte_T
         with Volatile,
              Async_Readers,
              Address => System.Storage_Elements.To_Address(16#A4CAF0#);

      -- This is a bidirectional port but individual reads and writes
      -- are independent and so Effective_Reads and Effective_Writes
      -- are both False.
      Wdog_Shared_Memory : Boolean
         with Volatile,
              Async_Writers,
              Async_Readers,
              Address => System.Storage_Elements.To_Address(16#A5CAF0#);

      procedure Get_Byte (A_Byte : out Byte_T)
         with Refined_Global  => (In_Out => Read_FIFO),
              Refined_Depends => (A_Byte    => Read_FIFO,
                                  Read_FIFO => null)
      is
      begin
         A_Byte := Read_FIFO;
      end Get_Byte;

      procedure Skip_To (Pattern : in Byte_T; Found : out Boolean)
         with Refined_Global  => (Input  => Status,
                                  In_Out => Read_FIFO),
              Refined_Depends => (Found,
                                  Read_FIFO => (Status, Read_FIFO))
      is
         Read_FIFO_Empty : constant Byte_T := 16#01#;
         Current_Status : Byte_T;
         Next_Byte : Byte_T;
      begin
         Found := False;
         loop
            Get_FIFO_Status (Current_Status);
            exit when Current_Status = Read_FIFO_Empty;
            Get_Byte (Next_Byte);
            exit when Next_Byte = Pattern;
         end loop;
      end Skip_To;

      procedure Get_FIFO_Status (A_Byte : out Byte_T)
         with Refined_Global  => (Input  => Status),
              Refined_Depends => (A_Byte => Status)
      is
      begin
        A_Byte := Status;
      end Get_FIFO_Status;

      procedure Put_Byte (A_Byte : Byte_T)
         with Refined_Global  => (Output => Write_FIFO),
              Refined_Depends => (Write_FIFO => A_Byte)
      is
      begin
         Write_FIFO := A_Byte;
      end Put_Byte;

      procedure Clear_In_FIFO
         with Refined_Global  => (Output => Control),
              Refined_Depends => (Control => null)
      is
         In_FIFO_Clear : constant Byte_T := 16#01#;
      begin
         Control := In_FIFO_Clear;
      end Clear_In_FIFO;

      procedure Clear_Out_FIFO
         with Refined_Global  => (Output => Control),
              Refined_Depends => (Control => null)
      is
         Out_FIFO_Clear : constant Byte_T := 16#02#;
      begin
         Control := Out_FIFO_Clear;
      end Clear_Out_FIFO;

      procedure Wdog_Timed_Out (Result : out Boolean)
         with Refined_Global  => (In_Out => Wdog_Shared_Memory),
              Refined_Depends => (Result             => Wdog_Shared_Memory,
                                  Wdog_Shared_memory => Wdog_Shared_Memory)
      is
         Watch_Dog_OK : Boolean;
      begin
         Watch_Dog_OK := Wdog_Shared_Memory;
         if Watch_Dog_OK then
            -- Retrigger the watch dog timer
            Wdog_shared_memory := True;
            -- It has not timed out.
            Result := False;
         else
            Result := True;
         end if;
      end Wdog_Timed_Out;

   end HAL;

   with HAL;
   use type HAL.Byte_T;
   procedure Main
      with Global  => (Input  => HAL.FIFO_Status,
                       In_Out => (HAL.Serial_In, HAL.Wdog_State),
                       Output => (HAL.FIFO_Control, HAL.Serial_Out)),
           Depends => (HAL.Serial_In    =>+ (HAL.FIFO_Status,
                                             HAL.Wdog_State),
                       HAL.Serial_Out   =>  (HAL.Serial_In,
                                             HAL.FIFO_Status,
                                             HAL.Wdog_State),
                       HAL.Wdog_State   =>+ HAL.FIFO_Status,
                       HAL.FIFO_Control =>  null)
   is
      Wdog_Timed_Out, Found : Boolean;
      A_Byte                : HAL.Byte_T;
   begin
      HAL.Clear_Out_FIFO;

      -- The start of the data is marked by the sequence 16#5555#
      -- Skip until we find the start of the message or the FIFO is empty.
      loop
         HAL.Wdog_Timed_Out (Wdog_Timed_Out);
         exit when Wdog_Timed_Out;
         HAL.Skip_To (16#55#, Found);
         exit when not Found;
         HAL.Get_Byte (A_Byte);
         exit when A_Byte = 16#55#;
      end loop;

      if Found and not Wdog_Timed_Out then
         -- We have found the start of the data

         -- As long as the watchdog doesn't time out, move data
         -- from Serial_In to Serial_Out.
         loop
            HAL.Wdog_Timed_Out (Wdog_Timed_Out);

            exit when Wdog_Timed_Out;

            HAL.Get_Byte (A_Byte);
            HAL.Put_Byte (A_Byte);
         end loop;
      end if;

   end Main;

Private Types and Private Extensions
------------------------------------

.. centered:: **Legality Rules**

.. _tu-private_types_and_private_extensions-01:

1. The partial view of a private type may be in |SPARK| even if its
   full view is not in |SPARK|.

.. _tu-private_types_and_private_extensions-02:

2. The usual rule applies here, so a private type without
   discriminants is in |SPARK|, while a private type with
   discriminants is in |SPARK| only if its discriminants are in
   |SPARK|.

.. _tu-private_types_and_private_extensions-03:

3. ``Private_extension_declarations`` are not currently permitted.

.. _etu-private_types_and_private_extensions:

Private Operations
~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Type Invariants
~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-nt-type_invariants-01:

1. The ``aspect_specification`` Type_Invariant is not permitted in |SPARK|.

.. _etu-type_invariants:

[Type invariants are not currently supported in |SPARK| but are intended
to be introduced in a future release.]

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


Deferred Constants
------------------

.. centered:: **Legality Rules**

.. _tu-nt-deferred_constants-01:

1. The view of an entity introduced by a
   ``deferred_constant_declaration`` is in |SPARK|, even if the
   *initialization_*\ ``expression`` in the corresponding completion
   is not in |SPARK|.

.. _etu-deferred_constants:

Limited Types
-------------

No extensions or restrictions.

Assignment and Finalization
---------------------------

.. centered:: **Legality Rules**

.. _tu-nt-assignment_and_finalization-01:

1. Controlled types are not permitted in |SPARK|.

.. _etu-assignment_and_finalization:

.. _elaboration_issues:

Elaboration Issues
------------------

|SPARK| imposes a set of restrictions which ensure that a
call to a subprogram cannot occur before the body of the
subprogram has been elaborated. The success of the runtime
elaboration check associated with a call is guaranteed by
these restrictions and so the proof obligation associated with
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

   7. Rule removed.

.. 7. In the case of a dispatching call, the subprogram_body mentioned
   in the above rules is that (if any) of the statically denoted callee.

.. _tu-nt-elaboration_issues-08:

   8. Rule removed.

.. 8. The first freezing point of a tagged type shall occur within the
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

9. For purposes of defining the early call region, the specification and body of a
   library unit package which has an Elaborate_Body pragma are treated as if
   they both belonged to some enclosing declaration list with the body
   immediately following the specification. This means that the early call
   region in which a call is permitted can span the specification/body boundary.

.. This is important for tagged type declarations.

.. _tu-nt-elaboration_issues-10:

10. For the inter-compilation_unit case, |SPARK| enforces the following static
    elaboration order rule:

    a. If a unit has elaboration code that can directly or indirectly
       make a call to a subprogram in a with'd unit, or instantiate a
       generic package in a with'd unit, then if the with'd unit does
       not have pragma Pure or Preelaborate, then the client should
       have a pragma Elaborate_All for the with'd unit. For generic
       subprogram instantiations, the rule can be relaxed to require
       only a pragma Elaborate. [This rule is the same as the GNAT
       static elaboration order rule as given in the GNAT Pro User's
       Guide.]

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

.. _etu-elaboration_issues-lr:

[These rules correctly prohibit the following example:

.. code-block:: ada

   package P is
      function F return Boolean;
      Flag : Boolean := F; -- would fail elaboration checks
   end; --]

.. centered:: **Examples**

.. code-block:: ada

    function Times_2 (X : Integer) return Integer
    is
    begin
       return 2 * X;
    end Times_2;

    with Times_2;
    package Intra_Unit_Elaboration_Order_Examples
    with Initializes => (X, Y)
    is
       pragma Elaborate_Body;        -- Ensures body of package is elaborated
				     -- immediately after its declaration
       procedure P (I : in out Integer); -- P and hence Q are executable during
       procedure Q (J : in out Integer); -- elaboration as P is called in the package body

       X : Integer := Times_2 (10);  -- Not preelaborable
				     -- The early call region begins here
				     -- and extends into the package body because
				     -- of the Elaborate_Body pragma.

       Y : Integer;

       procedure R (Z : in out Integer)
	 with Post => Z = G (Z'Old); -- The call to G is allowed here as it is in
				     -- the early call region

       procedure S (A : in out Integer)
         with Global => Y;           -- Global Y needs to be initialized.


       function F (I : Integer) return Integer;
       function G (J : Integer) return Integer is (2 * F (J));
				     -- The call to F is allowed here as it is in
				     -- early call region.
    end Intra_Unit_Elaboration_Order_Examples;

    package body Intra_Unit_Elaboration_Order_Examples is

       function F (I : Integer) return Integer is (I + 1);
       -- The early call region for F ends here as the body has been
       -- declared. It can now be called using normal visibility rules.

       procedure P (I : in out Integer)
       is
       begin
	  if I > 10 then
	     Q (I);  -- Q is still in the eartly call region and so this call is allowed
	  end if;
       end P;
       -- The early call region for P ends here as the body has been
       -- declared. It can now be called using normal visibility rules.

       procedure Q (J : in out Integer)
       is
       begin
	  if J > 20 then
	     J := J - 10;
	     P (J);  -- P can be called as its body is declared.
	  end if;
       end Q;
       -- The early call region for Q ends here as the body has been
       -- declared. It can now be called using normal visibility rules.

       procedure R (Z : in out Integer)
       is
       begin
	  Z := G (Z);  -- The expression function G has been declared and so can be called
       end R;

      procedure S (A : in out Integer)
      is
      begin
        A := A + Y;  -- Reference to Y is ok because it is in the early call region
                     -- and the Elaborate_Body pragma ensures it is initialized
                     -- before it is used.
      end S;

    begin
       Y := 42;
       P (X);   -- Call to P and hence Q during the elaboration of the package.
    end Intra_Unit_Elaboration_Order_Examples;

    package Inter_1 is
       function F (I : Integer) return Integer;
    end Inter_1;

    package body Inter_1 is
       function F (I : Integer) return Integer is (I);
    end Inter_1;

    package Inter_2 is
       function G (I : Integer) return Integer;
    end Inter_2;

    package body Inter_2 is
       function G (I : Integer) return Integer is (I);
    end Inter_2;

    with Inter_1;
    pragma Elaborate_All (Inter_1);    -- Ensure the body of the called function F
				       -- has been elaborated.
    package Inter_Unit_Elaboration_Examples is
       X : Integer := Inter_1.F (10);  -- The call to F is ok because its body is
				       -- sure to have been elaborated.
       Y : Integer;

       procedure P (I : in out Integer); -- P is declared so that the package
                                         -- requires a body for this example.

    end Inter_Unit_Elaboration_Examples;

    with Inter_2;
    pragma Elaborate_All (Inter_2);  -- Ensure body of called function G has
				     -- been elaborated.
    package body Inter_Unit_Elaboration_Examples is

      procedure P (I : in out Integer) is
       begin
	  I := 2 * I;
       end P;

    begin
       Y := Inter_2.G (20);          -- Call to G is ok because the body of
				     -- G is sure to have been elaborated.
    end Inter_Unit_Elaboration_Examples;


Use of Initial_Condition and Initializes Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Static Semantics**

To ensure the correct semantics of the Initializes and Initial_Condition
aspects, when applied to library units, language restrictions (described below)
are imposed in |SPARK| which have the following consequences:

.. _tu-cbatu-use_of_initial_condition_and_initializes_aspects-01:

1. During the elaboration of a library unit package (spec or body),
   library-level variables declared outside of that package cannot be
   modified and library-level variables declared outside of that
   package can only be read if

   a. the variable (or its state abstraction) is mentioned in the
      Initializes aspect of its enclosing package (from
      :ref:`initializes_aspect`); and

   b. an Elaborate (not necessarily an Elaborate_All) pragma ensures
      that the body of that package has been elaborated (from
      :ref:`elaboration_issues`).

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
   subprogram itself and during elaboration of any other unit which
   applies an Elaborate pragma to the library unit in question (note:
   an Initial_Condition which depends on no variable inputs can also
   be assumed to be true throughout the execution of the main
   subprogram).

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
   then the compilation unit containing the read shall apply an Elaborate (not
   necessarily Elaborate_All) pragma to the unit declaring the variable or state
   abstraction. The variable or state abstraction shall be specified as being
   initialized in the Initializes aspect of the declaring package. [This is
   needed to ensure that the variable has been initialized at the time of the
   read.]

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

6. A package body shall include Elaborate pragmas for all of the other
   library units [(typically private children)] which provide
   constituents for a state abstraction denoted in the Initializes
   aspect of the given package.

.. _etu-use_of_initial_condition_and_initializes_aspects-lr:

.. centered:: **Examples**

.. code-block:: ada

    package P
    with Initializes => VP
    is
       pragma Elaborate_Body; -- Needed because VP is
       VP : Integer;          -- Initialized in the body
    end P;

    with P;
    pragma Elaborate (P); -- required because P.VP is used in initialization of V
    package Initialization_And_Elaboration
    with Abstract_State => State,
	 Initializes    => (State,
			    V     =>  P.VP), -- Initialization of V dependent on P.VP
         Initial_Condition => (V = P.VP and Get_It = 0)
    is
       V : Integer := P.VP;

       procedure Do_It (I : in Integer)
	 with Global => (In_Out => State);

       function Get_It return Integer
	 with Global => State;

    end Initialization_And_Elaboration;

    private package Initialization_And_Elaboration.Private_Child
    with Abstract_State => (State with Part_Of => Initialization_And_Elaboration.State),
	 Initializes    => State,
         Initial_Condition => Get_Something = 0
    is
       procedure Do_Something (I : in Integer)
	 with Global => (In_Out => State);

       function Get_Something return Integer
	 with Global => State;
    end Initialization_And_Elaboration.Private_Child;

    with Initialization_And_Elaboration.Private_Child;
    -- pragma Elaborate for the private child is required because it
    -- is a constituent of the state abstraction Initialization_And_Elaboration.State,
    -- which is mentioned in the Initializes aspect of the package.
    pragma Elaborate (Initialization_And_Elaboration.Private_Child);
    package body Initialization_And_Elaboration
    with Refined_State => (State => Private_Child.State) -- State is initialized
    is                                                   -- Private child must be elaborated.
       procedure Do_It (I : in Integer)
	 with Refined_Global => (In_Out => Private_Child.State)
       is
       begin
	  Private_Child.Do_Something (I);
       end Do_It;

       function Get_It return Integer
	  with Refined_Global => Private_Child.State
       is
       begin
	 return Private_Child.Get_Something;
       end Get_It;
    end Initialization_And_Elaboration;
