Packages
========

.. centered:: **Verification Rules**

#. In |SPARK| the elaboration of a package shall only update, directly or
   indirectly, variables declared immediately within the package.

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

Though the variables may be hidden they still form part (or all) of the
persistent state of the package and the hidden state cannot be ignored for flow
analysis and proof. *State abstraction* is the means by which this hidden state
is managed for flow analysis and proof. A state abstraction represents one or
more declarations which are part of the hidden state of a package.

|SPARK| extends the concept of state abstraction to provide hierarchical data
abstraction whereby the state abstraction declared in a package may contain the
persistent state of other packages given certain restrictions described in
:ref:`package_hierarchy`. This provides data refinement similar to the
refinement available to types whereby a record may contain fields which are
themselves records.

.. centered:: **Static Semantics**


#. The visible state of a package P consists of:

   * any variables declared immediately within the visible part of
     package P; and

   * the state abstractions declared by the Abstract_State aspect specification
     (if any) of package P; and

   * the visible state of any packages declared immediately within the visible part
     of package P.


#. The hidden state of a package P consists of:

   * any variables declared immediately in the private part or body of P; and

   * the state declared in the visible part of any packages declared immediately
     within the private part or body of P.

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
instance reading or writing a stream of characters to a file, or
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

#. If an external state is declared without any of the external
   properties specified then all of the properties default to a value
   of True.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.2 LR An external state without any properties defaults to
                   having all properties set to True.

#. If just the name of the property is given then its value defaults
   to True [; for instance Async_Readers defaults to Async_Readers =>
   True].

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.2 LR If just a property name is given, then its value defaults
                   to True.

#. A property may be explicitly given the value False [for instance Async_Readers => False].

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.2 LR A property may be explicitly given the value False.

#. If any one property is explicitly defined, all undefined properties default to a value of False.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.2 LR If a property is explicitly defined then all undefined
                   properties default to False.

#. The expression defining the Boolean valued property shall be static.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.2 LR The expression defining the Boolean valued property
                   shall be static.

#. Only the following combinations of properties are valid:

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

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.2 LR Effective_Reads can only be True if Async_Writers
                   is True and Effective_Writes can only be True if Async_Readers
                   is True.

.. centered:: **Static Semantics**

#. Every update of an external state is considered to be read by
   some external reader if Async_Readers => True.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.1.2 SS Every update of an external state is considered
                   to be read by some external reader if Async_Readers => True.

#. Each successive read of an external state might have a different
   value [written by some external writer] if Async_Writers => True.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: PR 7.1.2 SS Each successive read of an external state might
                   have a different value if Async_Writers => True.

#. If Effective_Writes => True, then every value written to the
   external state is significant. [For instance writing a sequence
   of values to a port.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.1.2 SS If Effective_Writes => True then every value
                   written to the external state is significant.

#. If Effective_Reads => True, then every value read from the external
   state is significant. [For example a value read from a port
   might be used in determining how the next value is processed.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: PR 7.1.2 SS If Effective_Reads => True then every value
                   read from the external state is significant.

#. Each update of an external state has no external effect if both
   Async_Readers => False and Effective_Writes => False.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.1.2 SS An update of an external state has no
                   external effect if Async_Readers => False and
                   Effective_Writes => False.

#. Each successive read of an external state will result in the last
   value explicitly written [by the program] if Async_Writers => False.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: PR 7.1.2 SS Each successive read of an external state will
                   result in the last value explicitly written if
                   Async_Writers => False.

#. Every explicit update of an external state might affect the next value
   read from the external state even if Async_Writers => True.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.1.2 SS Every explicit update of an external
                   state might affect the next value read from the
                   external state even if Async_Writers => True.

#. An external state which has the property Async_Readers => True need
   not be initialized before being read although explicit
   initialization is permitted. [The external state might be
   initialized by an external writer.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.1.2 SS An external state with Async_Readers => True
                   need not be initialized.

.. _external_state-variables:

External State - Variables
~~~~~~~~~~~~~~~~~~~~~~~~~~

In Ada interfacing to an external device or subsystem normally entails using one
or more volatile variables to ensure that writes and reads to the device are not
optimized by the compiler into internal register reads and writes. A variable is
specified as Volatile using the Ada aspect or pragma Volatile or Atomic.

|SPARK| refines the Volatile specification by introducing four new Boolean
aspects which may be applied only to objects declared as Volatile. The aspects
may be specified in the aspect specification of a Volatile object declaration
(this excludes volatile objects that are formal parameters).

The new aspects are:

  * Async_Readers - as described in :ref:`external_state`.

  * Async_Writers - as described in :ref:`external_state`.

  * Effective_Reads - as described in :ref:`external_state`.

  * Effective_Writes - as described in :ref:`external_state`.

.. centered:: **Legality Rules**

#. All Volatile objects are considered to have one or more external
   state properties, either given explicitly in their declaration or
   implicitly when all the properties are considered to be True.  The
   following rules also apply to all Volatile objects.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.3 LR The aspects and rules apply to all volatile objects.
                   Covered by another TU.

#. The aspects shall only be specified in the aspect specification of a Volatile
   object declaration excluding Volatile formal parameter declarations.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.3 LR The aspects shall be specified in the aspect
                   specification of a Volatile object declaration excluding
                   Volatile formal parameter declarations.

#. The declaration of a Volatile object (other than as a formal
   parameter) shall be at library level. [That is, it shall not be
   declared within the scope of a subprogram body. A Volatile variable
   has an external effect and therefore should be global even if it is
   not visible. It is made visible via a state abstraction.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.3 LR Declaration of Volatile object shall be at
                   library level.

#. A Volatile object shall not be used as an actual parameter in a generic instantiation.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.3 LR A Volatile object shall not be used as an actual
                   parameter in a generic instantiation.

#. A Volatile object shall not be a ``global_item`` of a function.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.3 LR A Volatile shall not be a global_item of a function.

#. A function shall not have a formal parameter of a Volatile type.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.3 LR A function shall not have a Volatile formal parameter.

#. If a Volatile object has Effective_Reads set to True then it must
   have a ``mode_selector`` of Output or In_Out when denoted as a
   ``global_item``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.3 LR A Volatile with Effective_Reads must have a
                   mode_selector of Output or In_Out when denoted as a
                   global_item.

#. A Volatile object shall only occur as an actual parameter of a
   subprogram if the corresponding formal parameter is of a non-scalar
   Volatile type or as an actual parameter in a call to an instance of
   Unchecked_Conversion.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.3 LR A Volatile shall only occur as an actual
                   parameter of a subprogram if the corresponding formal
                   parameter is of a non-scalar Volatile type or as an
                   actual parameter in a call to an instance of
                   Unchecked_Conversion.

#. Contrary to the general |SPARK| rule that expression evaluation cannot
   have side effects, a read of a Volatile object with the properties
   Async_Writers or Effective_Reads set to True is considered to have an effect
   when read. To reconcile this discrepancy, a name denoting such an object
   shall only occur in the following contexts:

   * as the name on the left-hand side of an assignment statement; or

   * as the [right-hand side] expression of an assignment statement; or

   * as the expression of an initialization expression of an object declaration
     that is not specified as Volatile; or

   * as an actual parameter in a call to an instance of Unchecked_Conversion
     whose result is renamed [in an object renaming declaration]; or

   * as an actual parameter in a procedure call of which the corresponding
     formal parameter is of a non-scalar Volatile type.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.3 LR A Volatile with Async_Writers or Effective_Reads
                   can appear as the left-hand side of an assignment statement,
                   the right-hand side of an assignment statement, the expression
                   of an initialization expression, an actual parameter in an
                   Unchecked_Conversion and an actual parameter in a procedure
                   call where the corresponding formal parameter is a
                   non-scalar Volatile.

.. centered:: **Static Semantics**

These are explained in :ref:`external_state`.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with these aspects.

.. centered:: **Verification Rules**

#. As formal subprogram parameters of a Volatile type cannot have
   these aspects specified assumptions have to be made in the body of
   the subprogram of the properties that the formal parameter of a
   given mode may have as follows:

   * mode **in**: the formal parameter cannot be updated by the
     subprogram and is considered to have the properties Async_Writers
     => True and Effective_Reads => False. The actual parameter in a
     call must be Volatile and have these properties but may also have
     the properties Async_Readers and Effective_Writes set to True.

   * mode **out**: the formal parameter cannot be read by the
     subprogram as it is unknown whether a read will have an external
     effect. The formal parameter is considered to have the
     properties Async_Readers => True and/or Effective_Writes =>
     True. The actual parameter in a call to the subprogram must be
     Volatile and have either or both of these properties True but may
     also have Async_Writers and Effective_Reads set to True. If the
     subprogram attempts a read of the formal parameter a flow anomaly
     will be reported.

   * mode **in out**: the formal parameter is considered to have all
     properties; Async_Readers => True, Async_Writers => True,
     Effective_Reads => True, Effective_Writes => True. The actual
     parameter in a subprogram call must be Volatile have all of these
     properties set to True.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE FA 7.1.3 VR A Volatile actual parameter of mode in has
                   to have Async_Writers => True and Effective_Reads => False.
                   A Volatile actual parameter of mode out has to have
                   Async_Readers => True and/or Effective_Writes => True and
                   if a read is attempted, a flow anomaly is reported.
                   A Volatile actual parameter of mode in out must have all
                   properties set to True.


.. centered:: **Examples**

.. code-block:: ada

   with System.Storage_Elements;
   package Input_Port
   is
      Sensor : Integer
         with Volatile,
              Async_Writers,
              Address => System.Storage_Elements.To_Address (16#ACECAFE#);
   end Input_Port;

   with System.Storage_Elements;
   package Output_Port
   is
      Sensor : Integer
         with Volatile,
              Async_Readers,
              Address => System.Storage_Elements.To_Address (16#ACECAFE#);
   end Input_Port;

   with System.Storage_Elements;
   package Multiple_Ports
   is
      type Volatile_Type is record
        I : Integer;
      end record with Volatile;

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
              Address => System.Storage_Elements.To_Address (16#A1CAFE#);

      -- V_In_2 is similar to V_In_1 except that each value read is
      -- significant. V_In_2 can only be used as a Global with a
      -- mode_Selector of Output or In_Out or as an actual parameter
      -- whose corresponding formal parameter is of a Volatile type and
      -- has mode out or in out.
      V_In_2 : Volatile_Type
         with Async_Writers,
              Effective_Reads,
              Address => System.Storage_Elements.To_Address (16#ABCCAFE#);


      -- V_Out_1 is essentially an external output since it
      -- has Async_Readers => True but Async_Writers => False.
      -- Writing the same value successively might not have an
      -- observable effect.
      V_Out_1 : Volatile_Type
         with Async_Readers,
              Address => System.Storage_Elements.To_Address (16#BBCCAFE#);

      -- V_Out_2 is similar to V_Out_1 except that each write to
      -- V_Out_2 is significant.
      V_Out_2 : Volatile_Type
         with Async_Readers,
              Effective_Writes,
              Address => System.Storage_Elements.To_Address (16#ADACAFE#);

      -- This declaration defaults to the following properties:
      -- Async_Readers => True,
      -- Async_Writers => True,
      -- Effective_Reads => True,
      -- Effective_Writes => True;
      -- That is the most comprehensive type of external interface
      -- which is bi-directional and each read and write has an
      -- observable effect.
      V_In_Out : Volatile_Type
         with Address => System.Storage_Elements.To_Address (16#BEECAFE#);

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

Abstract_State Aspect
~~~~~~~~~~~~~~~~~~~~~

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
*part of* a state abstraction of a unit which is more visible than itself.

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
  simple_option            ::= identifier
  name_value_option        ::= Part_Of => abstract_state
                             | External [=> external_property_list]
  external_property_list   ::= external_property
                             | ( external_property {, external_property} )
  external_property        ::= Async_Readers [=> expression]
                             | Async_Writers [=> expression]
                             | Effective_Writes [=> expression]
                             | Effective_Reads  [=> expression]
                             | others [=> expression]
  state_name               ::= defining_identifier
  abstract_state           ::= name

.. ifconfig:: Display_Trace_Units

   :Trace Unit: FE 7.1.4 Syntax

.. centered:: **Legality Rules**

#. An ``option`` shall not be repeated within a single ``option_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.4 LR an option shall not be repeated within an option list

#. If External is specified in an ``option_list`` then there shall be at most
   one occurrence of each of Async_Readers, Async_Writers, Effective_Writes
   and Effective_Reads.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.4 LR at most one occurrence of each of Async_Readers,
                   Async_Writers, Effective_Writes and Effect_Reads with External

#. Currently no ``simple_options`` are defined.

#. If an ``option_list`` contains one or more ``name_value_option`` items
   then they shall be the final options in the list.
   [This eliminates the possibility of a positional
   association following a named association in the property list.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.4 LR any name_value_options must be the final options
                   in the list

#. A package_declaration or generic_package_declaration that contains a
   non-null Abstract_State aspect must have a completion (i.e. such a
   package requires a body).

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.4 LR package declarations with non-null Abstract State require
                   a body


#. A subprogram declaration that overloads a state abstraction has an implicit
   Global aspect denoting the state abstraction with a ``mode_selector`` of
   Input. An explicit Global aspect may be specified which replaces the
   implicit one.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.4 LR state_name shall only be overloaded by subprogram

.. centered:: **Static Semantics**


#. Each ``state_name`` occurring in an Abstract_State aspect
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

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.4 SS state_name shall have completion and is
                   overloadable. Covered by another TU

#. A **null** ``abstract_state_list`` specifies that a package contains no
   hidden state.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.4 SS packages with a null abstract_state_list must
                   contain no hidden state

#. An External state abstraction is one declared with an ``option_list``
   that includes the External ``option`` (see :ref:`external_state`).

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.4 SS External state abstraction needs to have an
                   External option in its option_list

#. A state abstraction which is declared with an ``option_list`` that includes
   a Part_Of ``name_value_option`` indicates that it is a constituent (see
   :ref:`state_refinement`) exclusively of the state abstraction
   denoted by the ``abstract_state`` of the ``name_value_option`` (see
   :ref:`package_hierarchy`).

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.4 SS a state abstraction that is part_of an abstract
                   state must be exclusively part of this abstract state

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

Initializes Aspect
~~~~~~~~~~~~~~~~~~

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

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 7.1.5 Syntax

.. centered:: **Legality Rules**

#. An Initializes aspect shall only appear in the ``aspect_specification`` of a
   ``package_specification``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.5 LR Initializes aspect must be in package_specification

#. The Initializes aspect shall follow the Abstract_State aspect if one is
   present.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.5 LR Initializes aspect shall follow Abstract_State

#. The ``name`` of each ``initialization_item`` in the Initializes aspect
   definition for a package shall denote a state abstraction of the package or
   an entire variable declared immediately within the visible part of the
   package.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.5 LR each initialization_item shall denote a state
                   abstraction or an entire variable declared immediately
                   within the visible part of the package

#. Each ``name`` in the ``input_list`` shall denote an entire variable or a state
   abstraction but shall not denote an entity declared in the package with the
   ``aspect_specification`` containing the Initializes aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.5 LR input_list name shall denote entire variable or state
                   abstraction but not entities declared in the package containing
                   the Initializes aspect

#. Each entity in a single ``input_list`` shall be distinct.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.5 LR Entities in single input_list shall be distinct

#. An ``initialization_item`` with a **null** ``input_list`` is
   equivalent to the same ``initialization_item`` without an ``input_list``.
   [That is Initializes => (A => **null**) is equivalent to Initializes => A.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.5 LR Initializes => (A => null) is equivalent to Initializes => A.

.. centered:: **Static Semantics**

#. The Initializes aspect of a package has visibility of the declarations
   occurring immediately within the visible part of the package.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.5 SS Initializes aspect has visibility of declarations
                   occurring immediately within the visible part

#. The Initializes aspect of a package specification asserts which
   state abstractions and visible variables of the package are initialized
   by the elaboration of the package, both its specification and body, and
   any units which have state abstractions or variable declarations that are
   part (constituents) of a state abstraction declared by the package.
   [A package with a **null** ``initialization_list``, or no Initializes aspect
   does not initialize any of its state abstractions or variables.]


   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.1.5 SS a null initialization_list package does not
                   initialize any state abstractions or variables

#. An ``initialization_item`` shall have a an ``input_list`` if and
   only if its initialization is dependent on visible variables and
   state anbstractions not declared within the package containing the
   Initializes aspect.  Then the ``names`` in the ``input_list`` shall
   denote variables and state abstractions which are used in
   determining the initial value of the state abstraction or variable
   denoted by the ``name`` of the ``initialization_item`` but are not
   constituents of the state abstraction.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.5 SS names in an input_list cannot be declared in the package
                   containing the Initializes aspect and if the ininitalization_item
                   is a state abstraction then the names in the input_list shall
                   not be constituents of the state abstraction.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Initializes aspect.

.. centered:: **Verification Rules**

#. If the Initializes aspect is specified for a package, then after the body
   (which may be implicit if the package has no explicit body) has completed its
   elaboration, every (entire) variable and state abstraction denoted by a
   ``name`` in the Initializes aspect shall be initialized. A state abstraction
   is said to be initialized if all of its constituents are initialized. An
   entire variable is initialized if all of its components are initialized.
   Other parts of the visible state of the package shall not be initialized.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.1.5 VR only variables and state abstractions in the
                   Initializes aspect shall be initialized

#. If an ``initialization_item`` has an ``input_list`` then the
   variables and state abstractions denoted in the input list shall be
   used in determining the initialized value of the entity denoted by
   the ``name`` of the ``initialization_item``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.1.5 VR only entities in the input_list shall be used in
                   determining the initialized value of an entity

#. All variables and state abstractions which are not declared within
   the package but are used in the initialization of an
   ``initialization_item`` shall appear in an ``input_list`` of the
   ``initialization_item``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.1.5 VR entities used in the initialization of an
                   initialization_item must appear in its input_list.

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


Initial_Condition Aspect
~~~~~~~~~~~~~~~~~~~~~~~~

The Initial_Condition aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Initial_Condition and the ``aspect_definition`` shall
be a *Boolean_*\ ``expression``.

.. centered:: **Legality Rules**

#. An Initial_Condition aspect shall only be placed in an ``aspect_specification``
   of a ``package_specification``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.6 LR Initial_Condition aspect shall be placed on a package's
                   specification

#. The Initial_Condition aspect shall follow the Abstract_State aspect and
   Initializes aspect if they are present.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.6 LR Initial_Condition aspect shall follow Abstract_State
                   and Initializes aspects

#. Each variable or indirectly referenced state abstraction in an Initial_Condition
   aspect of a package Q which is declared immediately within the visible part of Q
   shall be initialized during the elaboration of Q and be denoted by a ``name``
   of an ``initialization_item`` of the Initializes aspect of Q.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.1.6 LR variables and state abstractions in an Initial_Condition
                   aspect shall be denoted by a name of an initialization_item of
                   the Initializes aspect

.. centered:: **Static Semantics**

#. An Initial_Condition aspect is a sort of postcondition for the elaboration
   of both the specification and body of a package. If present on a package, then
   its *Boolean_*\ ``expression`` defines properties (a predicate) of the state
   of the package which can be assumed to be true immediately following the
   elaboration of the package. [The expression of the Initial_Condition cannot
   denote a state abstraction. This means that to express properties of
   hidden state, functions declared in the visible part acting on the state
   abstractions of the package must be used.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE PR FA 7.1.6 SS Initial_Condition acts as postcondition. State
                   abstractions cannot be denoted by an Initial_Condition aspect.

.. centered:: **Dynamic Semantics**

#. With respect to dynamic semantics, specifying a given expression
   as the Initial_Condition aspect of a package is equivalent to specifying that
   expression as the argument of an Assert pragma occurring at the end of the
   (possibly implicit) statement list of the (possibly implicit) body of the
   package. [This equivalence includes all interactions with pragma
   Assertion_Policy. This equivalence does not extend to matters of static
   semantics, such as name resolution.] An Initial_Condition expression does not
   cause freezing until the point where it is evaluated [, at which point
   everything that it might freeze has already been frozen].

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: PR FA 7.1.6 DS Initial_Condition aspect is equivalent to an
                   assertion located at the very end of the package's body

.. centered:: **Verification Rules**

#. [The Initial_Condition aspect gives a proof obligation to show that the
   implementation of the ``package_specification`` and its body satisfy the
   predicate given in the Initial_Condition aspect.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: PR 7.1.6 VR Initial_Condition generates proof obligation that
                   must be satisfied after package's spec and body

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

Constituents of each ``state_name`` have to be initialized consistently
with that of their representative ``state_name`` as determined by its denotation
or absence in the Initializes aspect of the package.

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

Refined_State Aspect
~~~~~~~~~~~~~~~~~~~~

The Refined_State aspect is introduced by an ``aspect_specification`` where the
``aspect_mark`` is Refined_State and the ``aspect_definition`` shall follow
the grammar of ``refinement_list`` given below.

.. centered:: **Syntax**

::

  refinement_list   ::= refinement_clause
                      | ( refinement_clause { , refinement_clause } )
  refinement_clause ::= state_name => constituent_list
  constituent_list  ::= null
                      | constituent
                      | ( constituent { , constituent } )

where

  ``constituent ::=`` *object_*\ ``name | state_name``

.. ifconfig:: Display_Trace_Units

   :Trace Unit: FE 7.2.2 Syntax

.. centered:: **Name Resolution Rules**

#. A Refined_State aspect of a ``package_body`` has visibility extended to the
   ``declarative_part`` of the body.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 NRR Refined_State has visibility of the declarative_part
                   of the body

.. centered:: **Legality Rules**

#. A Refined_State aspect shall only appear in the ``aspect_specification`` of a
   ``package_body``. [The use of ``package_body`` rather than package body
   allows this aspect to be specified for generic package bodies.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 LR aspect Refined_State must appear in aspect
                   specification of package_body

#. If a ``package_specification`` has a non-null Abstract_State aspect its body
   shall have a Refined_State aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 LR non-null Abstract_State packages must have
                   Refined_State aspect

#. If a ``package_specification`` does not have an Abstract_State aspect,
   then the corresponding ``package_body`` shall not have a Refined_State
   aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 LR cannot have Refined_State aspect without
                   Abstract_State aspect

#. Each ``constituent`` shall be either a variable or a state abstraction.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 LR constituent must be variable or state abstraction

#. An object which is a ``constituent`` shall be an entire object.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 LR constituent must be entire object

#. A ``constituent`` shall denote an entity of the hidden state of a package or an
   entity which has a Part_Of ``option`` or aspect associated with its
   declaration.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 LR constituents of hidden state must have
                   a Part_Of option that associates them with this
                   state abstraction

#. Each *abstract_*\ ``state_name`` declared in the package specification shall
   be denoted as the ``state_name`` of a ``refinement_clause`` in the
   Refined_State aspect of the body of the package.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 LR each abstract state_name shall have a refinement_clause

#. Every entity of the hidden state of a package shall be denoted as a
   ``constituent`` of exactly one *abstract_*\ ``state_name`` in the
   Refined_State aspect of the package and shall not be denoted more than once.
   [These ``constituents`` are either variables declared in the private part or
   body of the package, or the declarations from the visible part of
   nested packages declared immediately therein.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 LR hidden state constituents must be denoted by exactly
                   one constituents_list

#. The legality rules related to a Refined_State aspect given in
   :ref:`package_hierarchy` also apply.

.. centered:: **Static Semantics**

#. A Refined_State aspect of a ``package_body`` completes the declaration of the
   state abstractions occurring in the corresponding ``package_specification``
   and defines the objects and each subordinate state abstraction that are the
   ``constituents`` of the *abstract_*\ ``state_names`` declared in the
   ``package_specification``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 SS Refined_State completes declaration of all of the
                   corresponding state abstractions

#. A **null** ``constituent_list`` indicates that the named abstract
   state has no constituents and termed a *null_refinement*. The state
   abstraction does not represent any actual state at all. [This
   feature may be useful to minimize changes to Global and Depends
   aspects if it is believed that a package may have some extra state
   in the future, or if hidden state is removed.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.2 SS null constituent_list indicates the named
                   abstract state has no constituents

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

.. _package_hierarchy:

Abstract_State, Package Hierarchy and Part_Of
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Each item of state declared in the visible part of a private library unit
(and any descendants thereof) must be connected, directly or indirectly, to an
*encapsulating* state abstraction of some public library unit. This is done
using the Part_Of ``option`` or aspect associated with each declaration of
the visible state of the private unit.

The unit declaring the encapsulating state abstraction identified by the Part_Of
``option`` or aspect need not be its parent, but it must be a unit whose body
has visibility of the private library unit, while being *more visible* than the
original unit. Furthermore, the unit declaring the encapsulating state
abstraction must denote the corresponding item of visible state in its
Refined_State aspect to indicate that it includes this part of the visible state
of the private unit. That is, the two specifications, one in the private unit,
and one in the body of the (typically) public unit, must match one another.

Hidden state declared in the private part of a unit also requires a Part_Of
``option`` or aspect, but it must be connected to an encapsulating state
abstraction of the same unit.

The ``option`` or aspect Part_Of is used to specify the encapsulating state
abstraction of the (typically) public unit with which a private unit's visible
state item is associated.

To support multi-level hierarchies of private units, a private unit may connect
its visible state to the state abstraction of another private unit, so long as
eventually the state gets connected to the state abstraction of a public unit
through a chain of connections. However, as indicated above, the unit through
which the state is *exposed* must be more visible.

If a private library unit has visible state, this state might be read or updated
as a side effect of calling a visible operation of a public library unit. This
visible state may be referenced, either separately or as part of the state
abstraction of some other public library unit. The following scenario gives rise
to aliasing between the state abstraction and its constituents:

   * a state abstraction is visible; and

   * an object (or another state abstraction) is visible which is a constituent
     of the state abstraction; and

   * it is not apparent that the object (or other state) is a constituent
     of the state abstraction - there are effectively two entities representing
     part or all of the state abstraction.

To resolve such aliasing, rules are imposed to ensure such a scenario can never
occur. In particular, it is always known what state abstraction a constituent
is part of and a state abstraction always knows all of its constituents.

.. centered:: **Static Semantics**

#. A *Part_Of indicator* is a Part_Of ``option`` of a state abstraction
   declaration in an Abstract_State aspect, a Part_Of aspect applied to a
   variable declaration or a Part_Of aspect applied to a generic package
   instantiation.  The Part_Of indicator shall denote the encapsulating state
   abstraction of which the declaration is a constituent.

#. A unit is more visible than another if it has less private ancestors.

.. centered:: **Legality Rules**

#. Every private unit and each of its descendants, that have visible state
   shall for each declaration in the visible state:

   * connect the declaration to an encapsulating state abstraction by
     associating a Part_Of indicator with the declaration; and

   * name an encapsulating state abstraction in its Part_Of indicator if and
     only if the unit declaring the state abstraction is strictly more visible
     than the unit containing the declaration.

   [Each state abstraction which has a Part_Of indicator, the unit in which it
   is declared and its encapsulating state is noted by any tool analyzing
   SPARK 2014.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 LR private units and their descendants must connect
                   their visible states, via Part_Of indicators, to
                   encapsulating state abstractions of more visible units

#. Each item of hidden state declared in the private part of a unit shall have
   a Part_Of indicator associated with the declaration which shall denote an
   encapsulating state abstraction of the same unit.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 LR hidden state declared in private part of
                   a unit must be associated, via a Part_Of indicator, to
                   an encapsulating state abstraction of the same unit

#. No other declarations shall have a Part_Of indicator.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 LR Part_Of only applies on hidden state and
                   private units

#. The body of a unit whose specification declares a state abstraction named
   as an encapsulating state abstraction of a Part_Of indicator shall:

   * have a ``with_clause`` naming each unit, excluding itself, containing such
     a Part_Of indicator; and

   * in its Refined_State aspect, denote each declaration associated with such a
     Part_Of indicator as a ``constituent`` exclusively of the encapsulating
     state abstraction.

   [The state abstractions with a Part_Of indicator, the unit in which they have
   been declared and their encapsulating state have been noted as described
   previously and these records are used to check this rule.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 LR unit bodies must with other units that denote
                   their abstract states in their Part_Of indicators and
                   each declaration associated with a Part_Of indicator must
                   be a constituent of the encapsulating state abstraction

#. If both a state abstraction and one or more of its ``constituents`` are
   visible in a private package specification or in the package specification of
   a non-private descendant of a private package, then either the state
   abstraction or its ``constituents`` may be denoted but not within the same
   Global aspect or Depends aspect. The denotation must also be consistent
   between the Global and Depends aspects of a subprogram.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 LR if both an abstraction and its constituents are
                   visible then Global and Depends aspects shall consistently
                   denote one of them

#. In a public package specification entities that are Part_Of an
   encapsulating state abstraction shall not be denoted; such entities
   may be represented by denoting their encapsulating state
   abstraction which is not Part_Of a more visible state abstraction.
   [This rule is applied recursively, if an entity is Part_Of a state
   abstraction which is itself Part_Of another encapsulating state
   abstraction, then it must be represented by the encapsulating state
   abstraction]. The exclusion to this rule is that for private parts
   of a package given below.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 LR entities in public package specifications that
                   are Part_Of encapsulating states must not be denoted

#. In the private part of a package a state abstraction declared by the
   package shall not be denoted other than for specifying it as the
   encapsulating state in the Part_Of indicator. The state abstraction's
   ``constituents`` declared in the private part shall be denoted.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 LR a package's state abstraction cannot be denoted
                   in its private part except for specifying a Part_Of
                   indicator

#. In the body of a package, a state abstraction whose refinement is visible
   shall not be denoted except as an encapsulating state in a Part_Of indicator.
   Only its ``constituents`` may be denoted.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 LR when the refinement is visible, the state
                   abstraction cannot be denoted except as an encapsulating
                   state in a Part_Of indicator

#. Within a package body where a state abstraction is visible, its
   refinement is not visible, but one or more of its ``constituents``
   are visible, then the following rules apply:

   * either the state abstraction or its ``constituents`` may be
     denoted but not within the same Global aspect or Depends
     aspect. The denotation must also be consistent between the Global
     and Depends aspects of a subprogram.

   * a state abstraction denoted in a Global or Depends aspect is not
     refined into its constituents in a Refined_Global or
     Refined_Depends aspect [because the refinement of the state
     abstraction is not visible].

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 LR in a package body, when a state abstraction
                   and some of its constituents are visible but the refinement
                   is not then both the Global and Depends aspects have to
                   consistently mention either of the two

.. centered:: *Verification Rules*

#. In a package body of a public child when a state abstraction is
   visible, its refinement is not but one or more of its constituents
   are visible then if a subprogram declared in the visible part of
   the package, directly or indirectly:

   * reads a ``constituent`` of a state abstraction then, this
     shall be regarded as a read of the most visible encapsulating
     state abstraction of the ``constituent`` and shall be represented
     by this encapsulating state in the Global and Depends aspects of
     the subprogram; or

   * updates a ``constituent`` of a state abstraction then, this shall
     be regarded as an update of the most visible encapsulation state
     abstraction of the ``constituent`` and shall be represented by
     this encapsulating state with a ``mode_selector`` of In_Out in
     the Global aspect of the subprogram and as both an ``input`` and
     an ``output`` in the Depends aspect of the subprogram. [The
     reason for this is that it is not known whether the entire state
     abstraction is updated or only some of its constituents.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.3 VR public children which see a state abstraction
                   and some of its constituents but not its refinement,
                   may either read the most visible encapsulating state
                   abstraction or update it. These children must reference
                   this most visible encapsulating state abstraction in their
                   Global and Depends aspects.


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

    private package P.Priv --  private unit
       with Abstract_State => ((A with Part_Of => P.Pub.R),
                               (B with Part_Of => P.Pub.S))
    is
       X : T  -- visible variable which is part of state abstraction P.Pub.R.
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
                        -- part must have a Part_Of option
                        -- A1 cannot be denoted in the private part.
       is
          procedure Init_B1
             with Global  => (Output => B1),
                  Depends => (B1 => null);

          procedure Init_A2
             -- A2 cannot be denoted in the private part but
             -- Outer.Hidden_State, which is Part_Of A2, may be denoted.
             with Global  => (Output => Outer.Hidden_State),
                  Depends => (Outer.Hidden_State => null);

       end Inner;
    end Outer;

   package body Outer
      with Refined_State => (A1 => Inner.B1,
                             A2 => Hidden_State)
                             -- Outer.A1 and Outer.A2 cannot be denoted in the
                             -- body of Outer because their refinements are visible.
   is
      package body Inner
         with Refined_State => (B1 => null)  -- Oh, there isn't any state after all
      is
         procedure Init_B1
            with Refined_Global  => null,  -- Refined_Global and Refined_Depends of a null refinement
                 Refined_Depends => null
         is
         begin
            null;
         end Init_B1;

         procedure Init_A2
            -- Refined_Global and Refined_Depends aspects not required
            -- because there is no refinement of Outer.Hidden_State.
         is
         begin
            Outer.Hidden_State := 0;
         end Init_A2;

      end Inner;

      procedure Init_A1
         with Refined_Global  => (Output => B1),
              Refined_Depends => (B1 => null)
      is
      begin
         Inner.Init_B1;
      end Init_A1;

      procedure Init_A2
         with Refined_Global  => (Output => Hidden_State),
              Refined_Depends => (Hidden_State => null)
      is
      begin
         Inner.Init_A2;
      end Init_A2;

   end Outer;

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
      -- Q1 and Q2 may only be denoted as the encapsulating state abstraction
      Hidden_State : Integer
         with Part_Of => Q2;
   end Q;

   private package Q.Child
      with Abstract_State => (C1 with Part_Of => Q.Q1)
   is
      -- Only constituents of Q1 and Q2 may be denoted here
      procedure Init_Q1
         with Global  => (Output => C1),
              Depends => (C1 => null);

      procedure Init_Q2
         with Global  => (Output => Q.Hidden_State),
              Depends => (Q.Hidden_State => null);
   end Q.Child;

   with Q;
   package body Q.Child
      with Refined_State => (C1 => Actual_State)
   is
      -- C1 shall not be denoted here - only Actual_State
      -- but Q.Hidden_State may be denoted.
      Actual_State : Integer;

      procedure Init_Q1
         with Refined_Global  => (Output => Actual_State),
              Refined_Depends => (Actual_State => null)
      is
      begin
         Actual_State := 0;
      end Init_Q1;

      procedure Init_Q2
      is
      begin
         Q.Hidden_State := 0;
      end Init_Q2;

   end Q.Child;

   with Q.Child;
   package body Q
      with Refined_State => (Q1 => Q.Child.C1,
                             Q2 => Hidden_State)
   is
      -- Q1 and Q2 shall not be denoted here but the constituents
      -- Q.Child.C1 and Hidden_State may be.

      procedure Init_Q1
         with Refined_Global  => (Output => Q.Child.C1),
              Refined_Depends => (Q.Child.C1 => null)
      is
      begin
         Q.Child.Init_Q1;
      end Init_Q1;

      procedure Init_Q2
         with Refined_Global  => (Output => Hidden_State),
              Refined_Depends => (Hidden_State => null)
      is
      begin
         Q.Child.Init_Q2;
      end Init_Q2;

   end Q;



Initialization Issues
~~~~~~~~~~~~~~~~~~~~~

Every state abstraction specified as being initialized in the Initializes
aspect of a package has to have all of its constituents initialized. This
may be achieved by initialization within the package, by assumed
pre-initialization (in the case of external state) or, for constituents
which reside in another package, initialization by their declaring package.

.. centered:: **Verification Rules**

#. For each state abstraction denoted by the ``name`` of an
   ``initialization_item`` of an Initializes aspect of a package, all the
   ``constituents`` of the state abstraction must be initialized by:

   * initialization within the package; or

   * assumed pre-initialization (in the case of external states); or

   * for constituents which reside in another unit [and have a Part_Of
     indicator associated with their declaration] by their declaring
     package. [It follows that such constituents will appear in the
     initialization clause of the declaring unit unless they are external
     states.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.2.4 VR each state abstraction in an Initializes aspect
                   shall have all its constituents initialized by either the
                   package, by assumed pre-initialization or by the other
                   unit that declares the state abstraction constituent

.. _refined-global-aspect:

Refined_Global Aspect
~~~~~~~~~~~~~~~~~~~~~

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

The static semantics are equivalent to those given for the Global aspect in
:ref:`global-aspects`.

.. centered:: **Legality Rules**

#. A Refined_Global aspect shall be specified on a body_stub (if one is
   present) or subprogram body if and only if it has a declaration in the
   visible part of an enclosing package, the declaration has a
   Global aspect which denotes a state abstraction declared by the package and
   the refinement of the state abstraction is visible.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.5 LR Refined_Global must be placed on the body of a
                   subprogram. Specs of the subprogram must have a Global
                   aspect and there must be a Refined_State aspect on the
                   body of the enclosing package

#. A Refined_Global aspect specification shall *refine* the subprogram's
   Global aspect as follows:

   * For each ``global_item`` in the Global aspect which denotes
     a state abstraction whose non-**null** refinement is visible at the point
     of the Refined_Global aspect specification, the Refined_Global
     specification shall include one or more ``global_items`` which denote
     ``constituents`` of that state abstraction.

   * For each ``global_item`` in the Global aspect which denotes
     a state abstraction whose **null** refinement is visible at the point
     of the Refined_Global aspect specification, the Refined_Global
     specification shall be omitted, or if
     required by the syntax of a ``global_specification`` replaced by a **null**
     in the Refined_Global aspect.

   * For each ``global_item`` in the Global aspect which does not
     denote a state abstraction whose refinement is visible, the
     Refined_Global specification shall include exactly one
     ``global_item`` which denotes the same entity as the
     ``global_item`` in the Global aspect.

   * No other ``global_items`` shall be included in the Refined_Global
     aspect specification.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.5 LR Refined_Global must reference constituents of the
                   state abstractions denoted in the corresponding Global aspect
                   or must repeat the state abstraction if its refinement is not
                   visible

#. ``Global_items`` in a Refined_Global ``aspect_specification`` shall denote
   distinct entities.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.5 LR Refined_Global aspect must denote distinct entities

#. The mode of each ``global_item`` in a Refined_Global aspect shall match
   that of the corresponding ``global_item`` in the Global aspect unless:
   the ``mode_selector`` specified in the Global aspect is In_Out;
   the corresponding ``global_item`` of Global aspect shall denote a state
   abstraction whose refinement is visible; and the ``global_item`` in the
   Refined_Global aspect is a ``constituent`` of the state abstraction.

   For this special case when the ``mode_selector`` is In_Out, the
   Refined_Global aspect may denote individual ``constituents`` of the state
   abstraction as Input, Output, or In_Out (given that the constituent itself
   may have any of these ``mode_selectors``) so long as one or more of the
   following conditions are satisfied:

   * at least one of the ``constituents`` has a ``mode_selector`` of In_Out; or

   * there is at least one of each of a ``constituent`` with a ``mode_selector``
     of Input and of Output; or

   * the Refined_Global aspect does not denote all of the ``constituents`` of
     the state abstraction but denotes at least one ``constituent`` that has
     a ``mode_selector`` of Output.

   [This rule ensures that a state abstraction with the ``mode_selector``
   In_Out cannot be refined onto a set of ``constituents`` that are Output or
   Input only. The last condition satisfies this requirement because not all of
   the ``constituents`` are updated, some are preserved, that is the state
   abstraction has a self-dependency.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.5 LR refinement of an In_Out state abstraction must
                   have both an Input and an Output mode_selector

#. If the Global aspect specification references a state abstraction with a
   ``mode_selector`` of Output, whose refinement is visible, then every
   ``constituent`` of that state abstraction shall be referenced in the
   Refined_Global aspect specification.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.5 LR all constituents of an Output state abstraction
                   must be referenced in the Refined_Global aspect

#. The legality rules for :ref:`global-aspects` and External states described in
   :ref:`refined_external_states` also apply.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Refined_Global aspect.

.. centered:: **Verification Rules**

#. If a subprogram has a Refined_Global aspect it is used in the analysis of the
   subprogram body rather than its Global aspect.


   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.2.5 VR if a Refined_Global aspect exists, then it is
                   used instead of the Global aspect for the analysis of the
                   subprogram body

#. The verification rules given for :ref:`global-aspects` also apply.

.. _refined-depends-aspect:

Refined_Depends Aspect
~~~~~~~~~~~~~~~~~~~~~~

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

The static semantics are equivalent to those given for the Depends aspect in
:ref:`depends-aspects`.

.. centered:: **Legality Rules**

#. A Refined_Depends aspect shall be specified on a body_stub (if one is
   present) or subprogram body if and only if it has a declaration in the
   visible part of an enclosing package and the declaration has a
   Depends aspect which denotes a state abstraction declared by the package and
   the refinement of the state abstraction is visible.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.6 LR Refined_Depends must be on the body of a
                   subprogram that has a spec with a Depends. The enclosing
                   package must have a visible Refined_State

#. A Refined_Depends aspect specification is, in effect, a copy of
   the corresponding Depends aspect specification except that any references in
   the Depends aspect to a state abstraction, whose refinement is
   visible at the point of the Refined_Depends specification, are replaced with
   references to zero or more direct or indirect constituents of that state
   abstraction. A Refined_Depends aspect is defined by creating a new
   ``dependency_relation`` from the original given in the Depends aspect as
   follows:

   * A *partially refined dependency relation* is created by first copying, from
     the Depends aspect, each ``output`` that is not state abstraction whose
     refinement is visible at the point of the Refined_Depends aspect, along
     with its ``input_list``, to the partially refined dependency relation as an
     ``output`` denoting the same entity with an ``input_list`` denoting the
     same entities as the original. [The order of the ``outputs`` and the order
     of ``inputs`` within the ``input_list`` is insignificant.]

   * The partially refined dependency relation is then extended by replacing
     each ``output`` in the Depends aspect that is a state abstraction, whose
     refinement is visible at the point of the Refined_Depends, by zero or more
     ``outputs`` in the partially refined dependency relation. It shall be zero
     only for a **null** refinement, otherwise all of the ``outputs`` shall
     denote a ``constituent`` of the state abstraction.

     If the ``output`` in the Depends_Aspect denotes a state abstraction which
     is not also an ``input``, then all of the ``constituents`` [for a
     non-**null** refinement] of the state abstraction shall be denoted as
     ``outputs`` of the partially refined dependency relation.

     These rules may, for each ``output`` in the Depends aspect, introduce more
     than one ``output`` in the partially refined dependency relation. Each of
     these ``outputs`` has an ``input_list`` that has zero or more of the
     ``inputs`` from the ``input_list`` of the original ``output``. The union of
     these ``inputs`` shall denote the same ``inputs`` that appear in the
     ``input_list`` of the original ``output``.

   * If the Depends aspect has a ``null_dependency_clause``, then the partially
     refined dependency relation has a ``null_dependency_clause`` added with an
     ``input_list`` denoting the same ``inputs`` as the original.

   * The partially refined dependency relation is completed by replacing the
     ``inputs`` which are state abstractions, whose refinements are visible at
     the point of the Refined_Depends aspect, by zero or more ``inputs``. It
     shall be zero only for a **null** refinement, otherwise each of the
     ``inputs`` shall denote a ``constituent`` of the state abstraction. The
     completed dependency relation is the ``dependency_relation`` of the
     Refined_Depends aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.6 LR Refined_Depends references constituents of the
                   state abstractions denoted in the corresponding Depends
                   aspect and repeats everything that is not a refinement.

#. These rules result in omitting each state abstraction whose **null**
   refinement is visible at the point of the Refined_Depends. If and only if
   required by the syntax, the state abstraction shall be replaced by a **null**
   symbol rather than being omitted.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.6 LR state abstractions with null refinement must be
                   replaced by null if required by the syntax

#. No other ``outputs`` or ``inputs`` shall be included in the Refined_Depends
   aspect specification. ``Outputs`` in the Refined_Depends aspect
   specification shall denote distinct entities. ``Inputs`` in an ``input_list``
   shall denote distinct entities.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.6 LR Refined_Depends must have no additional outputs
                   or inputs and must denote distinct entities

#. [The above rules may be viewed from the perspective of checking the
   consistency of a Refined_Depends aspect with its corresponding Depends
   aspect. In this view, each ``input`` in the Refined_Depends aspect that
   is a ``constituent`` of a state abstraction, whose refinement is visible at
   the point of the Refined_Depends aspect, is replaced by its representative
   state abstraction with duplicate ``inputs`` removed.

   Each ``output`` in the Refined_Depends aspect, which is a ``constituent`` of
   the same state abstraction whose refinement is visible at the point of the
   Refined_Depends aspect, is merged along with its ``input_list`` into a single
   ``dependency_clause`` whose ``output`` denotes the state abstraction and
   ``input_list`` is the union of all of the ``inputs`` from the original
   ``input_lists``.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.2.6 LR Refined_Depends aspect needs to be consistent with
                   its corresponding Depends aspect. Covered by another TU.

#. The rules for :ref:`depends-aspects` also apply.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Refined_Depends aspect
as it is used purely for static analysis purposes and is not executed.

.. centered:: **Verification Rules**

#. If a subprogram has a Refined_Depends aspect it is used in the analysis of
   the subprogram body rather than its Depends aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FA 7.2.6 VR Refined_Depends aspect is used in the analysis of
                   the subprogram body instead of Depends aspect

#. The verification rules given for :ref:`depends-aspects` also apply.

Refined Postcondition Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the visible part of a package may have a Refined
Postcondition aspect applied to its body or body stub. The Refined Postcondition
may be used to restate a postcondition given on the declaration of a subprogram
in terms of the full view of a private type or the ``constituents`` of a refined
``state_name``.

The Refined Postcondition aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is "Refined_Post" and the ``aspect_definition`` shall
be a Boolean ``expression``.

.. centered:: **Legality Rules**

#. A Refined_Post aspect may only appear on a body_stub (if one is
   present) or the body (if no stub is present) of a subprogram which is
   declared in the visible part of a package, its abstract view. If the
   subprogram declaration in the visible part has no explicit postcondition, a
   postcondition of True is assumed for the abstract view.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.8 LR Refined_Post must be on the body or body stub
                   of a subprogram whose spec is on the visible part of a
                   package.

#. The same legality rules apply to a Refined Postcondition as for
   a postcondition.

.. centered:: **Static Semantics**

#. A Refined Postcondition of a subprogram defines a *refinement*
   of the postcondition of the subprogram.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.2.8 SS Refined_Post defines a refinement of the
                   abstract post. Covered by another TU.

#. Logically, the Refined Postcondition of a subprogram must imply
   its postcondition. This means that it is perfectly logical for the
   declaration not to have a postcondition (which in its absence
   defaults to True) but for the body or body stub to have a
   Refined Postcondition.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: PR 7.2.8 SS Refined_Post must imply abstract post

#. The default Refined_Post for an expression function, F, is
   F'Result = ``expression``, where ``expression`` is the expression defining
   the body of the function.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: PR 7.2.8 SS Expression functions have a default Refined_Post
                   of F'Result = expression_of_expression_function

#. The static semantics are otherwise as for a postcondition.

.. centered:: **Dynamic Semantics**

#. When a subprogram with a Refined Postcondition is called; first
   the subprogram is evaluated. The Refined Postcondition is evaluated
   immediately before the evaluation of the postcondition or, if there is no
   postcondition, immediately before the point at which a postcondition would
   have been evaluated. If the Refined Postcondition evaluates to
   True then the postcondition is evaluated as described in the Ada
   RM. If either the Refined Postcondition or the postcondition
   do not evaluate to True then the exception Assertions.Assertion_Error is
   raised.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.8 DS Refined_Post is evaluated right before Post and
                   if either is False Assertions.Assertion_Error is raised

.. centered:: **Verification Rules**

#. The precondition of a subprogram declaration and its Refined Postcondition
   together imply the postcondition of the declaration, that is:

   (Precondition and Refined Postcondition) -> Postcondition

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: PR 7.2.8 VR Pre and Refined_Post -> Post

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

#. A state abstraction that is not specified as External shall not have
   ``constituents`` which are External states.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.8 LR A non External state abstraction cannot
                   have Volatile constituents

#. An External state abstraction shall have at least one ``constituent``
   that is External state, or shall have a null refinement.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.8 LR An External state abstraction must have at least
                   one External state constituent, or shall have a null
                   refinement.

#. An External state abstraction shall have each of the properties set to True
   which are True for any of its ``constituents``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: FE 7.2.8 LR An External state abstraction shall have each
                   of the properties, which are True for any of its
                   constituents, set to True.

#. Refined_Global aspects must respect the rules related to external
   properties of constituents which are external states given in
   :ref:`external_state` and :ref:`external_state-variables`.

#. All other rules for Refined_State, Refined_Global and Refined_Depends aspect
   also apply.

.. centered:: **Examples**

.. code-block:: ada

   package Externals
      with Abstract_State => ((Combined_Inputs with External => Async_Writers),
                              (Displays with External => Asyc_Readers),
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
      ...
   end Externals.Temperature;

   private package Externals.Pressure
      with Abstract_State => (State with External => Async_Writers,
                                         Part_Of  => Externals.Combined_Inputs)
   is
      ...
   end Externals.Pressure;

   private package Externals.Main_Display
      with Abstract_State => (State with External => Async_Readers,
                                         Part_Of  => Externals.Displays)
   is
      ...
   end Externals.Main_Display;

   private package Externals.Secondary_Display
      with Abstract_State => (State with External => Async_Readers,
                                         Part_Of  => Externals.Displays)
   is
     ...
   end Externals.Secondary_Display;


   with System,
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
      Saved_Value : Integer := 0;  -- Initialized as required.

      Out_Reg : Integer
         with Volatile,
              Async_Readers,
              Effective_Writes, -- Every value written to the port is significant.
              Address  => System.Storage_Elements.To_Address (16#ACECAFE#);

      In_Reg : Integer
         with Volatile,
              Async_Writers,
              Address  => System.Storage_Elements.To_Address (16#A11CAFE#);

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

      ...

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
              Depends => (Found,
                          Serial_In => (FIFO_Status, Pattern, Serial_In));

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
              Address => System.Storage_Elements.To_Address(16#A1CAFE#);

      -- Each byte written is significant, it is a sequence of bytes
      -- and so Effective_Writes => True.
      Write_FIFO: Byte_T
         with Volatile,
              Async_Readers,
              Effective_Writes,
              Address => System.Storage_Elements.To_Address(16#A2CAFE#);

      -- The read of the FIFO status is a snap shot of the current status
      -- individual reads are independent of other reads of the FIFO status
      -- and so Effective_Reads => False.
      Status: Byte_T
         with Volatile,
              Async_Writers,
              Address => System.Storage_Elements.To_Address(16#A3CAFE#);

      -- The value written to the FIFO control register are independent
      -- of other value written to the control register and so
      -- Effective_Writes => False.
      Control: Byte_T
         with Volatile,
              Async_Readers,
              Address => System.Storage_Elements.To_Address(16#A4CAFE#);

      -- This is a bidirectional port but individual reads and writes
      -- are independent and so Effective_Reads and Effective_Writes
      -- are both False.
      Wdog_Shared_Memory : Boolean
         with Volatile,
              Async_Writers,
              Async_Readers,
              Address => System.Storage_Elements.To_Address(16#A5CAFE#);

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
         Watch_Dog_OK := Wdog_Shared_Memory;_
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
                       HAL.FIFO_Control => null)
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

            Get_Byte (A_Byte);
            Put_Byte (A_Byte);
         end loop;
      end if;

   end Main;


Private Types and Private Extensions
------------------------------------

The partial view of a private type or private extension may be in
|SPARK| even if its full view is not in |SPARK|. The usual rule
applies here, so a private type without discriminants is in
|SPARK|, while a private type with discriminants is in |SPARK| only
if its discriminants are in |SPARK|.


Private Operations
~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Type Invariants
~~~~~~~~~~~~~~~

The ``aspect_specification`` Type_Invariant is not permitted in |SPARK|.
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

The view of an entity introduced by a
``deferred_constant_declaration`` is in |SPARK|, even if the *initialization_*\
``expression`` in the corresponding completion is not in |SPARK|.

Limited Types
-------------

No extensions or restrictions.

Assignment and Finalization
---------------------------

Controlled types are not permitted in |SPARK|.

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

#. A call which occurs within the same compilation_unit as the subprogram_body
   of the callee is said to be an *intra-compilation_unit call*.

#. A construct (specifically, a call to a subprogram or a read or write
   of a variable) which occurs in elaboration code for a library level package
   is said to be *executable during elaboration*. If a subprogram call is
   executable during elaboration and the callee's body occurs in the same
   compilation_unit as the call, then any constructs occurring within that body
   are also executable during elaboration. [If a construct is executable during
   elaboration, this means that it could be executed during the elaboration of
   the enclosing library unit and is subject to certain restrictions described
   below.]

.. centered:: **Legality Rules**

#. |SPARK| requires that an intra-compilation_unit call which is
   executable during elaboration shall occur after a certain point in the unit
   (described below) where the subprogram's completion is known to have been
   elaborated. The portion of the unit following this point and extending
   to the start of the completion of the subprogram is defined to
   be the *early call region* for the subprogram. An intra-compilation_unit
   call which is executable during elaboration and which occurs (statically)
   before the start of the completion of the callee shall occur within the
   early call region of the callee.

#. The start of the early call region is obtained by starting at the
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

    package Pkg is
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
   is the call to Q.

   [TBD:
   it would be possible to relax this rule by defining
   a less-restrictive notion of preelaborability which allows, for example,

    .. code-block:: ada

     type Rec is record F1, F2 : Integer; end record;
     X : constant Rec := (123, 456);  -- not preelaborable

   while still disallowing the things that need to be disallowed and
   then defining the above rules in terms of this new notion instead of
   preelaborability. The only disadvantage of this is the added complexity
   of defining this new notion.]

#. For purposes of the above rules, a subprogram completed by a
   renaming-as-body is treated as though it were a wrapper
   which calls the renamed subprogram (as described in Ada RM 8.5.4(7.1/1)).
   [The notional "call" occuring in this wrapper is then subject to the
   above rules, like any other call.]

#. If an instance of a generic occurs in the same compilation_unit as the
   body of the generic, the body must precede the instance. [If this rule
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

#. In the case of a dispatching call, the subprogram_body mentioned
   in the above rules is that (if any) of the statically denoted callee.

#. The first freezing point of a tagged type shall occur within the
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

#. For purposes of defining the early call region, the spec and body of a
   library unit package which has an Elaborate_Body pragma are treated as if
   they both belonged to some enclosing declaration list with the body
   immediately following the specification. This means that the early call
   region in which a call is permitted can span the specification/body boundary.
   This is important for tagged type declarations.

   [This example is in |SPARK|, but would not be without the Elaborate_Body
   pragma (because of the tagged type rule).

   .. code-block:: ada

     with Other_Pkg;
     package Pkg is
        pragma Elaborate_Body;
        type T is new Other_Pkg.Some_Tagged_Type with null record;
        overriding procedure Op (X : T);
        -- freezing point of T is here
     end;

     package body Pkg is
        ... ; -- only preelaborable constructs here
        procedure Op (X : T) is ... ;
     end Pkg;

   An elaboration check failure would be possible if a call to Op (simple or via
   a dispatching call to an ancestor) were attempted between the elaboration of
   the spec and body of Pkg. The Elaborate_Body pragma prevents this from
   occurring. A library unit package spec which declares a tagged type will
   typically require an Elaborate_Body pragma.]

#. For the inter-compilation_unit case, |SPARK| enforces the following static
   elaboration order rule:

   * If a unit has elaboration code that can directly or indirectly make a call
     to a subprogram in a with'd unit, or instantiate a generic package in a
     with'd unit, then if the with'd unit does not have pragma Pure or
     Preelaborate, then the client should have a pragma Elaborate_All for the
     with'd unit. For generic subprogram instantiations, the rule can be
     relaxed to require only a pragma Elaborate. [This rule is the same as the
     GNAT static elaboration order rule as given in the GNAT Pro User's Guide.]

   For each call that is executable during elaboration for a given library unit
   package spec or body, there are two cases: it is (statically) a call
   to a subprogram whose body is in the current compilation_unit, or it
   is not. In the latter case, we require an Elaborate_All pragma as
   described above (the pragma must be given explicitly; it is not
   supplied implicitly).

   [Corner case notes:
   These rules correctly prohibit the following example:

   .. code-block:: ada

     package P is
        function F return Boolean;
        Flag : Boolean := F; -- would fail elab check
     end;

   The following dispatching-call-during-elaboration example would
   be problematic if the Elaborate_Body pragma were not required;
   with the pragma, the problem is solved because the elaboration
   order constraints are unsatisfiable:

   .. code-block:: ada

     package Pkg1 is
        type T1 is abstract tagged null record;
        function Op (X1 : T1) return Boolean is abstract;
     end Pkg1;

     with Pkg1;
     package Pkg2 is
        pragma Elaborate_Body;
        type T2 is new Pkg1.T1 with null record;
        function Op (X2 : T2) return Boolean;
     end Pkg2;

     with Pkg1, Pkg2;
     package Pkg3 is
        X : Pkg2.T2;
        Flag : Boolean := Pkg1.Op (Pkg1.T1'Class (X));
          -- dispatching call during elaboration fails check
          -- Note 'Class is not currently permitted.
     end Pkg3;

     with Pkg3;
     package body Pkg2 is
        function Op (X2 : T2) return Boolean is
        begin return True; end;
     end Pkg2;

#. For an instantiation of a generic which does not occur in the same
   compilation unit as the generic body, the rules are as described
   in the GNAT RM passage quoted above.

Use of Initial_Condition and Initializes Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To ensure the correct semantics of the Initializes and Initial_Condition
aspects, when applied to library units, language restrictions (described below)
are imposed in |SPARK| which have the following consequences:

   - During the elaboration of a library unit package (spec or body),
     library-level variables declared outside of that package
     cannot be modified and library-level variables declared
     outside of that package can only be read if

       * the variable (or its state abstraction) is mentioned in the
         Initializes aspect of its enclosing package; and

       * an Elaborate (not necessarily an Elaborate_All) pragma
         ensures that the body of that package has been elaborated.

   - From the end of the elaboration of a library package's body to the
     invocation of the main program (i.e., during subsequent library unit
     elaboration), variables declared in the package (and constituents of state
     abstractions declared in the package) remain unchanged. The
     Initial_Condition aspect is an assertion which is checked at the end of the
     elaboration of a package body (but occurs textually in the package spec).
     The initial condition of a library level package will remain true from this
     point until the invocation of the main subprogram (because none of the
     inputs used in computing the condition can change during this interval).
     This means that a package's initial condition can be assumed to be true
     both upon entry to the main subprogram itself and during elaboration of any
     other unit which applies an Elaborate pragma to the library unit in
     question (note: an Initial_Condition which depends on no variable inputs
     can also be assumed to be true throughout the execution of the main
     subprogram).

   - If a package's Initializes aspect mentions a state abstraction whose
     refinement includes constituents declared outside of that package,
     then the elaboration of bodies of the enclosing packages of those
     constituents will precede the elaboration of the body of the package
     declaring the abstraction. The idea here is that all constituents
     of a state abstraction whose initialization has been promised are
     in fact initialized by the end of the elaboration of the body of
     the abstraction's unit - we don't have to wait for the elaboration
     of other units (e.g., private children) which contribute to
     the abstraction.

.. centered:: **Verification Rules**

#. If a read of a variable (or state abstraction, in the case of a
   call to a subprogram which takes an abstraction as an input) declared in
   another library unit is executable during elaboration (as defined above),
   then the compilation unit containing the read shall apply an Elaborate (not
   necessarily Elaborate_All) pragma to the unit declaring the variable or state
   abstraction. The variable or state abstraction shall be specified as being
   initialized in the Initializes aspect of the declaring package. [This is
   needed to ensure that the variable has been initialized at the time of the
   read.]

#. The elaboration of a package's specification and body shall not write
   to a variable (or state abstraction, in the case of a call to a procedure
   which takes an abstraction as in output) declared outside of the package. The
   implicit write associated with a read of an external input only state is
   permitted. [This rule applies to all packages: library level or not,
   instantiations or not.] The inputs and outputs of a package's elaboration
   (including the elaboration of any private descendants of a library unit
   package) shall be as described in the Initializes aspect of the package.

.. centered:: **Legality Rules**

#. A package body shall include Elaborate pragmas for all of the
   other library units [(typically private children)] which provide constituents
   for state abstraction refinements occurring in the given package body. [This
   rule could be relaxed to apply only to constituents of an abstraction which
   is mentioned in an Initializes aspect.]
