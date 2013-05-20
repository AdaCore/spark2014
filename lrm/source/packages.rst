Packages
========

.. centered:: **Verification Rules**

#. In |SPARK| the elaboration of a package shall only update, directly or
   indirectly, variables declared immediately within the package.
   
.. note:: TJJ asks: Is this a verification rule or a legality rule?
   Ideally it should be a legality rule but the front end can probably
   only detect direct updates. The globals of called subprograms are needed
   to check indirect calls.

Package Specifications and Declarations
---------------------------------------

.. _abstract-state:

Abstraction of State
~~~~~~~~~~~~~~~~~~~~

The variables declared within a package but not within a subprogram body or
block which does not also enclose the given package constitute the *persistent
state* of the package. A package's persistent state is divided into *visible
state* and *hidden state*. If a declaration that is part a package's persistent
state is visible outside of the package, then it is a constituent of the
package's visible state; otherwise it is a constituent of the package's hidden
state.
    
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
   
   * any variables declared in immediately within the visible part of 
     package P; and
      
   * the state abstractions declared by the Abstract State aspect specification 
     (if any) of package P; and
      
   * the visible state any packages declared immediately within the visible part
     of package P.

     
#. The hidden state of a package P consists of:

   * any variables declared immediately in the private part or body of P; and
     
   * the visible state of any packages declared immediately within the private 
     part or body of P.

.. _external_state:

External State
~~~~~~~~~~~~~~

External state is a state abstraction or variable representing something 
external to a program.  For instance, an input or output device, or a 
communication channel to another subsystem such as another |SPARK| program.

An external state may be *volatile state* in the sense that an assignment to 
a volatile state is not ineffective even if it's value is not read by the
program [The assignment could be to an external device and has no logical effect
on the program]. Similarly, a read of a volatile state may not be ineffective;
it may have a side-effect. The values obtained from two successive
reads without an intervening update of a volatile state may not be equal.

An external state abstraction is considered to be volatile state unless it is
explicitly specified as non-volatile.  An external state which is a variable is 
volatile state if it is an Ada volatile object (as described in the Ada RM 
Annex C.6).  In |SPARK| individual components of an object cannot be specified 
as volatile.

In |SPARK| an external state which is a variable specified as volatile using 
Ada aspects or pragmas is specified as input only or an output only not both.
[This restriction may be relaxed at some point in the future.]
The variable is the means of communication with some external input or output.

A state abstraction that is volatile state may be specified as input only 
or output only or may be left unspecified in terms of whether it is an input or
output. [The lack of an input only or output only designator indicates that the 
state abstraction may represent a hidden state that may have non-volatile and, 
or, both input only and output only states. Such a state abstraction may be 
representing some complex external communication channel.]

An external state that is specified as non-volatile is assumed to be both an 
input and an output and may not be specified as an input or output only.

It follows that a external state that is specified as input only or output only
is volatile state. [If it is Input_Only then some external writer needs to be
updating the value of the variable. Similarly, if it is Output_Only it is 
expected that there are external readers to be consuming the output values. 
Either of these require external agents of some kind, which implies volatility.]

|SPARK| aspects are defined for specifying a variable as an external input only
or an external output only (see :ref:`external_aspects`) and a state abstraction
may be specified as external and, either input only or output only, or
non-volatile when it is declared by an Abstract_State aspect (see
:ref:`abstract-state-aspect`).


.. centered:: **Static Semantics**

#. An external state abstraction may be specified as being non-volatile 
   state; without this designation it is volatile state.
   
#. A variable is specified as volatile state using the aspects (or pragmas) 
   defined in the Ada RM Annex C6  (or J15).  A variable which is not specified 
   as volatile is non-volatile state.
   
#. A state abstraction denoted as an external non-volatile state cannot be 
   specified as an input only or output only state.  All external states that
   are specified as input only or output only are volatile states.

#. The read or update of volatile state is considered to be both a read and an 
   update of the state. A read of volatile state is preceded by an implicit
   update of the state and an update of volatile state is followed by an
   implicit read of the state. [Thus, a read of volatile state always has a
   side effect and an update of volatile state is never ineffective.]
   
#. It follows from the semantics of reading and updating of volatile state that
   such state does not require initialization for static analysis purposes
   [Indeed, it is not possible to initialize an external input only variable
   because the SPARK rules forbid it to be updated explicitly] and so volatile
   states are not the subject of an initialization item in an Initializes aspect
   (see :ref:`initializes_aspect`).
   
#. Global and Depends aspects of a subprogram represent the explicit reads and
   updates performed by a subprogram and the implicit reads and updates 
   described above are not recorded in these aspects.
   
.. centered:: **Legality Rules**

#. An External state which is specified as Input_Only shall not be denoted in a 
   Global aspect with a ``mode_selector`` of In_Out or Output.  Nor shall it be 
   denoted as an ``output`` of a Depends aspect.
   
#. An External state which is specified as Output_Only shall not be denoted in
   a Global aspect with a ``mode_selector`` of Input or In_Out. Nor shall not be
   denoted as an ``input`` of a Depends aspect.
    
#. As a read of a volatile state always has a side-effect a ``global_item`` of a
   function cannot denote a volatile state [which in turn means that a function
   cannot, directly or indirectly, read a volatile state].

#. A volatile state shall not be denoted by a ``name`` of an 
   ``initialization_item`` of an Initializes aspect 
   (see :ref:`initializes_aspect`).
   
.. todo:: Consider more than just simple External Inputs and Outputs;
          Latched outputs, In_Out Externals, etc.
          To be completed in the Milestone 4 version of this document.


.. _external_aspects:

External, Non_Volatile, Input_Only and Output_Only Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A variable which represents a communication channel with an external entity,
for instance a transducer, subsystem, or program may be specified as an
external state. If it is a volatile variable it has to be specified as an
external state which is an input only or an output only. The Boolean 
aspects External, Input_Only and Output_Only are used for this specification.

.. centered:: **Legality Rules**

#. An External, Input_Only or Output_Only aspect may only be specified for an
   ``object_declaration``.

#. One of an Input_Only or an Output_Only aspect shall be specified for a 
   volatile object declaration. A variable with an Input_Only specification is
   an *external input*; a variable with an Output_Only specification is an
   *external output*.
   
#. If an External aspect is specified for an object which is not volatile,
   then the Non_Volatile aspect may also be specified but is not required.
    
#. Contrary to the general SPARK 2014 rule that expression evaluation
   cannot have side effects, a read of a volatile variable is considered to have
   side effects. To reconcile this discrepancy, a name denoting an external
   input shall only occur in the following contexts:
   
   * as the [right hand side] expression of an assignment statement;
   
   * as the expression of an initialization expression of an object declaration
     that is not specified as volatile;
   
   * as an actual parameter in a call to an instance of Unchecked_Conversion
     whose result is renamed [in an object renaming declaration]; or
     
   * as an actual parameter in a procedure call of which the corresponding 
     formal parameter is mode **in** and is of a non-scalar volatile type.

#. A name denoting an external output shall only occur in the following
   contexts:
   
   * as the name on the left-hand side of an assignment statement; or
   
   * as an actual parameter in a procedure call of which the mode of the 
     corresponding formal parameter is **out** and is of a volatile, 
     non-scalar type.
   
#. See section on volatile variables for rules concerning their use in |SPARK|
   (:ref:`shared_variable_control`).

.. centered:: **Verification Rules**
  
There are no extra verification rules.

.. centered:: **Static Semantics**

There are no extra static semantics associated with these aspects.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with these aspects.

.. centered:: **Examples**

.. code-block:: ada

   with System.Storage_Units;
   package Input_Port
   is

      Sensor : Integer
         with Volatile,
              External,
              Input_Only,
              Address => System.Storage_Units.To_Address (16#ACECAFE#);

   end Input_Port;

   
   with System.Storage_Units;
   package Multiple_Ports
   is
      type Volatile_Type : Integer with Volatile;
   
      -- Read_Port may only be called with an actual parameter for Port
      -- which is an external input only
      procedure Read_Port (Port : in Volatile_Type; Value : out Integer)
      with
         Depends => (Value => Port); -- Port is an external input only
     
     
      -- Write_Port may only be called with an actual parameter for Port
      -- which is a external output only
      procedure Write_Port (Port : out Volatile_Type; Value : in Integer)
      with
         Depends => (Port => Value); -- Port is external output only
     
      -- The following declarations are all external input only variables
      V_In_1 : Volatile_Type 
      with 
         External,
         Input_Only,
         Address => System.Storage_Units.To_Address (16#A1CAFE#);
      
      V_In_2 : Integer
      with
         Volatile,
         External,
         Input_Only,
         Address => System.Storage_Units.To_Address (16#ABCCAFE#);

      -- The following declarations are all volatile output only variables      
      V_Out_1 : Volatile_Type 
      with 
         External,
         Output_Only,
         Address => System.Storage_Units.To_Address (16#BBCCAFE#);
      
      V_Out_2 : Integer
      with
         Volatile,
         External,
         Output_Only,
         Address => System.Storage_Units.To_Address (16#ADACAFE#);

   end Multiple_Ports;
            

.. _abstract-state-aspect:

Abstract State Aspect
~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

    * **Requirement:** It shall be possible to provide an abstracted view of hidden state that can be referred to
      in specifications of program behavior.

      **Rationale:** this allows modular analysis, since modular analysis is performed
      before all package bodies are available and so before all hidden state is known.
      Abstraction also allows the management of complexity.

#. Constraints:

   * No further abstract state-specific requirements.

#. Consistency:

    * No further abstract state-specific requirements.

#. Semantics:

    * No further abstract state-specific requirements.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Language Definition
^^^^^^^^^^^^^^^^^^^

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
package and P reads or updates any of the hidden state of the package then P
shall denote, in its Global aspect, the state abstractions with the correct mode
that represent the hidden state referenced by P. If P has a Depends aspect then
the state abstractions shall be denoted as inputs and outputs of P, as
appropriate, in the ``dependency_relation`` of the Depends aspect.

|SPARK| facilitates the specification of a hierarchy of state abstractions by
allowing a single state abstraction to contain visible declarations of package
declarations nested immediately within the body of a package, private child or
private sibling units and descendants thereof. Each visible state abstraction or
variable of a private child or descendant thereof has to be specified as being
*part of* a state abstraction of a unit which is more visible than itself.

The Abstract State aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is Abstract_State and the ``aspect_definition`` 
shall follow the grammar of ``abstract_state_list`` given below.

.. centered:: **Syntax**

::

  abstract_state_list        ::= null
                               | state_name_with_options
                               | (state_name_with_ { , state_name_with_options } )
  state_name_with_options    ::= state_name
                               | ( state_name with option_list )
  option_list                ::= option { , option }
  option                     ::= simple_option
                               | name_value_option
  simple_option              ::= External 
                               | Non_Volatile 
                               | Input_Only
                               | Output_Only
  name_value_option          ::= Part_Of  => abstract_state
  state_name                 ::= defining_identifier
  abstract_state             ::= name

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 7.1.2 Syntax

.. centered:: **Legality Rules**

#. An ``option`` shall not be repeated within a single ``option_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR An option shall not be repeated within a single option list.
      
#. If External is specified in an ``option_list`` then at most one of Input_Only
   or Output_Only ``options`` may be specified in the``option_list``.  The
   Input_Only and Output_Only options shall not be specified in an 
   ``option_list`` without an External ``option``. 
   

#. If a ``option_list`` contains one or more ``name_value_option`` items 
   then they shall be the final options in the list. 
   [This eliminates the possibility of a positional
   association following a named association in the property list.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR any name_value_properties must be the final properties in the list

#. A ``package_declaration`` or ``generic_package_declaration`` shall have a
   completion [(a body)] if it contains a non-null Abstract State aspect
   specification.
   
#. A subprogram declaration that overloads a state abstraction has an implicit
   Global aspect denoting the state abstraction with a ``mode_selector`` of
   Input.  An explicit Global aspect may be specified which replaces the 
   implicit one.
   

.. centered:: **Static Semantics**


#. Each ``state_name`` occurring in an Abstract_State aspect
   specification for a given package P introduces an implicit
   declaration of a state abstraction entity. This implicit
   declaration occurs at the beginning of the visible part of P. This
   implicit declaration shall have a completion and is overloadable.

   .. note::
      (SB) Making these implicit declarations overloadable allows declaring
      a subprogram with the same fully qualified name as a state abstraction;
      to make this scenario work, rules of the form "... shall denote a state
      abstraction" need to be name resolution rules, not just legality rules.

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
   hidden state.

#. An External state abstraction is one declared with a ``option_list``
   that includes the  External ``option``.
   
#. A state abstraction which is declared with a ``option_list`` that includes
   a Part_Of ``name_value_option`` indicates that it is a constituent (see
   :ref:`state_refinement`) exclusively of the state abstraction 
   denoted by the ``abstract_state`` of the ``name_value_option`` (see
   :ref:`package_hierarchy`).
   
      
.. centered:: **Verification Rules**

There are no verification rules associated with the Abstract_State aspect.

.. centered:: **Dynamic Semantics**

There are no Dynamic Semantics associated with the Abstract_State aspect.

.. centered:: **Examples**

.. code-block:: ada

   package Q
   with
      Abstract_State => State           -- Declaration of abstract state named State
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
   with  
      Abstract_State => (A, B, (C with External, Input_Only))
   is                     -- Three abstract state names are declared A, B & C.
                          -- A and B are internal abstract states
      ...                 -- C is specified as an external state which is input only.
   end X;

   package Mileage
   with 
      Abstract_State => 
         (Trip,     -- number of miles so far on this trip (can be reset to 0).
          Total,    -- total mileage of vehicle since the last factory-reset.
         )
   is
     function Trip  return Natural;  -- Has an implicit Global => Trip.
     function Total return Natural;  -- Has an implicit Global => Total.
    
     procedure Zero_Trip
     with
       Global  => (Output => Trip),  -- In the Global and Depends aspects
       Depends => (Trip => null),    -- Trip denotes the state abstraction.
       Post    => Trip = 0;          -- In the Post condition Trip denotes
                                    -- the function.      
     procedure Inc
     with
       Global  => (In_Out => (Trip, Total)),
       Depends => ((Trip, Total =>+ null)),
       Post    => (Trip = Trip'Old + 1) and (Total = Total'Old + 1);

       -- Trip and Old in the Post conditions denote functions but these 
       -- represent the state abstractions in expressions.

   end Mileage;

.. _initializes_aspect: 

Initializes Aspect
~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

    * **Requirement:** Flow analysis requires the knowledge of whether each
      variable has been initialized.  It should be possible to determine this
      from the specification of a unit.

      **Rationale:** Variables and state abstractions may be initialized within
      a package body as well as a package specification.  It follows not all
      initializations are visible from the specification.  An Initializes aspect
      is applied to a package specification to indicate which variables and
      state abstractions are initialized by the package.  This facilitates
      modular analysis.
      
#. Constraints:

   * No further Initializes-specific requirements.

#. Consistency:

    * No further Initializes-specific requirements.

#. Semantics:

    * **Requirement:** The set of data items listed in an Initializes aspect shall be fully initialized
      during elaboration of this package.

      **Rationale:** To ensure that listed data items are always initialized before use.

#. General requirements:

    * See also section :ref:`generic_hlrs`.


Language Definition
^^^^^^^^^^^^^^^^^^^

The Initializes aspect specifies the visible variables and state abstractions of
a package that are initialized by the elaboration of the package.  In |SPARK|
a package may only initialize variables declared immediately within the package.

If the initialization of a variable or state abstraction, V, during the
elaboration of a package, P, is dependent on the value of a visible variable or
state abstraction from another package, then this entity shall be denoted in
the input list associated with V in the Initialization aspect of P.

The Initializes aspect is introduced by an ``aspect_specification`` where the 
``aspect_mark`` is Initializes and the ``aspect_definition`` shall follow the 
grammar of ``initialization_spec`` given below.

.. centered:: **Syntax**

::

  initialization_spec ::= initialization_list
                        | null

  initialization_list ::= initialization_item
                        | (initialization_item {, initialization_item})

  initialization_item ::= name [ => input_list]
  
.. centered:: **Legality Rules**
   
#. An Initializes aspect may only appear in the ``aspect_specification`` of a 
   ``package_specification``.
   
#. The Initializes aspect shall follow the Abstract_State aspect if one is 
   present.
   
#. The Initializes aspect of a package has visibility of the declarations
   occurring immediately within the visible part of the package.

#. The ``name`` of each ``initialization_item`` in the Initializes aspect 
   definition for a package shall denote a state abstraction of the package or 
   an entire variable declared immediately within the visible part of the
   package.

#. Each ``name`` in the ``input_list`` denotes an entire variable or a state 
   abstraction but shall not denote an entity declared in the package with the
   ``aspect_specification`` containing the Initializes aspect.
   
#. Each entity in a single ``input_list`` shall be distinct.

   .. centered:: **Static Semantics**
   
#. The Initializes aspect of a package specification asserts which 
   state abstractions and visible variables of the package are initialized
   by the elaboration of the package, both its specification and body, and
   any units which have state abstractions or variable declarations that are
   part of (constituents) of a state abstraction declared by the package.  
   [A package with a **null** ``initialization_list``, or no Initializes aspect
   does not initialize any of its state abstractions or variables.]
   
#. If an ``initialization_item`` has an ``input_list`` then the ``names`` in the
   list denote entities which are used in determining the initial value of the
   state abstraction or variable denoted by the ``name`` of the 
   ``initialization_item`` but are not constituents of the state abstraction.   

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Initializes Aspect.

.. centered:: **Verification Rules**

#. If the Initializes aspect is specified for a package, then after the body
   (which may be implicit if the package has no explicit body) has completed its
   elaboration, every (entire) variable and state abstraction denoted by a
   ``name`` in the Initializes aspect shall be initialized. A state abstraction
   is said to be initialized if all of its constituents are initialized. An
   entire variable is initialized if all of its components are initialized.
   Other parts of the visible state of the package shall not be initialized.
   
#. Partial initialization, initializing some but not all of the constituents of 
   a state abstraction or components of a entire variable, is not permitted.
   
#. If an ``initialization_item`` has a ``input_list`` then the entities denoted
   in the input list shall be used in determining initialized value of the
   entity denoted by the ``name`` of the ``initialization_item``

.. centered:: **Examples**

.. code-block:: ada

    package Q
    with
       Abstract_State => State,  -- Declaration of abstract state name State
       Initializes    => State   -- Indicates that State will be initialized
    is                           -- during the elaboration of Q.
      ...
    end Q;

    package Y
    with
       Abstract_State => (A, B, (C with External, Input_Only)),
       Initializes    => A
    is                          -- Three abstract state names are declared A, B & C.
                                -- A is initialized during the elaboration of Y.
       ...                      -- C is specified as an external input only state
				-- and cannot appear in an initializes aspect.
                                -- B is not initialized.
    end Y;

    package Z
    with
       Abstract_State => A,
       Initializes    => null
    is                          -- Package Z has an abstract state name A declared but the
                                -- elaboration of Z and its private descendants do not
                                -- perform any initialization during elaboration.
      ...

    end Z;


Initial Condition Aspect
~~~~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

    * **Requirement:** It shall be possible to formally specify the result of performing package elaboration.

      **Rationale:** This specification behaves as a postcondition for the result of package elaboration
      and so establishes the "pre-condition" that holds at the point of beginning execution of the program proper.
      Giving an explicit postcondition supports modular analysis.

#. Constraints:

   * No further Initial Condition-specific requirements.

#. Consistency:

    * No further Initial Condition-specific requirements.

#. Semantics:

    * **Requirement:** The predicate given by the Initial Condition aspect should evaluate to
      True at the point at which elaboration of the package, its embedded packages and its private descendants has completed.

      **Rationale:** By definition.

#. General requirements:

    * See also section :ref:`generic_hlrs`.


Language Definition
^^^^^^^^^^^^^^^^^^^

The Initial Condition aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Initial_Condition" and the ``aspect_definition`` shall
be a *Boolean_*\ ``expression``.

.. centered:: **Legality Rules**

#. An Initial_Condition aspect may only be placed in an ``aspect_specification`` 
   of a ``package_specification``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The Initial_Condition aspect shall follow the Abstract_State aspect and 
   Initializes aspect if they are present.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. Each variable or state abstraction appearing in an Initial Condition Aspect 
   of a package Q which is declared immediately within the visible part of Q 
   shall be initialized during the elaboration of Q and be denoted by a ``name`` 
   of an ``initialization_item`` of the Initializes aspect of Q.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. Each ``state_name`` referenced in Initial Condition Aspect shall
   be initialized during package elaboration.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**

#. An Initial_Condition aspect is a sort of postcondition for the elaboration
   of both the specification and body of a package. If present on a package, the
   its *Boolean_*\ ``expression`` defines properties (a predicate) of the state
   of the package which can be assumed to be true immediately following the
   elaboration of the package. [The expression of the Initial_Condition may only
   refer to names that are visible. This means that to express properties of
   hidden state, functions declared in the visible part acting on the state
   abstractions of the package must be used.]
   
.. centered:: **Dynamic Semantics**

#. For a non-library level package the *Boolean_*\ ``expression`` 
   Initial_Condition aspect acts as the Boolean parameter of an assume pragma 
   placed immediately after the declaration of the package.  For library level
   packages see :ref:`elaboration_issues`.
   
   .. centered:: **Verification Rules**

#. The Initial_Condition aspect gives a proof obligation to show that the 
   implementation of the ``package_specification`` and its body satisfy the 
   predicate given in the Initial_Condition aspect. [The Boolean expression of 
   the Initial_Condition aspect of a package may only predicate properties of 
   the state of the package specifying the Initial_Condition aspect otherwise 
   it will not be possible to discharge the proof obligation by analysis of the 
   package alone.] 

.. centered:: **Examples**

.. code-block:: ada

    package Q
    with
       Abstract_State    => State,    -- Declaration of abstract state name State
       Initializes       => State,    -- State will be initialized during elaboration
       Initial_Condition => Is_Ready  -- Predicate stating the logical state after
				      -- initialization.
    is

      function Is_Ready return Boolean
      with
	 Global => State;

    end Q;

    package X
    with
       Abstract_State    =>  A,    -- Declares an abstract state name A
       Initializes       => (A, B) -- A and visible variable B are initialized
	                           -- during package initialization.
       Initial_Condition => A_Is_Ready and B = 0
				   -- The logical conditions after package elaboration.
    is
      ...
      B : Integer;

      function A_Is_Ready return Boolean
      with
	 Global => A;

     --
    end X;

Package Bodies
--------------
   
.. _state_refinement:

State Refinement
~~~~~~~~~~~~~~~~

A ``state_name`` declared by an Abstract State aspect in the specification of a
package denotes an abstraction representing all or part of its hidden state. The
declaration must be completed in the package body by a Refined State aspect. The
Refined_State aspect is used to show for each ``state_name`` which variables and
subordinate state abstractions are represented by the ``state_name`` and are 
known as its *constituents*.

In the body of a package the constituents of the refined ``state_name``, the
*refined view*, have to be used rather than the *abstract view* of the
``state_name``. Refined Global, Depends, Pre and Post aspects are provided to
express the refined view.

In the refined view the constituents of each ``state_name`` has to be
initialized consistently with their appearance or omission from the Initializes
aspect of the package.

.. _refinement-rationale:

Common Rationale for Refined Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Where it is possible to specify subprogram behavior using a language feature that
refers to abstract state, it should be possible to define a corresponding *refined*
version of the language feature that refers to the decomposition of that abstract state.

The rationale for this is as follows:

#. The semantics of properties defined in terms of abstract state
   can only be precisely defined in terms of the corresponding concrete state,
   though nested abstraction is also necessary to manage hierarchies of data.

#. There may be multiple possible refinements for a given abstract specification
   and so the user should be able to specify what they actually want.

#. This is necessary to support development via stepwise refinement.


Refined State Aspect
~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** For each state abstraction, it shall be possible to define the set of hidden
     state items that implement or *refine* that abstract state (where the
     hidden state items can either be concrete state or further state abstractions).
     
     **Rationale**: see section :ref:`refinement-rationale`.

#. Constraints:

   * **Requirement:** Each item of hidden state must map to exactly one state abstraction.

     **Rationale:** all hidden state must be covered since otherwise specifications referring to abstract state may
     be incomplete; each item of that hidden state must map to exactly one abstraction to give a clean and easily understandable
     abstraction, and for the purposes of simplicity of analysis.

   * **Requirement:** Each item of abstract state covered by the package shall be mapped to at least one
     item of hidden state (either concrete state or a further state abstraction).

     **Rationale:** the semantics of properties defined in terms of abstract state
     can only be precisely defined in terms of the corresponding concrete state.

   * **Requirement:** Each item of hidden state should appear in at least one global data list
     within the package body.

     **Rationale:** If this is not the case, then there is at least one hidden state item that is not
     used by any subprogram.

#. Consistency:

   * No further Refined state-specific requirements needed.

#. Semantics:

   * No further Refined state-specific requirements needed.

#. General requirements:

    * See also section :ref:`generic_hlrs`.


Language Definition
^^^^^^^^^^^^^^^^^^^

The Refined State aspect is introduced by an ``aspect_specification`` where the
``aspect_mark`` is "Refined_State" and the ``aspect_definition`` shall follow
the grammar of ``refinement_list`` given below.

.. centered:: **Syntax**

::

  refinement_list   ::= refinement_clause
                      | (refinement_clause {, refinement_clause})
  refinement_clause ::= state_name => constituent_list
  constituent_list  ::= null
                      | constituent
                      | (constituent {, constituent})

where

  ``constituent ::=`` *object_*\ ``name | state_name``


.. centered:: **Legality Rules**

#. A Refined_State Aspect may only appear in the ``aspect_specification`` of a
   ``package_body``. [The use of ``package_body`` rather than package body 
   allows this aspect to be specified for generic package bodies.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. If a ``package_specification``  has a non-null Abstract_State aspect its body
   shall have a Refined_State aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. If a ``package_specification``  does not have an Abstract_State aspect,
   then the corresponding ``package_body`` shall not have a Refined_State 
   aspect.
  
   .. note:: We may want to be able to override this error.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. A Refined_State Aspect of a ``package_body`` has visibility extended to  the 
   ``declarative_part`` of the body.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. Each ``constituent`` is either a variable or a state abstraction.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD
      
#. An object which is a ``constituent`` shall be an entire object.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. A ``constituent`` denotes an entity of the hidden state of a package or an
   entity which has a Part_Of ``option`` or aspect associated with its
   declaration.

#. Each *abstract_*\ ``state_name`` declared in the package specification shall
   be denoted as the ``state_name`` of a ``refinement_clause`` in the
   Refined_State aspect of the body of the package.

#. Every entity of the hidden state of a package shall be denoted as a
   ``constituent`` of exactly one *abstract_*\ ``state_name`` in the
   Refined_State aspect of the package and shall not be denoted more than once.
   [These ``constituents`` are either variables declared in the private part or
   body of the package, or the declarations from the visible part of 
   nested packages declared immediately therein.]
   
   .. note:: We may want to be able to override this error.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD
      
#. The legality rules related to a Refined_State aspect given in
   :ref:`package_hierarchy` also apply.
   
.. centered:: **Static Semantics**

#. A Refined_State aspect of a ``package_body`` completes the declaration of the
   state abstractions occurring in the corresponding ``package_specification``
   and defines the objects and each subordinate state abstraction that are the
   ``constituents`` of the *abstract_*\ ``state_names`` declared in the
   ``package_specification``.
   
#. A ``constituent`` with an ``option_list`` is used to indicate the
   ``options`` that apply to the constituent.
   
#. A **null** ``constituent_list`` indicates that the named abstract state has 
   no constituents. The state abstraction does not represent any actual state at
   all. [This feature may be useful to minimize changes to Global and Depends
   aspects if it is believed that a package may have some extra state in the
   future, or if hidden state is removed.]


.. centered:: **Verification Rules**

There are no verification rules associated with Refined_State aspects.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with state abstraction and refinement.

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

Abstract State, Package Hierarchy and Part_Of
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Each item of visible state of a private library unit (and any descendants
thereof) must be connected, directly or indirectly, to an
*encapsulating* state abstraction of some public library unit. This is done 
using the Part_Of ``option`` or aspect, associated with each declaration of 
the visible state of the private unit.

The unit declaring the encapsulating state abstraction identified by the Part_Of
``option`` or aspect need not be its parent, but it must be a unit whose body
has visibility on the private library unit, while being *more visible* than the
original unit. Furthermore, the unit declaring the encapsulating state
abstraction must denote the the corresponding item of visible state in its
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
abstraction of some other public library unit. The following scenario: 
  
   * a state abstraction is visible; and
   
   * an object (or another state abstraction) is visible which is a constituent
     of the state abstraction; and
    
   * it is not apparent that the object (or other state) is a constituent
     of the state abstraction - there are effectively two entities representing
     part or all of the state abstraction.
     
gives rise to aliasing between the state abstraction and its constituents.  

To resolve such aliasing rules are imposed to ensure such a scenario can never
occur. In particular, it is always known what state abstraction a constituent
is part of and a state abstraction always knows all of its constituents.
    
.. centered:: **Static Semantics**

#. A *Part_Of indicator* is a Part_Of ``option`` of a state abstraction 
   declaration in an Abstract_State aspect, a Part_Of aspect applied to a 
   variable declaration or a Part_Of aspect applied to a generic package
   instantiation.  The Part_Of indicator denotes the encapsulating state 
   abstraction of which the declaration is a constituent. 
   
#. A unit is more visible than another if it has less private ancestors.

.. centered:: **Legality Rules**

#. Every private unit and each of its descendants, P, that have visible state 
   shall for each declaration in the visible state:

   * connect the declaration to an encapsulating state abstraction by 
     associating a Part_Of indicator with the declaration;
   
   * name an encapsulating state abstraction in its Part_Of indicator if and 
     only if the unit declaring the state abstraction is strictly more visible 
     than the unit containing the declaration; and
   
   * require a ``limited_with_clause`` naming P on the unit which declares the 
     encapsulating state abstraction. 
     [This rule is checked as part of checking the Part_Of aspect.]
     
#. Each item of hidden state declared in the private part of a unit shall have
   a Part_Of indicator associated with the declaration which denotes a 
   encapsulating state abstraction of the same unit.
   
#. No other declarations shall have a Part_Of indicator.
     
#. The body of a unit whose specification declares a state abstraction named
   as a encapsulating state abstraction of a Part_Of indicator shall:
   
   * have a ``with_clause`` naming each unit, excluding itself, containing such
     a Part_Of indicator; and
     
   * in its Refined_State aspect, denote each declaration associated with such a
     Part_Of indicator as a ``constituent`` exclusively of the encapsulating state 
     abstraction.
   
   [The units that need to be with'd is known from the ``limited_with_clauses``
   on its specification and from this it is known which declarations have a
   Part_Of indicator for a encapsulating state abstraction.]

#. Other than in the body of a unit that contains the State_Refinement aspect
   which defines the constituents of a state abstraction, where both a state
   abstraction and one or more of its constituents are visible, only the
   state abstraction may be denoted in Global and Depends aspects of a 
   subprogram or the Initializes or Initial_Condition aspects of a package. 
   [This rule still permits the denotation of either or both the state
   abstraction and its constituents in the implementation of the subprogram or
   package. The Part_Of indicator of the declaration of the constituent
   facilitates resolution of the two views.]
   
.. centered:: **Examples**

.. code-block:: ada


    package P
    is
        -- P has no state abstraction
    end P;
   
    -- P.Pub is the public package that declares the state abstraction
  
    limited with P.Priv;   -- Indicates to P.Pub that the visible (to P.Pub)
                           -- state of P.Priv may be constituents of P.Pub's
                           -- state abstractions.
    package P.Pub --  public unit
      with Abstract_State => (R, S)
    is
       ...
    end P.Pub;

    --  State abstractions of P.Priv, A and B, plus
    --  the concrete variable X, are split up among
    --  two state abstractions within P.Pub, R and S

    private package P.Priv --  private unit
      with Abstract_State =>
        ((A with Part_Of => P.Pub.R), (B with Part_Of => P.Pub.S))
    is
        X : T  -- visible variable which is part of state abstraction P.Pub.R.
           with Part_Of => P.Pub.R;
    end P.Priv;

    with P.Priv; -- P.Priv has to be with'd because its state is part of the
                 -- refined state.
    package body P.Pub
      with Refined_State =>
        (R => (P.Priv.A, P.Priv.X, Y),
         S => (P.Priv.B, Z))
    is
       Y : T2;  -- hidden state
       Z : T3;  -- hidden state
       ...
    end P.Pub;

Initialization Refinement
~~~~~~~~~~~~~~~~~~~~~~~~~

Every state abstraction specified as being initialized in the Initializes 
aspect of a package has to have all of its constituents initialized.  This
may be achieved by initialization within the package, by
assumed pre-initialization (in the case of volatile state) or, for constituents 
which reside in another package, initialization by their declaring package.

.. centered:: **Verification Rules**

#. For each state abstraction denoted by the ``name`` of an 
   ``initialization_item`` of an Initializes aspect of a package, all the 
   ``constituents`` of the state abstraction must be initialized by:
   
   * initialization within the package; or
   
   * assumed pre-initialization (in the case of volatile states); or
   
   * for constituents which reside in another unit [and have a Part_Of 
     indicator associated with their declaration] by their declaring 
     package. [It follows that such constituents will appear in the 
     initialization clause of the declaring unit unless they are volatile 
     states.]
     
.. _refined-global-aspect:

Refined Global Aspect
~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** Where a global data list referring to abstract state has been specified for a subprogram,
     it shall be possible to provide a refined global data list that takes account of the
     refinement of that abstract state.

     **Rationale:** see section :ref:`refinement-rationale`.

#. Constraints:

   * No further Refined Global-specific requirements needed.

#. Consistency:

   * Let *Abstract* be the abstraction function defined by state refinement (such that
     *Abstract* is the identity function when applied to visible state).
     Let *G* be the global data list and *RG* be the refined global data list. Then:

     * **Requirement:** If *X* appears in *RG* but not all constituents of *Abstract (X)* appear in *RG*
       then *Abstract (X)* must appear in *G* with at least input mode.

       **Rationale:** In this case, *Abstract (X)* is not fully initialized by the
       subprogram and the relevant components must be intialized prior to calling
       the subprogram.

     * **Requirement:** If *Y* appears in *G*, then at least one *X* such that *Abstract (X) = Y*
       must appear in *RG*.

       **Rationale:** By definition of abstraction.
     
     * **Requirement:** Refinement of modes:

          * If the mode of *X* in *RG* indicates it is **not** used in a
            proof context, then that mode must be a mode of *Abstract (X)* in *G*.

          * If the mode of *X* in *RG* indicates it **is** used in a proof context and
            *Abstract(X)* does not have another mode according to the above rules, then the
            mode of *Abstract(X)* shall indicate it is only used in proof contexts.

       **Rationale:** In general, modes should be preserved by refinement. However,
       if one refinement constituent of a state abstraction has an input and/or output mode, then
       it is no longer of interest whether another constituent is only used in a
       proof context.

#. Semantics:

   * As per Global aspect.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

.. todo:: The consistency rules will be updated as the
          model for volatile variables is defined.
          To be completed in the Milestone 3 version of this document.

.. todo:: If it ends up being possible to refine null abstract state, then refinements of such
          state could appear in refined globals statements, though they would need
          to have mode in out.
          To be completed in the Milestone 3 version of this document.

Language Definition
^^^^^^^^^^^^^^^^^^^

A subprogram declared in the visible part of a package may have a Refined Global
aspect applied to its body or body stub. A Refined Global aspect of a subprogram
defines a *refinement* of the Global Aspect of the subprogram; that is, the
Refined Global aspect repeats the Global aspect of the subprogram except that
references to state abstractions whose refinements that are visible at the point 
of the subprogram_body are replaced with references to [some or all of the]
constituents of those abstractions.

The Refined Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Refined_Global and the ``aspect_definition``
shall follow the grammar of ``global_specification`` in :ref:`global-aspects`.

.. centered:: **Static Semantics**

The static semantics are equivalent to those given for the Global aspect in
:ref:`global-aspects`.

.. centered:: **Legality Rules**

#. A Refined_Global Aspect may only appear on a body_stub (if one is present)
   or the body (if no stub is present) of a subprogram which is declared
   in the visible part of a package and whose Global aspect denotes one or more
   state abstractions declared in the Abstract_State aspect of the package.
   
#. A Refined_Global aspect specification shall *refine* the subprogram's
   Global aspect as follows:

   * For each ``global_item`` in the Global aspect which denotes
     a state abstraction whose refinement is visible at the point
     of the Refined_Global aspect specification, the Refined_Global
     specification shall include one or more ``global_items`` which
     denote ``constituents`` of that state abstraction.

   * For each ``global_item`` in the Global aspect which does not
     denote such a state abstraction, the Refined_Global specification
     shall include exactly one ``global_item`` which denotes the same entity as
     the ``global_item`` in the Global aspect.

   * No other ``global_items`` shall be included in the Refined_Global
     aspect specification. ``Global_items`` in the a Refined_Global
     aspect specification shall denote distinct entities.

#. The mode of each ``global_item`` in a Refined_Global aspect shall match
   that of the corresponding ``global_item`` in the Global aspect unless:
   the ``mode_selector`` specified in the Global aspect is In_Out;
   the corresponding ``global_item`` of Global aspect denotes a state 
   abstraction whose refinement is visible; and 
   the ``global_item`` in the Refined_Global aspect is a ``constituent`` of 
   the state abstraction.  
     
   When all of these conditions are satisfied the Refined_Global aspect may 
   denote individual ``constituents`` of the state abstraction as Input, Output, 
   or In_Out (given that the constituent itself may have any of these 
   ``mode_selectors``) so long as one or more of the 
   following conditions are satisfied:
   
   * at least one of the ``constituents`` has a ``mode_selector`` of In_Out; or
   
   * there is at least one of each of a ``constituent`` with a ``mode_selector``
     of Input and of Output; or
     
   * the Refined_Global aspect does not denote all of the ``constituents`` of
     the state abstraction and at least one of them has the ``mode_selector``
     of Output.
     
   [This rule ensures that a state abstraction with the ``mode_selector``  
   In_Out cannot be refined onto a set of ``constituents`` that are Output or 
   Input only.  The last condition satisfies this requirement because not all of 
   the ``constituents`` are updated, some are preserved, that is the state
   abstraction has a self-dependency.]
    
#. If the Global aspect specification references a state abstraction. with a
   ``mode_selector`` of Output whose refinement is visible, then every 
   ``constituent`` of that state abstraction shall be referenced in the 
   Refined_Global aspect specification.

#. The legality rules for :ref:`global-aspects` and External states described in 
   :ref:`refined_external_states` also apply.

.. centered:: **Verification Rules**

#. If a subprogram has a Refined Global Aspect it is used in the analysis of the
   subprogram body rather than its Global Aspect.
   
#. The verification rules given for :ref:`global-aspects` also apply.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Refined_Global aspect.

.. _refined-depends-aspect:

Refined Depends Aspect
~~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** Where a dependency relation referring to abstract state has been given,
     it shall be possible to specify a refined dependency relation that takes account
     of the refinement of that abstract state.

     **Rationale:** see section :ref:`refinement-rationale`.

#. Constraints:

   * No further Refined depends-specific requirements needed.

#. Consistency: 

    * **Requirement:** The refined dependency relation defines an alternative view of the inputs and outputs
      of the subprogram and that view must be equivalent to the refined list of global
      data items and formal parameters and their modes (ignoring data items used only in proof contexts).

      **Rationale:** this provides a useful early consistency check.


    * Let *Abstract* be the abstraction function defined by state refinement (such that
      *Abstract* is the identity function when applied to visible state).
      Let *D* be a dependency relation and *RD* be the corresponding
      refined dependency relation. Then:

      * **Requirement:** If *(X,Y)* is in *RD* - i.e. *X* depends on *Y* -
        then *(Abstract(X), Abstract(Y))* is in *D*.

        **Rationale:** dependencies must be preserved after abstraction.

      * **Requirement:** If *(X,Y)* is in *RD* and there is *A* such that *Abstract(A)=Abstract(X)* but
        there is no *B* such that *(A,B)* is in *RD*, then *(Abstract(X),Abstract(X))* is in *D*.

        **Rationale:** In this case, *Abstract (X)* is not fully initialized by the
        subprogram and the relevant components must be initialized prior to calling
        the subprogram.

      * **Requirement:** If *(S,T)* is in *D* then there shall exist *(V,W)* in *RD* such that
        *Abstract(V)=S* and *Abstract(W)=T*.

        **Rationale:** By definition of abstraction.

#. Semantics:

   * As per Depends aspect.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

.. todo:: The consistency rules will be updated as the
          model for volatile variables is defined.
          To be completed in the Milestone 3 version of this document.

.. todo:: If it is possible to refine null abstract state, then refinements of such
          state could appear in refined depends statements, but wouldn't map to
          anything in the depends relation itself and would need to have mode in/out
          in the refined depends.
          To be completed in the Milestone 3 version of this document.

Language Definition
^^^^^^^^^^^^^^^^^^^

A subprogram declared in the visible part of a package may have a Refined
Depends aspect applied to its body or body stub. A Refined Depends aspect of a
subprogram defines a *refinement* of the Depends aspect of the subprogram; that
is, the Refined Depends aspect repeats the Depends aspect of the subprogram
except that references to state abstractions whose refinements are visible at 
the point of the subprogram_body are replaced with references to [some or all of
the] constituents of those abstractions.

The Refined Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Refined_Depends and the ``aspect_definition``
shall follow the grammar of ``dependency_relation`` in :ref:`depends-aspects`.

.. centered:: **Static Semantics**

The static semantics are equivalent to those given for the Depends aspect in
:ref:`depends-aspects`.

.. centered:: **Legality Rules**

#. A Refined_Depends Aspect may only appear on a body_stub (if one is present)
   or the body (if no stub is present) of a subprogram which is declared
   in the visible part of a package and whose Depends aspect denotes one or more
   state abstractions declared in the Abstract_State aspect of the package.
   
   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. A Refined_Depends aspect shall only refine state abstractions whose
   refinement is visible at the point of the Refined_Depends aspect.  All other
   variables and state abstractions are simply replicated in the Refined_Depends
   aspect by names that denote the same entities.
   
#.  Each **null** identifier in the Depends aspect is replicated in the 
    Refined_Depends aspect.

#. Each state abstraction denoted in the Depends aspect whose non-**null**
   refinement is visible at the point of the Refined_Depends aspect shall be 
   refined in the Refined_Depends aspect as follows:

   * Each ``input`` in the Depends aspect shall be replaced, in the 
     Refined_Depends aspect, by one or more ``inputs`` each of which shall 
     denote a ``constituent`` of the state abstraction in the Refined_Depends 
     aspect ``constituent``.

   * Each ``output`` in the Depends aspect shall be replaced, in the 
     Refined_Depends aspect, by one or more ``outputs`` each of which shall 
     denote a ``constituent`` of the state abstraction.  If the ``output``
     in the Depends_Aspect denotes a state abstraction which is not also an 
     ``input``, then all of the ``constituents`` of the state abstraction shall
     be denoted as ``outputs`` of the Refined_Depends aspect. These rules may
     introduce extra ``outputs`` in the Refined_Depends and each of these extra
     ``outputs`` has a corresponding ``input_list``. The union of the ``inputs``
     in the extra ``input_lists`` shall denote the same ``inputs`` as the
     ``input_list`` for the state abstraction denoted as the ``output`` in the
     Depends aspect with its ``inputs`` replaced as required by the above rule
     for refinement of ``inputs``.

#. No other ``outputs`` or ``inputs`` shall be included in the Refined_Depends
   aspect specification. ``Outputs`` in the a Refined_Depends aspect
   specification shall denote distinct entities. ``Inputs`` in an ``input_list``
   denote distinct entities.
   
#. The rules for :ref:`depends-aspects` also apply.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD
      
.. centered:: **Verification Rules**

#. If a subprogram has a Refined Depends Aspect it is used in the analysis of 
   the subprogram body rather than its Depends Aspect.
   
#. The verification rules given for :ref:`depends-aspects` also apply.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Refined_Depends aspect
as it is used purely for static analysis purposes and is not executed.


Refined Precondition Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** Where a precondition has been provided for a subprogram declaration, it shall be
     possible to state a refined precondition that refers to concrete rather than abstract state
     and/or concrete rather than abstract type detail.

     **Rationale:** See section :ref:`refinement-rationale`.

#. Constraints:

   * No further Refined precondition-specific requirements needed.

#. Consistency: 

   * **Requirement:** The refined precondition of the subprogram must be implied by the precondition.

     **Rationale:** standard definition of proof refinement.

#. Semantics:

   * As per the semantics of the Precondition aspect.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Language Definition
^^^^^^^^^^^^^^^^^^^

A subprogram declared in the visible part of a package may have a Refined
Precondition aspect applied to its body or body stub. The Refined Precondition
may be used to restate a precondition given on the declaration of a subprogram
in terms of the full view of a private type or the ``constituents`` of a refined
``state_name``.

The Refined Precondition aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is "Refined_Pre" and the ``aspect_definition`` shall
be a Boolean ``expression``.

.. centered:: **Legality Rules**

#. A Refined_Pre aspect may only appear on a body_stub (if one is 
   present) or the body (if no stub is present) of a subprogram which is 
   declared in the visible part of a package.
   
   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The same legality rules apply to a Refined Precondition as for
   a precondition.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**

#. A Refined Precondition of a subprogram defines a *refinement*
   of the precondition of the subprogram.
   
   #. The static semantics are otherwise as for a precondition.


.. centered:: **Verification Rules**

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

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** Where a post-condition has been provided for a subprogram declaration, it shall be
     possible to state a refined post-condition that refers to concrete rather than abstract state
     and/or concrete rather than abstract type detail.

     **Rationale:** See section :ref:`refinement-rationale`.   

#. Constraints:

   * No further Refined post-condition-specific requirements needed.

#. Consistency: 

   * **Requirement:** The post-condition of the subprogram must be implied by the refined post-condition.

     **Rationale:** standard definition of proof refinement.

#. Semantics:

   * As per the semantics of the Post-condition aspect.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Language Definition
^^^^^^^^^^^^^^^^^^^

A subprogram declared in the visible part of a package may have a Refined
Postcondition aspect applied to its body or body stub. The Refined Postcondition
may be used to restate a postcondition given on the declaration of a subprogram
in terms the full view of a private type or the ``constituents`` of a refined
``state_name``.

The Refined Postcondition aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is "Refined_Post" and the ``aspect_definition`` shall
be a Boolean ``expression``.

.. centered:: **Legality Rules**

#. A Refined_Post aspect may only appear on a body_stub (if one is 
   present) or the body (if no stub is present) of a subprogram which is 
   declared in the visible part of a package.
   

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
   
#. For an ``expression_function`` without an explicit Refined Postcondition
   the expression implementing the function acts as its Refined Postcondition.

#. The static semantics are otherwise as for a postcondition.


.. centered:: **Verification Rules**

#. The precondition of a subprogram declaration with the
   Refined Precondition of its body or body stub and its
   Refined Postcondition together imply the postcondition of the
   declaration, that is:

   ::
     (Precondition and Refined Precondition and Refined Postcondition) -> Postcondition


.. centered:: **Dynamic Semantics**

#. When a subprogram with a Refined Postcondition is called; first
   the subprogram is evaluated. The Refined Postcondition is evaluated
   immediately before the evaluation of the postcondition or, if there is no 
   postcondition, immediately before the point at which a postcondition would 
   have been evaluated.  If the Refined Postcondition evaluates to
   True then the postcondition is evaluated as described in the Ada
   RM.  If either the Refined Postcondition or the postcondition
   do not evaluate to True then the exception Assertions.Assertion_Error is 
   raised.

.. todo:: refined contract_cases.
          To be completed in the Milestone 3 version of this document.

.. _refined_external_states:

Refined External States
~~~~~~~~~~~~~~~~~~~~~~~

An external state which is a state abstraction requires a refinement as does any
state abstraction. There are rules which govern refinement of a state 
abstraction on to external states which are given in this section.

.. centered:: **Legality Rules**

#. A state abstraction that is not specified as External shall not be refined 
   on to ``constituents`` which are specified as External states.
   
#. A state abstraction which is specified as an External, Non_Volatile state 
   shall only be refined on to a **null** ``constituent_list`` or to 
   ``constituents`` that are specified as External, Non_Volatile states and, 
   or, ``constituents`` that are not external states.

#. A state abstraction which is specified as External, Input_Only state 
   shall only be refined on to a **null** ``constituent_list`` or to 
   ``constituents`` that are specified as External, Input_Only states. 

#. A state abstraction which is specified as External, Output_Only state 
   shall only be refined on to a **null** ``constituent_list`` or to
   constituents that are specified as External, Output_Only states. 

#. A state abstraction which is specified as just External state, referred to 
   as a *plain External state* may be refined on to a **null** 
   ``constituent_list`` or to ``constituents`` of any sort of external state 
   and, or, non external states.
   
#. A subprogram declaration that has a Global aspect denoting a state 
   abstraction, which is specified as a plain External state, with a 
   ``mode_selector`` of Input shall in its Refined_Global aspect only denote 
   ``constituents`` that are non-volatile External states or ``constituents``
   that are not external states.
   
#. A subprogram declaration that has a Global aspect denoting a state 
   abstraction, which is specified as a plain External state, and the
   Refined_Global aspect of the subprogram denotes one or more ``constituents``
   that are volatile states, then the ``mode_selector`` of the state abstraction
   in the Global_Aspect of the subprogram declaration shall be In_Out. 

#. All other rules for Refined_State, Refined_Global and Refined_Depends aspect
   also apply.
   
.. centered:: **Examples**


.. code-block:: ada


   package Externals
   with
      Abstract_State => ((Combined_Inputs with External, Input_Only),
                         (Displays with External, Output_Only),
                         (Complex_Device with External),
      Initializes => Complex_Device
   is
      procedure Read (Combined_Value : out Integer)
      with
         Global  => Combined_Inputs,  -- Combined_Inputs is an Input_Only
                                      -- External state it can only be an 
                                      -- Input in Global and Depends aspects.
         Depends => (Combined_Value => Combined_Inputs);
      
      procedure Display (D_Main, D_Secondary : in String)
      with
         Global  => Displays,         -- Displays is an Output_Only
                                      -- External state it can only be an 
                                      -- Output in Global and Depends aspects.
         Depends => (Displays => (D_Main, D_Secondary));

      function Last_Value_Sent return Integer
      with
         Global => Complex_Device;    -- Complex_Device is a Plain External
                                      -- state.  It can be an Input and
                                      -- be a global to a function
                                      -- provided the Refined Global aspect only
                                      -- refers to non-volatile or non-external
                                      -- constituents.
          
      procedure Output_Value (Value : in Integer)
      with
         Global  => (In_Out => Complex_Device),
         Depends => (Complex_Device => (Complex_Device, Value));
         -- If the refined Global Aspect refers to constituents which
         -- are volatile state then the mode_selector for Complex_Device must 
         -- be In_Out and it is both and an output.  The subprogram must be
         -- a procedure.
 
   end Externals;
    
   limited with Externals;
   private package Externals.Temperature
   with
      Abstract_State => 
         (State with External, Input_Only,
                     Part_Of  => Externals.Combined_Inputs)
   is
     ...
   end Externals.Temperature;
    
   limited with Externals;
   private package Externals.Pressure
   with
      Abstract_State => 
         (State with External, Input_Only,
                     Part_Of  => Externals.Combined_Inputs)
   is
     ...
   end Externals.Pressure;
   
   limited with Externals;
   private package Externals.Main_Display
   with
      Abstract_State => 
         (State with External, Output_Only,
                     Part_Of  => Externals.Displays)
   is
      ...
   end Externals.Main_Display;
    
   limited with Externals;
   private package Externals.Secondary_Display
   with
      Abstract_State => 
         (State with External, Output_Only,
                     Part_Of  => Externals.Displays)
   is
     ...
   end Externals.Secondary_Display;
 
    
   with 
     Externals.Temperature,
     Externals.Pressure;
   package body Externals
   with
      Refined_State => (Combined_Inputs =>         -- Input_Only external state
                          (Externals.Temperature,  -- so both Temperature and
                           Externals.Pressure      -- Pressure must be Input_Only
                          ),
                        Displays =>                    -- Output_Only external state 
                          (Externals.Main_Display,     -- so both Main_Display and 
                           Externals.Secondary_Display -- Secondary_Display must be
                          ),                           -- Output_Only.
                           
                        Complex_Device =>              -- Complex_Device is a Plain 
                          (Saved_Value,                -- External and may be mapped
                           Out_Reg,                    -- to any sort of constituent
                           In_Reg
                          )
   is
      Saved_Value : Integer := 0;  -- Initialized as required.
       
      Out_Reg : Integer
      with
         Volatile,
         External,
         Output_Only,
         Address  => System.Storage_Units.To_Address (16#ACECAFE#);
                           
      In_Reg : Integer
      with
         Volatile,
         External,
         Input_Only,
         Address  => System.Storage_Units.To_Address (16#A11CAFE#);
                           
      function Last_Value_Sent return Integer
      with
         Refined_Global => Saved_Value -- Refined_Global aspect only refers to non
                                       -- external state as an Input.
      is
      begin
         return Saved_Value;
      end Last_Value_Sent;
          
      procedure Output_Value (Value : in Integer)
      with
         Refined_Global  => ((Input  => In_Reg),  -- Refined_Global aspect
                             (Output => Out_Reg), -- refers to both volatile
                             (In_Out => Saved_Value)), state and non external state.
                              
         Refined_Depends => (((Out_Reg, Saved_Value) => (Saved_Value, Value)),
                               null => In_Reg)
      is
        Ready : constant := 42;
        Status : Integer;
      begin
         if Saved_Value /= Value then
            loop
               Status := In_Reg;   -- In_Reg is Input_Only external state
                                   -- and may appear on RHS of assignment
                                   -- but not in a condition.
               exit when Status = Ready;
            end loop;
            
            Out_Reg := Value;       -- Out_Reg is an Output_Only external
                                    -- state.  Its value cannot be read.
            Saved_Value := Value;
         end if;
      end Output_Value; 

      ...
       
   end Externals;                     

       
Private Types and Private Extensions
------------------------------------

The partial view of a private type or private extension may be in
|SPARK| even if its full view is not in |SPARK|. The usual rule
applies here, so a private type without discriminants is in
|SPARK|, while a private type with discriminants is in |SPARK| only
if its discriminants are in |SPARK|.


.. centered:: **Legality Rules**

#. If a private type or private extension lacks unknown discriminants,
   then the full view shall define full default initialization. [In other words,
   if a client seeing the private view can declare an object of the type without
   explicitly initializing it, then the resulting object shall be fully
   initialized.]

#. The full type declaration of a private type declaration shall not be 
   specified as Volatile either by an Volatile aspect or by pragma Volatile.

Private Operations
~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Type Invariants
~~~~~~~~~~~~~~~

.. todo:: Type Invariants may not be supported in the first release

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
     
.. todo:: The support for type invariants needs to be considered further and will
          be completed for Milestone 3 version of this document.

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

A call which occurs within the same compilation_unit as the subprogram_body
of the callee is said to be an "intra-compilation_unit call".

A construct (specifically, a call to a subprogram or a read or write
of a variable) which occurs in elaboration code for a library level
package is said to be "executable during elaboration". If a subprogram
call is executable during elaboration and the callee's body
occurs in the same compilation_unit as the call, then any
constructs occurring within that body are also "executable during
elaboration". [If a construct is "executable during elaboration",
this means that it could be executed during the elaboration of the
enclosing library unit and is subject to certain restrictions
described below.]

.. centered:: **Language Design Principles / Legality Rules**

|SPARK| requires that an intra-compilation_unit call which is
executable during elaboration shall occur after a certain point in
the unit where the subprogram_body is known to have been elaborated.

Roughly speaking, the start of the region in which such a call is permitted
is obtained by starting at the subprogram_body and then "backing up" (in
reverse elaboration order) until a non-preelaborable
statement/declarative_item/pragma is encountered.
The region starts immediately after this non-preelaborable
construct (or at the beginning of the enclosing block (or library unit
package spec or body) if no such non-preelaborable construct is found).

The idea here is that once elaboration reaches this point, there will
be no further expression evaluation or statement execution (and, in
particular, no further calls) before the subprogram_body has been
elaborated because all elaborable constructs that will be elaborated
in that interval will be preelaborable. Hence, any calls that occur
statically after this point cannot occur dynamically before the
elaboration of the subprogram body.

These rules allow this example

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

even though the call to Q precedes the body of Q. The allowed region
for calls to either P or Q begins immediately after the declaration of X.
Note that because the call to P is executable during elaboration, so
is the call to Q.

[TBD: it would be possible to relax this rule by defining
a less-restrictive notion of preelaborability which allows, for example,

.. code-block:: ada

   type Rec is record F1, F2 : Integer; end record;
   X : constant Rec := (123, 456);  -- not preelaborable

while still disallowing the things that need to be disallowed and
then defining the above rules in terms of this new notion instead of
preelaborability. The only disadvantage of this is the added complexity
of defining this new notion.]

If an instance of a generic occurs in the same compilation_unit as the
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

In the case of a dispatching call, the subprogram_body mentioned
in the above rules is that (if any) of the statically denoted callee.

In order to ensure that dispatching calls do not fail elaboration
checks, the freezing point of a tagged type must meet the same restrictions
as would be required for a call to each of its overriding primitive operations.
The idea here is that after the freezing point it would be possible to
declare an object of the type and then use it as a controlling operand
in a dispatching call to a primitive operation of an ancestor type.
No analysis is performed to identify scenarios where this is not the case,
so conservative rules are adopted.

[Ada ensures that the freezing point of a tagged type
will always occur after both the completion of the type and the
declarations of each of its primitive subprograms. This is typically all
that one needs to know about freezing points in order to understand
the above rule.]

For purposes of defining the region described above, the spec and body
of a library unit package which has an Elaborate_Body pragma
are treated as if they both belonged to
some enclosing declaration list with the body immediately
following the spec. This means that the "region" in which a call
is permitted can span the spec/body boundary. This is important for
tagged type declarations. This example is in SPARK, but would not be
without the Elaborate_Body pragma (because of the notional calls
associated with the tagged type declaration).

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
  
An elaboration check failure would be possible if a call to Op (simple
or via a dispatching call to an ancestor) were attempted between the
elaboration of the spec and body of Pkg. The Elaborate_Body pragma
prevents this from occurring. A library unit package spec which
declares a tagged type will typically require an Elaborate_Body
pragma.

For the inter-compilation_unit case, SPARK enforces the GNAT static
elaboration order rule. The GNAT Pro User's Guide says:

   If a unit has elaboration code that can directly or indirectly make a call
   to a subprogram in a with'ed unit, or instantiate a generic package in a
   with'ed unit, then if the with'ed unit does not have pragma Pure or
   Preelaborate, then the client should have a pragma Elaborate_All for the
   with'ed unit. ... For generic subprogram instantiations, the rule can be
   relaxed to require only a pragma Elaborate.

For each call that is executable during elaboration for a given library unit
package spec or body, there are two cases: it is (statically) a call
to a subprogram whose body is in the current compilation_unit, or it
is not. In the latter case, we require an Elaborate_All pragma as
described above (the pragma must be given explicitly; it is not
supplied implicitly).

Corner case notes:
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
    end Pkg3;

    with Pkg3;
    package body Pkg2 is
       function Op (X2 : T2) return Boolean is
       begin return True; end;
    end Pkg2;

For an instantiation of a generic which does not occur in the same
compilation unit as the generic body, the rules are as described
in the GNAT RM passage quoted above.

[TBD: this whole section needs to be reformulated more precisely. Still,
perfect is an enemy of good and this is good enough to get started with.]

Use of Initial_Condition and Initializes Aspects
------------------------------------------------

.. centered:: **Language Design Principles**

Language restrictions (described below) are imposed which have the
following consequences:

   - During the elaboration of a library unit package (spec or body),
     library-level variables declared outside of that package
     cannot be modified and library-level variables declared
     outside of that package can only be read if

       * the variable (or its state abstraction) is mentioned in the
         Initializes aspect of its enclosing package; and

       * an Elaborate (not necessarily an Elaborate_All) pragma
         ensures that the body of that package has been elaborated.

   - From the end of the elaboration of a library package's body to the
     invocation of the main program (i.e., during subsequent library
     unit elaboration), variables declared in the package (and
     constituents of state abstractions declared in the package)
     remain unchanged.
     The Initial_Condition aspect is an assertion which is checked at the
     end of the elaboration of a package body (but occurs textually
     in the package spec). The initial condition of
     a library level package will remain true from this point until
     the invocation of the main subprogram (because none of the inputs
     used in computing the condition can change during this interval).
     This means that a package's initial condition can be assumed
     to be true both upon entry to the main subprogram itself and during
     elaboration of any other unit which applies an Elaborate pragma
     to the library unit in question (note: an Initial_Condition which
     depends on no variable inputs can also be assumed to be true throughout
     the execution of the main subprogram).

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

If a read of a variable (or state abstraction, in the case of a
call to a subprogram which takes an abstraction as an input)
declared in another library unit is "executable during elaboration"
(as defined above), then the compilation unit containing the read shall
apply an Elaborate (not necessarily Elaborate_All) pragma to the
unit declaring the variable or state abstraction. The variable or
state abstraction shall be specified as being initialized in the
Initializes aspect of the declaring package.
[This is needed to ensure that the variable has been initialized
at the time of the read.]

The elaboration of a package's specification and body shall not write
to a variable (or state abstraction, in the case of a
call to a procedure which takes an abstraction as in output)
declared outside of the package. The implicit write associated
with a read of a external input only state is permitted. [This rule
applies to all packages: library level or not, instantations or not.]
The inputs and outputs of a package's elaboration (including the
elaboration of any private descendants of a library unit package)
shall be as described in the Initializes aspect of the package.

.. centered:: **Legality Rules**

A package body shall include Elaborate pragmas for all of the
other library units [(typically private children)] which provide
constituents for state abstraction refinements occurring
in the given package body. [This rule could be relaxed to apply
only to constituents of an abstraction which is mentioned in
an Initializes aspect.]
