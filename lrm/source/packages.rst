Packages
========

.. centered:: **Verification Rules**

#. In |SPARK| the elaboration of a package shall only update variables declared 
   immediately within the package.

Package Specifications and Declarations
---------------------------------------

.. centered:: **Verification Rules**

#. Each ``basic_declaration`` occurring in the visible or private part of a 
   package shall not read, directly or indirectly, any value which is not
   entirely derived from compile-time constants.

.. _abstract-state:

Abstraction of State
~~~~~~~~~~~~~~~~~~~~

The variables declared immediately within a package and package declarations
nested immediately therein constitute the *global state* of a package. Only part
of the global state of a package may be visible to a client of a package;
specifically the variables which are declared in the visible part of the
package. The declarations of all other variables of the global state of the
package are *hidden* from a client. 

Though the variables are hidden they still form part (or all) of the global
state of the package and this *hidden state* cannot be ignored for flow analysis
and proof.

State abstraction is the means by which this hidden state is managed for flow
analysis and proof. |SPARK| extends the concept of state abstraction to provide
hierarchical data abstraction whereby the state abstraction declared in a
package may contain the global state of other packages given certain
restrictions described in :ref:`package_hierarchy`. This provides data
refinement similar to the refinement available to types whereby a record may
contain fields which are themselves records.


Volatile State
~~~~~~~~~~~~~~

Volatile state is a volatile variable or a volatile state abstraction.

The abstract state aspect provides a way to designate a named abstract state as
being volatile, usually representing an external input or output. A volatile
variable is designated as volatile using a Volatile aspect possibly with a
further designation of whether it is an input or an output.


.. centered:: **Static Semantics**

#. The read or update of a volatile variable or state abstraction is considered 
   for analysis purposes to be both a read and an update of the entity. 
   [Thus, a read always has a side effect and a write is never ineffective]
   
#. In Global and Depends aspects this means that volatile entities will be 
   regarded as being both an input and an output and this fact may be stated 
   explicitly in those aspects [, for example by using the ``In_Out`` mode in 
   the Global aspect]. 
   
#. However if a variable or abstract state is explicitly designated as being a
   Volatile Input or a Volatile Output, an abbreviated form of the Global and
   Depends aspect is permitted [which gives a more intuitive view of the Global
   and Depends aspects]:

   * If the variable or state abstraction is designated as a Volatile Input,
     then it may appear just as an Input in the Global aspect. Implicitly it is
     declared with a ``mode_selector`` of In_Out. In a Depends aspect it need
     not appear as an output as an implicit self dependency of the volatile
     entity will be declared.

   * If the variable or state abstraction is designated as Volatile Output, then
     it may appear just as an Output in the Global aspect. Implicitly it is
     not appear as an input as an implicit self dependency of the entity will be
     declared.
     
#. [The read of a Volatile Input variable IP in a simple assignment, X := IP;
   behaves as a procedure call of the form Read_Volatile (X) where the
   specification of the procedure is:

   procedure Read_Volatile (X : out T)
   with Global => (In_Out => IP);

   Similarly the update of a Volatile Output variable OP, behaves as a call to a 
   procedure of the form:

   procedure Update_Volatile (Y : in T)
   with Global => (In_Out => OP);]

  
.. centered:: **Legality Rules**

#. As a Volatile entity always has a ``mode_selector`` of In_Out, either given
   explicitly or implicitly, it follows that a Volatile state abstraction
   cannot be a ``global_item`` of a function Global ``aspect_specification``
   [which in turn means that a function cannot, directly or indirectly, 
   read or update a volatile variable].

#. A variable with Volatile and Input aspects cannot be updated directly.
     
#. A variable with Volatile and Output aspects cannot be read directly.

#. [The general |SPARK| rule that an expression evaluation cannot
   have a side effect means that a read of a volatile variable is not an
   ordinary expression.] The value of a volatile variable may only be read 
   directly as a``name`` denoting the variable occurring as:

   * the expression of the right hand side of an assignment statement;
   
   * the expression of an initialization expression of an object declaration;
   
   * an actual parameter in a call to an instance of Unchecked_Conversion
     which is the right hand side of an assignment statement; or
     
   * an actual parameter in a call to an instance of Unchecked_Conversion
     which is renamed.

   
Volatiles:

  An explicit read of a volatile is considered (for purposes of flow
  analysis) to be preceded by an implicit assignment.
  Similarly, an explicit write to a volatile is considered (for purposes
  of flow analysis) to be followed by an implicit read,
  Thus, a read always has a side effect and a write is never ineffective.

  However, this is reflected implicitly, not explicitly, in global
  annotations.  A volatile global can be of mode In. This means only that
  it cannot be explicitly assigned to. For a procedure with
  an In-mode volatile global (which it only reads) this is ok.
  On the other hand, the rule that a function cannot have a
  side-effect applies even to these implicit assignments - a
  function cannot read a volatile.

  Similarly, a volatile global can be of mode Out; this means that
  the volatile cannot be explicitly read.

  Because of the general rule that expression evaluation cannot
  have side effects, we need to spell out exactly when it is ok to read
  a volatile:

      Rhs of assignment (either assignment stmt or declaration initial value)
      Operand of call to U_C instance which is rhs of assignment.
      Operand of call to U_C instance which is renamed.

  The Unchecked_Conversion cases are allowed

  Nonvolatile abstraction can have a volatile component. Problems
  (e.g., a function calling a procedure which reads a volatile) will
  be caught at the point of the refinement. A volatile in-mode abstraction
  allows reading volatile constituents; a non-volatile in-mode abstraction
  does not.

The read of a Volatile Input variable IP in a simple assignment, X := IP;
can be considered as a procedure call of the form Read_Volatile (X) where the
specification of the procedure is:

procedure Read_Volatile (X : out T)
with Global => (In_Out => IP);

Similarly the update of a Volatile Output variable OP, would be represented by 
a call to a procedure of the form:

procedure Update_Volatile (Y : in T)
with Global => (In_Out => OP);

From the representation for a read of a volatile variable it is clear that it
cannot be regarded as an expression in |SPARK|.  In |SPARK| the only place where
a read of a volatile variable may be used in place of an ``expression`` is as a
``name`` denoting the variable on the right hand side of an 
``assignment_statement``.

As a function cannot have a side-effect in |SPARK| a function cannot return
a value dependent on the read of a volatile variable.

A volatile variable may be the parameter of a procedure provided
the formal parameter is a volatile type.  Regardless of the mode of the formal 
parameter given in the subprogram specification it is considered to behave as
mode **in out**.


#. A ``state_name`` which is designated as ``Volatile`` shall not
   appear in an Initializes aspect.

.. todo:: Consider more than just simple Volatile Inputs and Outputs;
          Latched outputs, In_Out volatiles, etc.
          To be completed in the Milestone 4 version of this document.


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
declarations nested immediately within the body of a package, private child
units and descendants thereof. Each visible state abstraction or variable of a
private child or descendant thereof has to be designated as being *part of* a
state abstraction of a unit which is more visible than itself.

The Abstract State aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is Abstract_State and the ``aspect_definition`` 
shall follow the grammar of ``abstract_state_list`` given below.

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
   Part_Of and at most one may appear in the ``property_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR name_value_property identifier must be Part_Of
      
#. A ``name_value_property`` with an ``identifier`` of Part_Of shall appear in
   a non-null Abstract_State aspect if and only if it is declared in:
     
   * a private child unit or a descendant of a private child unit;
   
   * a package declared within the visible part or a nested package declared 
     therein of a private child unit or one of its descendants; or
     
   * a package declared in the private part of a package or a nested package 
     declared therein. 
     
   The expression of such a ``name_value_property`` shall denote a state 
   abstraction.

#. If a ``property_list`` contains one or more ``name_value_property`` items 
   then they shall be the final properties in the list. 
   [This eliminates the possibility of a positional
   association following a named association in the property list.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR any name_value_properties must be the final properties in the list

#. A ``package_declaration`` or ``generic_package_declaration`` shall have a
   completion [(a body)] if it contains a non-null Abstract State aspect
   specification.

.. centered:: **Static Semantics**


#. The visible state of a package P consists of:
   
   * the variables declared in the visible part of package P, the 
     state abstractions declared by the Abstract State aspect specification
     (if any) of package P;
     
   * the visible state and state abstractions of any nested packages declared 
     immediately within the visible part of P; and
     
   * the visible state introduced by a generic package instantiated immediately
     within the visible part of P.
     
#. The hidden state of a package P consists of:

   * the variables declared in the private part or body of P; 
   
   * the visible state and state abstractions of any nested packages declared
     immediately within the private part or body of P; and
     
   * the visible state introduced by a generic package instantiated immediately
     within the private part or body of P.

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
   [The specification is checked when the package is analyzed.]

#. A volatile state abstraction is one declared with a ``property_list``
   that includes the Volatile ``property``, and either Input or Output.
   
#. A state abstraction which is declared with a ``property_list`` that includes
   a Part_Of ``name_value_property`` indicates that it is a constituent (see
   :ref:`state_refinement`) exclusively of the state abstraction denoted by the
   expression of the ``name_value_property``.
   
      
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
      Abstract_State => (A, B, (C with Volatile, Input))
   is                     -- Three abstract state names are declared A, B & C.
                          -- A and B are non-volatile abstract states
      ...                 -- C is designated as a volatile input.
   end X;

   limited with Sensor.Raw;
   package Sensor -- simple volatile, input device driver
   with 
      Abstract_State => (Port with Volatile, Input);
   is
      ...
   end Sensor;
   
   private package Sensor.Raw
   with
      Abstract_State => (Port_22 with Volatile, Input, 
                         Part_Of => Sensor.Port)
   is
      
      ...
   end Sensor.Raw;


Input, Output and Part_Of Aspects
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Variable declarations may have the Input, Output and Part_Of aspects
specified directly as part of declaration.  A generic package instantiation
may have a Part_Of aspect.


.. centered:: **Legality Rules**

#. Input and Output are Boolean aspects.

#. If a variable has the Volatile aspect, then it shall also have
   exactly one of the Input or Output aspects.

#. The Part_Of aspect requires an ``aspect_definition`` which denotes
   a state abstraction.

#. A Part_Of aspect shall appear in the ``aspect_specification`` of a variable
   if and only if it is declared in:
   
   * the private part of a package; or 

   * the visible part of a package declared in the private part of a package and
     package declarations nested therein; or
   
   * the visible part of a private descendant package or the visible part of a 
     package declarations nested therein.
     
#. A Part_Of aspect shall appear in the ``aspect_specification`` of a
   generic package instantiation if and only if:
   
   * the generic package has visible state; and 

   * it is instantiated in private part of a package.
     
.. centered:: **Static Semantics**

#. A Part_Of aspect in the ``aspect_specification`` of a variable 
   declaration indicates that the variable is a constituent of the state
   abstraction denoted by its ``aspect_definition``.

.. centered:: **Examples**

.. code-block:: ada

   with System.Storage_Units;
   private package Input_Port.Raw
   is

      Sensor : Integer
         with Volatile,
              Input,
              Address => System.Storage_Units.To_Address (16#ACECAFE#),
              Part_Of => Input_Port.Pressure_Input;

   end Input_Port.Raw_Input_Port;

   

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

#. The ``name`` of each ``initialization_item`` denotes a state abstraction 
   declared in the same ``aspect_specification`` of a package or an entire 
   variable declared in the visible part of the package.


#. The entity denoted by the ``name`` of an ``initialization_item`` shall be 
   distinct from every other entity denoted in the ``initialization_list``.

#. Each ``name`` in the ``input_list`` denotes an entire variable or a state 
   abstraction but shall not denote an entity declared in the package with the
   ``aspect_specification`` containing the Initializes aspect.
   
# Each entity in a single ``input_list`` shall be distinct.

   .. centered:: **Static Semantics**
   
#. The Initializes aspect of a package specification asserts which 
   state abstractions and visible variables of the package are initialized
   by the elaboration of the package, both its specification and body, and
   any units which have state abstractions or variable declarations that are
   part of (constituents) of a state abstraction declared by the package.  
   
#. If a state abstraction or variable declared in the visible part of a package 
   is not denoted by a ``name`` of an ``initialization_item``, then it should 
   not be initialized during the elaboration of the package.
   
#. A package with a **null** ``initialization_list`` does not initialize any
   of its state abstractions or variables.
   
#. If an ``initialization_item`` has an ``input_list`` then the ``names`` in the
   list denote entities which are used in determining the initial value of the
   state abstraction or variable denoted by the ``name`` of the 
   ``initialization_item`` but are not constituents of the state abstraction.   

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Initializes Aspect.

.. centered:: **Verification Rules**

#. For a Initialization aspect of a package every state abstraction or variable
   denoted by a ``name`` of an ``initialization_item`` shall be initialized
   explicitly, or implicitly during the elaboration of the package and the units
   which declare entities that are part of (constituents) of the state
   abstraction.
   
#. The state abstractions and variables declared in the visible part of a 
   package and not denoted by a ``name`` of an ``initialization_item`` shall not
   be explicitly initialized during the elaboration of the package or any units
   which declare entities that are part of (constituents) of such state
   abstractions.
   
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

    limited with X.PC;
    package X
    with
       Abstract_State =>  A,    -- Declares an abstract state name A.
       Initializes    => (A, B) -- Visible variable B is initialized
                                -- during the elaboration of X.
                                -- Abstract_State A is initialized during
                                -- the elaboration of X and X.PC.
    is
      ...
      B : Integer;
     --
    end X;
    
    private package X.PC
    with
       Abstract_State => (S with Part_Of => X.A)
    is
       ...
    end X.PC;

    package Y
    with
       Abstract_State => (A, B, (C with Volatile, Input)),
       Initializes    => A
    is                          -- Three abstract state names are declared A, B & C.
                                -- A is initialized during the elaboration of Y.
       ...                      -- C is designated as a volatile input and cannot appear
				-- in an initializes aspect.
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
the ``aspect_mark`` is "Initial_Condition" and the ``aspect_definition`` shall be
an ``expression``.

.. todo:: Complete language definition for Initial Condition aspect.
          To be completed in the Milestone 3 version of this document.

.. centered:: **Legality Rules**

#. An Initial Condition Aspect may only be placed in an
   ``aspect_specification`` of a ``package_specification``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The Initial Condition Aspect shall follow the
   Abstract State Aspect, Depends aspect and
   Initializes aspect if they are present.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**

#. The predicate of an Initial Condition Aspect of a package
   defines the initial state of the package after its elaboration and
   the elaboration of its private descendants.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. Each *variable* appearing in an Initial Condition Aspect of a
   package Q which is declared in the visible part of Q shall be
   initialized during the elaboration of Q and its private descendants.
#. A ``state_name`` cannot appear directly in
   an Initial Condition Aspect but it may be indirectly referenced
   through a function call.
#. Each ``state_name`` referenced in Initial Condition Aspect shall
   be initialized during package elaboration.

.. centered:: *Checked by Proof*

#. Verification conditions are generated which have to be proven to
   demonstrate that the implementation of a package Q and its private
   descendants satisfy the predicate given in the
   Initial Condition Aspect of Q.

.. centered:: **Dynamic Semantics**

#. An Initial Condition Aspect is like a postcondition.  It
   should be evaluated following the elaboration of Q and its private
   descendants.  If it does not evaluate to True, then an exception
   should be raised.

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
subordinate abstract states are represented by the ``state_name`` and are known
as its *constituents*.

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

The Refined State aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_State" and the ``aspect_definition`` shall follow
the grammar of ``state_and_category_list`` given below.

.. centered:: **Syntax**

::

  state_and_constituent_list     ::= (state_and_constituents {, state_and_constituents})
  state_and_constituents         ::= state_name => constituent_with_property_list
  constituent_with_property_list ::= constituent_with_property
                                   | (constituent_with_property {, constituent_with_property})
  constituent_with_property      ::= constituent
                                   | (constituent_list with property_list)
  constituent_list               ::= constituent
                                   | (constituent {, constituent})

where

  ``constituent ::=`` *object_*\ ``name | state_name``


.. centered:: **Legality Rules**

#. A Refined_State Aspect may only appear in the ``aspect_specification`` of a
   ``package_body``. [The use of ``package_body`` rather than package body 
   allows this aspect to be specified for generic package bodies.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. If a ``package_specification``  has an Abstract_State aspect its body
   shall have a Refined_State aspect.

   .. note:: We may want to be able to override this error.

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
   entity which has a Part_Of ``property`` or aspect associated with its
   declaration.

#. Each *abstract_*\ ``state_name`` declared in the package specification shall
   be denoted as the ``state_name`` of a ``state_and_constituents`` in the
   Refined_State aspect of the body of the package.

   .. note:: We may want to be able to override this error.

#. Every entity of the hidden state of a package shall be denoted as a
   ``constituent`` of exactly one *abstract_*\ ``state_name`` in the
   Refined_State aspect of the package and shall not be denoted more than once.
   [These ``constituents`` are either variables declared in the private part or
   body of the package, or the declarations from the visible part of 
   nested packages declared immediately therein.]
   
   .. note:: We may want to be able to override this error.

#. A ``property_list`` shall not contain a ``name_value`` property.

#. The ``identifier`` of a ``simple_property`` shall be "Volatile",
   "Input", or "Output".

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. If a ``property_list`` includes the ``simple_property`` "Volatile",
   then the same ``property_list`` shall also include exactly one of
   ``Input`` or ``Output``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD


#. The same identifier shall not appear more than once in a property
   list.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD
      
#. The legality rules related to a Refined_State aspect given in
   :ref:`package_hierarchy` also apply.
   
.. centered:: **Static Semantics**

#. A Refined_State aspect of a ``package_body`` completes the declaration of the
   state abstractions occurring in the corresponding ``package_specification``
   and defines the objects and each subordinate ``state_name`` that are the
   ``constituents`` of the *abstract_*\ ``state_names`` declared in the
   ``package_specification``.
   
#. A ``constituent`` with a ``property_list`` is used to indicate the
   ``properties`` that apply to the constituent.


.. centered:: **Verification Rules**

There are no verification rules associated with Refined_State aspects.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with state abstraction and refinement.

.. centered:: **Examples**

.. code-block:: ada

   -- Here, we present a package Q that declares three abstract states:
   package Q
      with Abstract_State => (A, B, (C with Volatile, Input)),
           Initializes    => (A, B)
   is
      ...
   end Q;

   -- The package body refines
   --   A onto three concrete variables declared in the package body
   --   B onto the abstract state of a nested package
   --   C onto a raw port in the package body
   package body Q
      with Refined_State => (A => (F, G, H),
                             B => R.State,
                             C => (Port with Volatile, Input))
   is
      F, G, H : Integer := 0; -- all initialized as required

      Port : Integer
         with Volatile, Input;

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
thereof) must be connected, directly or indirectly, to a 
*specific state abstraction* of some public library unit. This is done using the
Part_Of ``property`` or aspect, associated with each declaration of the 
visible state of the private unit.

The unit declaring the specific state abstraction identified by the Part_Of
``property`` or aspect need not be its parent, but it must be a unit whose body
has visibility on the private library unit, while being *more visible* than the
original unit. Furthermore, the unit declaring the specific state abstraction
must denote the the corresponding item of visible state in its Refined_State
aspect to indicate that it includes this part of the visible state of the
private unit. That is, the two specifications, one in the private unit, and one
in the body of the (typically) public unit, must match one another.

Hidden state declared in the private part of a unit also requires a Part_Of
``property`` or aspect, but it must be connected to a specific state abstraction 
of the same unit.

The ``property`` or aspect Part_Of is used to specify the specific state
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

#. A *Part_Of indicator* is a Part_Of ``property`` of a state abstraction 
   declaration in an Abstract_State aspect, a Part_Of aspect applied to a 
   variable declaration or a Part_Of aspect applied to a generic package
   instantiation.  The Part_Of indicator denotes the specific state 
   abstraction of which the declaration is a constituent. 
   
#. A unit is more visible than another if it has less private ancestors.

.. centered:: **Legality Rules**

#. Every private unit and each of its descendants that have visible state shall
   for each declaration in the visible state:

   * connect the declaration to a specific state abstraction by associating a
     Part_Of indicator with the declaration;
   
   * name a specific state abstraction in its Part_Of indicator if and only if 
     the unit declaring the state abstraction is strictly more visible than the
     unit containing the declaration; and
   
   * require a ``limited_with_clause`` on the unit which declares the specific
     state abstraction named in the Part_Of indicator associated with the 
     declaration.[This rule is checked as part of checking the Part_Of aspect.]
     
#. Each item of hidden state declared in the private part of a unit shall have
   a Part_Of indicator associated with the declaration which denotes a 
   specific state abstraction of the same unit.
   
#. No other declarations shall have a Part_Of indicator.
     
#. The body of a unit whose specification declares a state abstraction named
   as a specific state abstraction of a Part_Of indicator shall have
   
   * have a ``with_clause`` naming each unit, excluding itself, containing such
     a Part_Of indicator; and
     
   * in its Refined_State aspect denote each declaration associated with such a
     Part_Of indicator as a ``constituent`` exclusively of the specific state 
     abstraction.
   
   [The units that need to be withed is known from the ``limited_with_clauses``
   on its specification and from this it is known which declarations have a
   Part_Of indicator for a specific state abstraction.]

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

    --  State abstractions of P.Priv, A and B, plus
    --  the concrete global variable X, are split up among
    --  two state abstractions within P.Pub, R and S
    limited with P.Priv;
    package P.Pub --  public unit
      with Abstract_State => (R, S)
    is
       ...
    end P.Pub;

    private package P.Priv --  private unit
      with Abstract_State =>
        ((A with Part_Of => P.Pub.R), (B with Part_Of => P.Pub.S))
    is
        X : T  -- visible global variable
          with Part_Of => P.Pub.R;
    end P.Priv;

    with P.Priv;
    package body P.Pub
      with Refined_State =>
        (R => (P.Priv.A, P.Priv.X, Y),
         S => (P.Priv.B, Z))
    is
       Y : T2;  -- hidden global state
       Z : T3;  -- hidden global state
       ...
    end P.Pub;

Initialization Refinement
~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: Complete Verification Rules for Initializes aspect in the presence
          of state abstraction. The text given below is unlikely to be consistent
          with current usage of terminology in this document. We will also likely
          need to remove references to volatile state.
          To be completed in the Milestone 3 version of this document.

If a package has an
Initializes Aspect which contains an ``export`` which is a
``state_name`` then each ``constituent`` of the ``state_name`` must be
initialized during package elaboration or be designated as Volatile,
in which case they are implicitly initialized.  A ``constituent`` of a
non-volatile ``state_name`` of a package which does not appear in the
Initializes Aspect of the package must not be initialized during
package elaboration.  A ``constituent`` of a Volatile ``state_name``
which is non-volatile must be initialized during package elaboration.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. For each ``export`` that appears in an
   Initializes aspect of a package declaration the following must
   be satisfied:

   * Each ``export`` that is a *variable* must be initialized at its
     point of declaration, initialized by the sequence of statements
     of the package, or by an embedded package or a private child
     package which names the ``export`` in its Depends aspect
     or Initializes aspect;
   * For an ``export`` which is a ``state_name``, each ``constituent``
     of the ``export`` that is a *variable* must be initialized at
     its point of declaration, initialized by the sequence of
     statements of the package, or by an embedded package or a private
     child package which names the ``export`` in its
     Depends aspect or Initializes aspect;
   * For an ``export`` which is a ``state_name`` each ``constituent``
     of the ``export`` that is a ``state_name`` must appear in the
     Depends aspect or Initializes aspect of an embedded
     package or private child package.

#. A non-volatile ``constituent`` of a Volatile ``state_name`` must be
   initialized during package elaboration.
#. Each ``constituent`` of a **null** ``abstract_state_name`` must be
   initialized implicitly or during package elaboration.

.. _refined-global-aspect:

Refined Global Aspect
~~~~~~~~~~~~~~~~~~~~~

.. todo:: The subject of refined Global, Depends, Pre and Post aspects is still
          under discussion (and their need questioned) and so the subsections covering
          these aspects is subject to change.  To be resolved and completed by
          Milestone 3 version of this document.
  
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

A subprogram declared in the visible part of a package may have a
Refined Global aspect applied to its body or body stub.
A Refined Global Aspect of a subprogram defines a *refinement*
of the Global Aspect of the subprogram; that is, the Refined Global aspect
repeats the Global aspect of he subprogram except that references to
state abstractions whose refinements are visible at the point of the
subprogram_body are replaced with references to [some or all of the]
constituents of those abstractions.

The Refined Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Global" and the ``aspect_definition``
must follow the grammar of ``global_specification`` in :ref:`global-aspects`.

.. centered:: **Legality Rules**

A Refined_Global Aspect may only appear on body_stub (if one is present)
or the body (if no stub is present) of a subprogram P which is declared
in the visible part of a package and whose Global aspect is specified
(either explicitly or implicitly).

A Refined_Global aspect specification shall "refine" the subprogram's
Global aspect as follows:

   - For each global_item in the Global aspect which denotes
     a state abstraction whose refinement is visible at the point
     of the Refined_Global aspect specification, the Refined_Global
     specification shall include one or more global_items which
     denote constituents (direct or indirect) of that state abstraction.

   - For each global_item in the Global aspect which does not
     denote such a state abstraction, the Refined_Global specification
     shall include exactly one global_item which denotes the same entity as
     the global_item in the Global aspect.

   - A global_item denoting a declaration which is referenced in a (visible)
     **null** state refinement may be referenced with mode **in out**.

     TBD: do we still need null state refinements if we have ghost variables?
     This rule was copied from existing text, but I (SB) don't
     have a clear picture of how null statement refinements work.

   - No other global_items shall be included in the Refined_Global
     aspect specification. Global_items in the a Refined_Global
     aspect specification shall denote distinct entities.

The mode of each global_item in a Refined_Global aspect shall match
that of the corresponding global_item in the Global aspect unless
the mode specified in the Global aspect is **in out** and the
corresponding global_item of Global aspect denotes a state abstraction
whose refinement is visible.

If the Global aspect specification references a state abstraction with
mode **out** whose refinement is visible, then every constituent of that
state abstraction shall be
referenced in the Refined_Global aspect specification. This rule is
applied recursively if one of those constituents is itself a state
abstraction whoe refinement is visible.

TBD: Interactions with volatiles.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. If a subprogram has a Refined Global Aspect which satisfies the
   flow analysis checks, it is used in the analysis of the subprogram
   body rather than its Global Aspect.

* If the declaration of a subprogram P in the visible part of package
  Q has a Global Aspect which mentions a ``state_name`` of Q, but
  P does not have a Refined Global Aspect then an implicit
  Refined Global Aspect will be synthesized from the body of P.

* if the declaration of a subprogram P declared in the visible part of
  a package Q does not have a Global Aspect, first an implicit
  Refined Global Aspect is synthesized from the body of P, then an
  implicit Global Aspect is synthesized from the synthesized
  Refined Global Aspect and the Refined State Aspect (which may also
  have been synthesized).

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

A subprogram declared in the visible part of a package may have a
Refined Depends aspect applied to its body or body stub. The
Refined Depends aspect defines the ``dependency_relation`` of the
subprogram in terms of the ``constituents`` of a ``state_name`` of the
package rather than the ``state_name``.

The Refined Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Depends" and the ``aspect_definition`` must follow
the grammar of ``dependency_relation``.

.. todo:: Complete language definition for Refined_Depends aspect.
          To be completed in the Milestone 3 version of this document.

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
  Refined Depends aspect will be synthesized from the body of P.

* if the declaration of a subprogram P declared in the visible part of
  a package Q does not have a Depends aspect, an implicit one is
  synthesized from the Refined Depends aspect and the
  Refined State aspect (both of which which may also have been
  synthesized).

.. centered:: **Dynamic Semantics**

Abstractions do not have dynamic semantics.


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

A subprogram declared in the visible part of a package may have a
Refined Precondition aspect applied to its body or body stub.  The
Refined Precondition may be used to restate a precondition given on
the declaration of a subprogram in terms of the full view of a private
type or the ``constituents`` of a refined ``state_name``.

The Refined Precondition aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Pre" and the ``aspect_definition`` must be
a Boolean ``expression``.

.. todo:: Complete language definition for Refined_Pre aspect.
          To be completed in the Milestone 3 version of this document.

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

A subprogram declared in the visible part of a package may have a
Refined Postcondition aspect applied to its body or body stub.  The
Refined Postcondition may be used to restate a postcondition given
on the declaration of a subprogram in terms the full view of a private
type or the ``constituents`` of a refined ``state_name``.

The Refined Precondition aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Post" and the ``aspect_definition`` must be
a Boolean ``expression``.

.. todo:: Complete language definition for Refined_Post aspect.
          To be completed in the Milestone 3 version of this document.

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

.. todo:: refined contract_cases.
          To be completed in the Milestone 3 version of this document.


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
