﻿Packages
========

A *compile-time* constant is a static expression or an expression involving only
static expressions [for example an aggregate of static expressions].

In |SPARK| a declaration or statement occurring immediately within the package
shall only read -- whether directly or indirectly -- values derived only from 
compile-time constants.

Among other things this restriction avoids the need to have dependency relations 
applied to packages.

Package Specifications and Declarations
---------------------------------------

.. centered:: **Verification Rules**

#. Each ``basic_declaration`` occurring in the visible or private part of a 
   package shall not read, directly or indirectly, any value which is not
   entirely derived from compile-time constants.

.. _abstract-state:

Abstraction of State
~~~~~~~~~~~~~~~~~~~~

The variables declared immediately within a package Q, its embedded
packages and its private descendants constitute the state of Q.

The variable declarations are only visible to clients of Q if they
are declared in the visible part of Q.  The
declarations of all other variables are *hidden* from a client of Q.
Though the variables are hidden they still form part (or all) of the
state of Q and this *hidden state* cannot be ignored for static analyses
and proof.  *State abstraction* is the means by which this hidden state
is managed for static analyses and proof.

|SPARK| extends the concept of state abstraction to provide
hierarchical data abstraction whereby the hidden state of a package Q
may be refined over a tree of private descendants or embedded packages
of Q.  This provides data refinement similar to the refinement
available to types whereby a record may contain fields which are
themselves records.

Volatile State
~~~~~~~~~~~~~~

Volatile state is a volatile variable or a volatile state abstraction.

The abstract state aspect provides a way to designate a named abstract state as
being volatile, usually representing an external input or output. A volatile
variable is designated as volatile using a Volatile aspect possibly with a
further designation of whether it is an input or an output.

The read or update of a volatile variable or state abstraction is considered to
be both a read and an update of the entity. In Global and Depends aspects this
means that volatile entities will be regarded as being both an input and an
output and this fact may be stated explicitly in those aspects, for example by
using the ``In_Out`` mode in the Global aspect.
However if a variable or abstract state
is explicitly designated as being a Volatile Input or a Volatile Output, an
abbreviated form of the Global and Depends aspect is permitted which gives a
more intuitive view of the globals and the dependency relation.

If the variable or state abstraction is designated as Volatile Input, then it 
may only appear as an Input in the Global aspect.  There is an implicit
declaration that it is also an Output. In a Depends aspect it need not
appear as an output as an implicit self dependency of the entity will be declared.

If the variable or state abstraction is designated as Volatile Output, then it
may only appear as an Output in the Global aspect. There is an implicit 
declaration that it is also an Input.  In a Depends aspect it need not appear
as an input as an implicit self dependency of the entity will be declared.

A volatile variable or volatile state abstraction cannot be mentioned directly in an
assertion expression as the reading of a volatile may affect its value.

.. todo:: More details on volatile variables and definition of a complete
          model. At the very least, if V is a Volatile Input variable should not
          have the following assertion provable:
          T1 := V;
          T2 := V;
          pragma Assert (T1 = T2);
          To be completed in the Milestone 3 version of this document.
          
.. todo:: Need to describe the conditions under which a volatile variable
          can be a parameter of a subprogram.
          To be completed in the Milestone 3 version of this document.

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

State abstraction provides a mechanism for naming, in a package's
``visible_part``, state (typically a collection of variables) that will be
declared within the package's body, ``private_part``, packages nested within
these, or within private descendants of the package. For example, a package
declares a visible procedure and we wish to specify the set of global variables
that the procedure reads and writes as part of the specification of the
subprogram. Those variables cannot be named directly in the package
specification. Instead, we introduce a state abstraction which is visible in the
package specification and later, when the package body is declared, we specify
the set of variables that *constitute* or *implement* that state abstraction. If
a package body contains, for example, a nested package, then a state abstraction
of the inner package may also be part of the implementation of the given state
abstraction of the outer package.

The hidden state of a package may be represented by one or more state
abstractions, with each pair of state abstractions representing disjoint sets of
hidden variables.

If a subprogram P with a Global aspect is declared in the
visible part of a package and P reads or updates any of the hidden
state of the package then P must include in its Global aspect the
abstract state names with the correct mode that represent the hidden
state referenced by P.  If P has a Depends aspect then the abstract
state names must appear as inputs and outputs of P, as appropriate, in
the ``dependency_relation`` of the Depends aspect.

The Abstract State aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is Abstract_State and the ``aspect_definition`` 
must follow the grammar of ``abstract_state_list`` given below.

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
   Integrity  or Constituent_Of and at most one each may appear in the 
   ``property_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR name_value_property identifier must be Integrity
      
#. A ``name_value_property`` with an ``identifier`` of Constituent_Of may
   only appear in an aspect specification of a private child package,
   or a package declared immediately within the visible part of a private child 
   package. The expression of such a ``name_value_property`` must denote a state 
   abstraction.

#. If a ``property_list`` contains at least one ``name_value_property`` then 
   they shall be the final properties in the list. 
   [This eliminates the possibility of a positional
   association following a named association in the property list.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR If property_list has Integrity it must be the final property in the list

#. A package_declaration or generic_package_declaration shall have a completion
   [(a body)] if it contains a non-null Abstract State aspect specification.

.. centered:: **Static Semantics**

#. The visible state and state abstractions of a package P consist of:

   * any non-manifest objects, types, or subtypes declared immediately
     within the visible part of P; and
   * any state abstractions declared by the Abstract State aspect
     specification (if any) of package P; and
   * the visible state and state abstractions of any packages declared
     immediately within the visible part of P.

#. The hidden state of a package P consists of:

   * any non-manifest objects, types, or subtypes declared immediately
     within the private part or body of P;
   * the state abstractions of any packages declared immediately within the 
     visible part of P; and
   * the visible state and state abstractions of any packages declared
     immediately within the private part or body of P, and of any
     private child units of P or of their public descendants.

#. Each ``state_name`` occurring in an Abstract_State aspect
   specification for a given package P introduces an implicit
   declaration of a *state abstraction* entity. This implicit
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

#. A *volatile* state abstraction is one declared with a ``property_list``
   that includes the Volatile ``property``, and either Input or Output.
   
#. A state abstraction which is declared with a ``property_list`` that includes 
   the Integrity ``name_value_property`` is said to have an *integrity level* 
   specified by the Integer expression of the ``name_value_property``.
   
#. A state abstraction which is declared with a ``property_list`` that includes
   a Constituent_Of ``name_value_property``  indicates that it is a 
   constituent (see :ref:`state_refinement`) of the state abstraction denoted 
   by the expression of the ``name_value_property`` and only that state 
   abstraction.
   
#. A state abstraction declared in the ``aspect_specification`` of a private 
   child package, Q, or a package declared immediately within the visible part
   of Q, without a Constituent_Of ``property`` is considered to be a 
   constituent of one of Q's parent's state abstractions and no other state 
   abstraction.

.. centered:: **Verification Rules**

#. A state abstraction which is declared with a ``property_list`` that includes
   a Constituent_Of ``name_value_property`` shall be a constituent of the 
   state abstraction denoted by the expression of the ``name_value_property``.
   
#. A state abstraction declared in the ``aspect_specification`` of a private 
   child package, Q, or a package immediatly within the visible part of Q,
   without a Constituent_Of ``property`` shall be a constituent of one of Q's 
   parent's state abstractions.
   
.. centered:: **Dynamic Semantics**

There are no Dynamic Semantics associated with the Abstract State
aspect.

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

   package Sensor -- simple volatile, input device driver
   with 
      Abstract_State => (Port with Volatile, Input);
   is
      ...
   end Sensor;
   
   private package Sensor.Raw
   with
      Abstract_State => (Port_22 with Volatile, Input, 
                         Constituent_Of => Sensor.Port)
   is
      
      ...
   end Sensor.Raw;

.. todo:: 
     Further semantic detail regarding Volatile state and integrity levels
     needs to be added, in particular in relation to specifying these
     properties for variables which are declared directly within the
     visible part of a package specification.
     To be completed in the Milestone 3 version of this document.

Integrity Levels
^^^^^^^^^^^^^^^^
.. todo:: Integrity levels are still under discussion so that the
   following description should be considered provisional.
 
An abstract state may be assigned an *integrity level* which indicates
that the state has a particular integrity.  *Integrity levels* are
used in information flow analysis to monitor or prohibit the flow of
information (data) of different *integrity levels* between abstract
states.

.. centered:: **Static Semantics**

#. A state abstraction which is declared with an ``Integrity``
   property is deemed to have an *integrity level* as specified by the
   integer expression of the ``name_value`` property.  The *integrity
   level* of an abstract state is used monitor or prohibit information
   flow from a higher *integrity level* to a lower one or vice-versa
   depending on the options selected for the analysis.  A state
   abstraction which is not declared with an Integrity property is
   considered to have a lower *integrity level* than any declared with
   one. [Information flow integrity checks are performed as part of
   the verification rules.]

#. A state abstraction which requires a particular *integrity level*
   must be explicitly declared. *Integrity levels* cannot be
   synthesized.

.. centered:: **Verification Rules**

#. An abstract state declared with an *integrity level* shall not be
   used in determining the value of an output of a subprogram with a
   higher or lower *integrity level* depending on the mode of analysis.
   [Checked during information flow analysis.]

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the integrity levels.

.. centered:: **Examples**

.. code-block:: ada

   package MILS -- a package that manages distinct state of differing Integrities
      with Abstract_State => ((Top_Secret   with Integrity => 4),
                              (Unclassified with Integrity => 0));
   is
      ...
   end MILS;


Input, Output, Constituent_Of  and Integrity Aspects
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

For variables which are declared directly within the visible part of a
package specification, the Volatile, Input, Output, Constituent_Of
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

#. The Constituent_Of aspect requires an ``aspect_definition`` which denotes
   a state abstraction.

#. A Constituent_Of aspect can only appear in the ``aspect_specification`` of a
   variable declared in the visible part of a private child package or
   the visible part of a package declared within the visible part of the 
   private child package..
   
.. centered:: **Static Semantics**

# An Integrity aspect in the ``aspect_specification`` of variable declaration
  defines the integrity level of the variable to be as given by the Integer
  expression given by its ``aspect_definition``.

# A Constituent_Of aspect in the ``aspect_specification`` of a variable 
  declaration indicates that the variable is a constituent of the state
  abstraction denoted by its ``aspect_definition``.

#. A variable that is declared in the visible part of a private child package
   or within the visible part of a package declared within the visible part of
   a private child package which does not have a Constituent_Of aspect is 
   considered to be a constituent of one of the state abstractions of the
   parent of the private child packages.

.. centered:: **Examples**

.. code-block:: ada

   private package Input_Port.Raw
   is

      Sensor : Integer
         with Volatile,
              Input,
              Address => 16#DEADBEEF#,
              Integrity => 4
              Constituent_Of => Input_Port.Pressure_Input;

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
``aspect_mark`` is Initializes and the ``aspect_definition`` must follow the 
grammar of ``initialization_spec`` given below.

.. centered:: **Syntax**

::

  initialization_spec ::= initialization_list
                        | null

  initialization_list ::= initialization_item
                        | (initialization_item {, initialization_item})

  initialization_item ::= name

.. todo:: Complete language definition for Initializes aspect. Note that the text
          given immediately below this ToDo is out of date and doesn't necessarily match
          with the syntax given here.
          To be completed in the Milestone 3 version of this document.

.. centered:: **Syntax**

::

  initialization_list   ::= output_list

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 7.1.4 Syntax

.. centered:: **Legality Rules**

#. Every ``output`` of an ``initialization_list`` of an Initializes
   aspect of a package specification is a state abstraction.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. An Initializes aspect may only appear in the
   ``aspect_specification`` of a package specification.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The Initializes aspect must follow the
   Abstract State aspect if one is present.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. An ``aspect_specification`` shall not have an
   Initializes Aspect if it has a Depends aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The object denoted by a given ``output`` in an Initializes aspect shall
   not be denoted by any other ``output`` in that Initializes aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. A variable appearing in an Initializes aspect must be entire,
   it cannot be a subcomponent of a containing object.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. A ``state_name`` which is designated as ``Volatile`` must not
   appear in an Initializes aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. An Initializes aspect shall not allow ``function_result`` as an ``output``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**

#. An Initializes Aspect is a shorthand notation for a
   Depends aspect of the form:

   ::

     Depends => (S1 => null,
                 S2 => null,
                 ...
                 Sn => null)

     where

       each S1 .. Sn is a variable or state abstraction initialized
       during the elaboration of the package.

#. A **null** ``initialization_list`` is equivalent to a **null**
   ``dependency_relation``.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
Initializes Aspect as the rules are checked by static analysis.


.. centered:: **Examples**

.. code-block:: ada

    package Q
    with
       Abstract_State => State,  -- Declaration of abstract state name State
       Initializes    => State   -- Indicates that State will be initialized
    is                           -- during the elaboration of Q
				 -- or its private descendants.
      ...
    end Q;

    package X
    with
       Abstract_State =>  A,    -- Declares an abstract state name A.
       Initializes    => (A, B) -- A and visible variable B are initialized
                                -- during the elaboration of X or its private descendants.
    is
      ...
      B : Integer;
     --
    end X;

    package Y
    with
       Abstract_State => (A, B, (C with Volatile, Input)),
       Initializes    => A
    is                          -- Three abstract state names are declared A, B & C.
                                -- A is initialized during the elaboration of Y or
				-- its private descendants.
       ...                      -- C is designated as a volatile input and cannot appear
				-- in an initializes aspect clause
                                -- B is not initialized during the elaboration of Y
                                -- or its private descendants.
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
the ``aspect_mark`` is "Initial_Condition" and the ``aspect_definition`` must be
an ``expression``.

.. todo:: Complete language definition for Initial Condition aspect.
          To be completed in the Milestone 3 version of this document.

.. centered:: **Legality Rules**

#. An Initial Condition Aspect may only be placed in an
   ``aspect_specification`` of a ``package_specification``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The Initial Condition Aspect must follow the
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
   package Q which is declared in the visible part of Q must be
   initialized during the elaboration of Q and its private descendants.
#. A ``state_name`` cannot appear directly in
   an Initial Condition Aspect but it may be indirectly referenced
   through a function call.
#. Each ``state_name`` referenced in Initial Condition Aspect must
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

.. centered:: **Verification Rules**

#. Each declaration of the ``declarative_part`` of a ``package_body`` shall not
   read, directly or indirectly, any value which is not
   entirely derived from compile-time constants.

#. Each statement of a ``handled_sequence_of_statements`` of a ``package_body`` 
   shall not read, directly or indirectly, a value which is not entirely derived 
   entirely from compile-time constants.
   
.. _state_refinement:

State Refinement
~~~~~~~~~~~~~~~~

A ``state_name`` declared by an Abstract State aspect in the specification of a
package is an abstraction representing its hidden state. The declaration must be
completed in the package body by a Refined State aspect. The Refined State
aspect is used to show for each ``state_name`` which variables and subordinate
abstract states are represented by the ``state_name`` and are known as its 
*constituents*.

In the body of a package the constituents of the refined
``state_name``, the refined view, has to be used rather than the
abstract view of the ``state_name``.  Refined global, depends, pre
and post aspects are provided to express the refined view.

In the refined view the constituents of each ``state_name`` have to be
initialized consistently with their appearance or omission from the
Package Depends or Initializes aspect of the package.

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


.. todo:: The consistency rules will be updated as the
          models for volatile variables and integrity levels are defined.
          To be completed in the Milestone 3 version of this document.

.. todo:: Consider whether it should be possible to refine null abstract state onto hidden state.
          *Rationale: this would allow the modeling of programs that - for example - use caches
          to improve performance.*
          To be completed in the Milestone 3 version of this document.

.. todo:: Consider whether it should be possible to refine abstract onto hidden state without any restrictions,
          although the refinement would be checked and potential issues flagged up to the user.
     
          **Rationale:** there are a number of different possible models of mapping abstract
          to concrete state - especially when volatile state is being used - and it might
          be useful to provide greater flexibility to the user. In addition, if a facility is
          provided to allow users to step outside of the language when refining depends, for example, then it may be
          necessary to relax the abstraction model as well as relaxing the language feature
          of direct relevance.*

          To be completed in the Milestone 3 version of this document.

Language Definition
^^^^^^^^^^^^^^^^^^^

The Refined State aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_State" and the ``aspect_definition`` must follow
the grammar of ``state_and_category_list`` given below.

.. centered:: **Syntax**

::

  state_and_category_list          ::= (state_and_category {, state_and_category})
  state_and_category               ::= abstract_state_name => constituent_with_property_list
  abstract_state_name              ::= state_name
  constituent_with_property_list   ::= constituent_with_property
                                     | (constituent_with_property {, constituent_with_property})
  constituent_with_property        ::= constituent
                                     | (constituent_list with property_list)
  constituent_list                 ::= constituent
                                     | (constituent {, constituent})

where

  ``constituent ::=`` *variable_*\ ``name | state_name``

.. todo:: Complete language definition for Refined_State aspect.
          To be completed in the Milestone 3 version of this document.

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 7.2.2 Syntax

.. centered:: **Legality Rules**

#. A Refined State Aspect may only appear in ``package_body``. [The use
   of ``package_body`` rather than package body allows this aspect to be specified
   for generic package bodies.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. If a package declaration has an Abstract State Aspect its body
   must have a Refined State Aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. If a package declaration does not have an Abstract State Aspect,
   then the corresponding package body *may* have a Refined State Aspect
   with exactly one ``state_and_category`` where the ``abstract_state_name`` is **null**.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. A Refined State Aspect of a package body has extended
   visibility; it is able to refer to a *variable* declared in the
   package body, or a ``state_name`` or *variable* declared in the
   visible part of a package, declared immediately within the package
   body.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. Every item of the package's hidden state must appear as a
   ``constituent`` in its Refined State aspect.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. Each ``state_name`` declared in a package specification must appear
   exactly once as an ``abstract_state_name`` in the
   Refined State Aspect of the body of the package.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. If a ``constituent`` has the same name as an
   ``abstract_state_name`` it can only be a ``constituent`` of that
   ``abstract_state_name`` and it must be the only ``constituent`` of
   the ``abstract_state_name``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The ``identifier`` of a ``simple_property`` shall be "Volatile",
   "Input", or "Output".

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. If a ``property_list`` includes the ``simple_property`` "Volatile",
   then the same ``property_list`` shall also include exactly one of
   ``Input`` or ``Output``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The ``identifier`` of a ``name_value_property`` shall be
   "Integrity".

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The ``expression`` of an "Integrity" property shall be a static
   expression of any integer type.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The same identifier shall not appear more than once in a property
   list.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. There should be at most one **null** ``abstract_state_name`` and,
   if it is present it must be non-volatile and the last entry of the
   ``state_and_category_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**

#. A Refined State Aspect defines the *variables* and each
   subordinate ``state_name`` which are the constituents that comprise
   the hidden state represented by the ``state_name`` declared in the
   Abstract State Aspect.

#. Each ``constituent`` of the hidden state of must appear exactly
   once in a ``constituent_list`` of exactly one
   ``state_and_category``; that is each ``constituent`` must
   be a constituent of one and only one ``state_name``.
#. A *variable* which is a ``constituent`` is an *entire variable*; it
   is not a component of a containing object.
#. If an ``abstract_state_name`` and its ``constituent`` have the same
   name this represents the simple mapping of an abstract
   ``state_name`` on to a concrete *variable* of the same name.
#. A ``constituent`` with a ``property_list`` assumes the properties
   given in the list:

   * The property Volatile indicates that the ``constituent`` is
     Volatile and this ``simple_property`` must be supplemented by one
     of the ``simple_properties`` Input or Output indicating whether
     the ``constituent`` is a Volatile Input or a Volatile Output.
   * The ``name_value_property`` Integrity is used to specify an
     integrity level for the ``constituent``.  Integrity levels may be
     used in information flow analysis to control the flow of
     information from a less critical to a more critical object or
     ``state_name``.

#. A ``state_name`` declared in the Abstract State Aspect which
   has not designated as Volatile may be refined on to one or more
   Volatile Input or Output ``constituents`` as well as non-volatile
   ``constituents``.
#. If a ``state_name`` declared in the Abstract State Aspect has been
   designated as Volatile with a ``property`` of Input (Output) then
   at least one ``constituent`` of the ``state_name`` must also be
   designated as Volatile with a ``property`` of Input (Output) in
   the Refined State Aspect.
#. A **null** ``abstract_state_name`` represents a hidden state
   component of a package which has no logical effect on the view of
   the package visible to a user.  An example would be a cache used to
   speed up an operation but does not have an effect on the result of
   the operation.
#. A non-volatile ``constituent`` of a **null** ``abstract_state_name``
   must be initialized by package elaboration.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. If a package has no Abstract State Aspect or no Pure aspect or
   pragma it may have internal state.  First an implicit
   Refined State Aspect is synthesized using the predefined
   categories of state, Non_Volatile_Initialized,
   Non_Volatile_Uninitialized, Volatile_Input and Volatile_Output.  An
   implicit Abstract State Aspect is synthesized from the
   synthesized Refined State Aspect.

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


Abstract State and Package Hierarchy
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: We need to consider the interactions between package hierarchy and abstract state.
          Do we need to have rules restricting access between parent and child packages?
          Can we ensure abstract state encapsulation?
          To be completed in the Milestone 3 version of this document.


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
Refined Global aspect applied to its body or body stub. The
Refined Global aspect defines the global items of the subprogram
in terms of the ``constituents`` of a ``state_name`` of the package
rather than the ``state_name``.

The Refined Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Global" and the ``aspect_definition`` must follow
the grammar of ``global_specification`` in :ref:`global-aspects`.

.. todo:: Complete language definition for Refined_Global aspect.
          To be completed in the Milestone 3 version of this document.

.. centered:: **Legality Rules**

#. A Refined Global Aspect may only appear on the body or body stub
   of a subprogram P in a package whose ``visible_part`` contains the
   declaration of P.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. A Refined Global Aspect on the body or body stub of a
   subprogram P may only mention ``constituents`` of a ``state_name``
   given in the Global Aspect in the declaration of P, a *global*
   item, which is not a ``state_name`` of the enclosing package, named
   in the the Global Aspect of P or a ``constituent`` of a
   **null** ``abstract_state_name``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**


#. A Refined Global Aspect of a subprogram defines a *refinement*
   of the Global Aspect of the subprogram.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. A *refinement* G' of a Global Aspect G declared within package
   Q shall satisfy the following rules:

   * For each item in G which is not a ``state_name`` of Q, the same
     item must appear with the same mode in G';
   * For each item in G which is a ``state_name`` S of package Q that
     is non-volatile at least one ``constituent`` of S must appear in
     G' and,

     * if the item in G has mode **in** then each ``constituent`` of S
       in G' must be of mode **in**.
     * if the item in G has mode **out** then each ``constituent`` of
       S in G' must be of mode **out**.
     * if the item in G has mode **in out** then each ``constituent``
       of S in G' may be of mode **in**, **out** or **in out** but if
       S has only one ``constituent`` it must appear in G' with the
       mode **in out**.  Each ``constituent`` of S in G' may be of
       mode **out** provided that not every ``constituent`` of S is
       included in G'.

   * For each item in G which is a ``state_name`` S of package Q that
     is Volatile at least one ``constituent`` of S must appear in G'
     and,

     * if S is a Volatile Input at least one ``constituent`` of S in
       G' must be of mode **in**.
     * if S is a Volatile Output at least one ``constituent`` of S in
       G' must be of mode **out**.

   * A ``constituent`` of a **null** ``abstract_name`` may also be
     mentioned in G' provided its mode is **in out**.

   * function may have a Refined Global Aspect G' which mentions a
     ``constituent`` of a **null** ``abstract_name`` but its mode must
     be **in out**.  The **null** ``abstract_state`` does not appear
     in G. The **null** ``abstract_state`` must not affect the value of the
     result of the function it must be purely for optimization.

#. If a subprogram has a Refined Global Aspect which satisfies the
   flow analysis checks, it is used in the analysis of the subprogram
   body rather than its Global Aspect.

* If the declaration of a subprogram P in the visible part of package
  Q has a Global Aspect which mentions a ``state_name`` of Q, but
  P does not have a Refined Global Aspect then an implicit
  Refined Global Aspect will be synthesized from the body of P.`

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
