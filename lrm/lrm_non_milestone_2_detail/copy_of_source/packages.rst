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

#. A Volatile Input or Output state abstraction represents a sequence
   of state changes brought about by reading or writing successive
   values to or from a volatile variable.


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

Synthesized State Abstractions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A package which has hidden state is considered to have one or more
state abstractions even if they are not explicitly declared.  If the
state abstractions are not explicitly declared they will be
synthesized from the implementation (if it exists) of the package and
its private descendent.

.. centered:: **Static Semantics**

#. A state abstraction of a package is considered to represent
   hidden state in one of the following categories:

   * Non-Volatile Uninitialized State - state which is not initialized
     during the elaboration of the package
   * Non-Volatile Initialized State - state which is initialized
     during the elaboration of the package
   * Volatile Input State - Volatile state which is an input only and
     is considered to be implicitly initialized.
   * Volatile Output State - Volatile state which is an output only
     and is considered to be implicitly initialized.

#. If a package has hidden state but no Abstract State Aspect is
   provided, a state abstraction is synthesized for each category of
   hidden state for which there exits *variables* of the category.
   The synthesized state abstractions are given one of the following
   default ``state_names`` representing each of the categories of
   state:

   * Uninitialized_State
   * Initialized_State
   * Volatile_Input_State
   * Volatile_Output_State

   A default ``state_name`` is only synthesized if the hidden state of
   the corresponding category is present within the package or its
   private descendants.


Input, Output and Integrity Aspects
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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

Package Depends Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~

An important property of a package is the state components it
initializes during its elaboration and on what the initial value of
each depends.  This information is required for flow analysis which is
used to demonstrate that every variable in a |SPARK| program is
initialized before use.

The package-level Depends aspect is introduced by an
``aspect_specification`` where the ``aspect_mark`` is Depends and the
``aspect_definition`` must follow the grammar of ``dependency_relation``
given in section :ref:`depends_aspect`.

.. centered:: **Legality Rules**

#. Every ``input`` and ``output`` of a ``dependency_relation`` of a Depends
   aspect of a package specification is a state abstraction.
#. A Depends aspect may appear in the ``aspect_specification``
   of a package specification but it must follow the
   Abstract State aspect if one is present.
#. A Depends aspect of a package shall not allow the optional ``+``
   within a ``dependency_clause``.
#. A Depends aspect of a package shall not allow a ``function_result``
   as an ``output``.
#. A Depends aspect of a package shall not allow ``null`` as an
   ``output_list``.
#. A ``state_name`` that is designated as ``Volatile`` must not appear in
   an ``output_list`` in a Depends aspect of a package.

#. The object denoted by a given ``output`` in an ``output_list`` shall
   not be denoted by any other ``output`` in that ``output_list``.   

#. The object denoted by a given ``input`` in an ``input_list`` shall
   not be denoted by any other ``input`` in that ``input_list``.  

.. centered:: **Static Semantics**

#. An *output* of a package elaboration is a state abstraction such that the
   set of variables represented by the state abstraction is initialized during
   elaboration.
#. An *input* of a package elaboration is a state abstraction such that the
   initial value of one or more of the set of variables represented by that
   state abstraction may be used to determine the final value of one or more
   members of the set of variables represented by the outputs of the
   package elaboration.
#. The Depends aspect of a package declaration describes for
   each ``output`` of the package elaboration a list of every ``input``
   on which the initial value of that ``output`` depends.  [A package may
   initialize an item at the point of declaration of the item, in the
   sequence of statements of its body, within an embedded package or a
   private descendent of the package.]
#. A package that does not initialize any state components can be
   explicitly indicated using a **null** ``dependency_relation``.
#. A ``dependency_clause`` with a **null** ``input_list`` means that the final
   value of each ``output`` in the ``output_list`` does not depend on any
   ``input``.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. If a Depends aspect is provided on a package declaration
   then flow analysis does not require the package body to proceed
   with the analysis of clients of the package.  Flow analysis will
   check that the body of the package satisfies its
   Depends aspect when it is analyzed.
#. Only *inputs* of a package elaboration shall appear as an ``input``
   in its Depends aspect.
#. Every *output* of a package elaboration shall appear as an ``output``
   in the Depends aspect of the package, if one is present.
#. A ``state_name`` designated as Volatile shall only appear in a
   Depends aspect if the package reads or updates the Volatile
   variables represented by the ``state_name`` during its elaboration
   or the elaboration of its private descendants.
#. If a Depends aspect (or an equivalent
   Initializes aspect) is not provided on a package declaration,
   its body and any private descendants must be present as well as the
   bodies of any packages on which the package depends to synthesize
   an implicit Depends aspect for the package.  Ultimately this
   could require an entire program analysis.
#. Library level packages are considered to be elaborated in some
   order determined by the compiler prior to a call to the main
   subprogram.  When the main subprogram is analysed the elaboration
   of the library-level packages is modelled as a sequence of
   subprogram calls, one for each package, in the same order as
   determined for package elaboration by the compiler.  Flow analysis
   is used to determine from the sequence of subprogram calls whether
   a *variable* or ``state_name`` is initialized and whether it is
   potentially erroneously initialized more than once prior to the
   call to the main subprogram.
#. For flow analysis purposes, the elaboration of a package embedded
   within a subprogram or block statement is modelled as a subprogram
   call immediately following the package declaration.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
Depends aspect as the rules are checked by static analysis.

.. centered:: **Examples**

.. code-block:: ada

    package Q
    with
       Abstract_State => State,  -- Declaration of abstract state name State
       Depends        => (State => null)
                                 -- Indicates that State will be initialized
    is                           -- during the elaboration of Q
				 -- or a private descendant of the package.
      ...
    end Q;

    package X
    with
       Abstract_State =>  A,          -- Declares an abstract state name A.
       Depends        => (A => null,  -- Indicates that A and visible variable 
                          B => null)  -- B will be initialized during the.
                                      -- elaboration of X or a private descendant
    is                                -- of the package.
      ...
      B : Integer;
     --
    end X;

    with Q;
    package Y
    with
       Abstract_State => (A, B, (C with Volatile, Input)),
       Depends        => (A => null,
                          B => Q.State)
    is                    -- Three abstract state names are declared A, B & C.
                          -- A is initialized during the elaboration of Y or
			  -- its private descendants.
       ...                -- B is initialized during the elaboration of Y or
                          -- its private descendants and is dependent on the
                          -- value of Q.State.
                          -- C is designated as a volatile input and is not
                          -- read during package elaboration and so does not appear
		          -- in the Depends aspect.
    end Y;

    package Z
    with
       Abstract_State => A,
       Depends        => null
    is                          -- Package Z has an abstract state name A declared but the
                                -- elaboration of Z and its private descendants do not
                                -- perform any initialization.
      ...

    end Z;



Initializes Aspect
~~~~~~~~~~~~~~~~~~

The Initializes Aspect is a shorthand notation for the most common
form of package initialization where none of the initialized items
have any dependence.  They are initialized from static or compile-time
constants.

The Initializes Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Initializes" and the ``aspect_definition`` must follow
the grammar of ``initialization_list`` given below.

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

The Initial Condition Aspect is a predicate that may be used to
describe formally the initial state of a package.  It behaves as a
postcondition for the result of package elaboration.

The Initial Condition Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Initial_Condition" and the ``aspect_definition`` must be
an ``expression``.

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

The Refined State Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_State" and the ``aspect_definition`` must follow
the grammar of ``state_and_category_list`` given below.

.. centered:: **Syntax**

::

  state_and_category_list          ::= (state_and_category {, state_and_category})
  state_and_category               ::= abstract_state_name => constituent_with_property_list
  abstract_state_name              ::= state_name | null
  constituent_with_property_list   ::= constituent_with_property
                                     | (constituent_with_property {, constituent_with_property})
  constituent_with_property        ::= constituent
                                     | (constituent_list with property_list)
  constituent_list                 ::= constituent
                                     | (constituent {, constituent})

where

  ``constituent ::=`` *variable_*\ ``name | state_name``

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

If a package has a Depends aspect or an
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

#. For each ``export`` that appears in a Depends aspect or
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

A subprogram declared in the visible part of a package may have a
Refined Global Aspect applied to its body or body stub. The
Refined Global Aspect defines the global items of the subprogram
in terms of the ``constituents`` of a ``state_name`` of the package
rather than the ``state_name``.

The Refined Global Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Global" and the ``aspect_definition`` must follow
the grammar of ``global_specification`` in :ref:`global-aspect`.

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

