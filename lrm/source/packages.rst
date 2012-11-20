Packages
========

Package Specifications and Declarations
---------------------------------------

.. _abstract-state:

Abstraction of State
~~~~~~~~~~~~~~~~~~~~

The *variables* declared immediately within a package Q, its embedded
packages and its private descendants constitute the state of Q.

For a package declared immediately in the body of package, an embedded
package E, the *variables* which form part of the state are the
*variables* declared immediately within E and embedded packages
declared immediately within E.

The *variable* declarations are only visible to clients of Q if they
are declared in the ``visible_part`` of Q which is not considered good
practice in general for public (non-private) packages.  The
declarations of all other variables are hidden from the user of Q.
Though the variables are hidden they still form part (or all) of the
state of Q and this hidden state cannot be ignored for static analyses
and proof.  State abstraction is the means by which this hidden state
is managed for static analyses and proof.

|SPARK| extends the concept of state abstraction to provide
hierarchical data abstraction whereby the hidden state of a package Q
may be refined over a tree of private descendants or embedded packages
of Q.  This provides data refinement similar to the refinement
available to types whereby a record may contain fields which are
themselves records.

The other feature supported using state abstraction is a logical model
of volatile *variables*.  A volatile *variable* does not behave like
standard non-volatile *variable* as its value may change between two
successive reads without an intervening update, or successive updates
may occur without any intervening reads and appear to have no effect
on the program.  Often volatile *variables* are inputs or outputs to
external devices or subsystems.

For flow analysis and proof volatile *variables* have to be modelled
differently to standard non-volatile *variables*.  The abstract state
aspect provides a way to designate a named abstract state as being
volatile, usually representing an external input or output.  This
abstract state may be refined on to actual *variables* which are the
input or output ports connected to the external device.

The modelling of volatile variables in this way may only be achieved
by explicitly providing the abstract state aspect and refined state
aspect described in the following subsections.

.. _abstract-state-aspect:

Abstract State Aspect
~~~~~~~~~~~~~~~~~~~~~

State abstraction provides a mechanism for naming, in a packages's visible
part, state (typically variable declarations) that will be declared within
the package's body (or private part, or within private child units of the
package). For example, a package declares a visible procedure and we wish to
specify the set of global variables that the procedure reads and writes
as part of the specification of the subprogram. Those variables cannot
be named directly in the package specification. Instead, we introduce
a state abstraction which is visible in the package specification and
later, when the package body is declared, we specify the set of
variables that "comprise" or "implement" that state abstraction. If a
package body contains, for example, a nested package, then a state
abstraction of the inner package may also be part of the implementation
of the given state abstraction of the outer package. No such mechanism
is  needed for visible state (i.e., variables declared in the visible part
of a package).

The "hidden" state of a package (roughly speaking, all variables declared
within the the private part or body of the package but not within
a more nested subprogram body or block statement; state declared in
private child units is also included) may be represented by one or more state
abstractions, with each pair of state abstractions representing disjoint
sets of hidden variables.

If a subprogram P with a Global Aspect is declared in the
``visible_part`` of a package and P reads or updates any of the hidden
state of the package then P must include in its Global Aspect the
abstract state names with the correct mode that represent the hidden
state referenced by P.  If P has a Dependency Aspect then the
abstract state names must appear as imports and exports, as
appropriate, in the ``dependency_relation`` of the aspect.

The Abstract State Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Abstract_State" and the ``aspect_definition`` must follow
the grammar of ``abstract_state_list`` given below.

.. centered:: **Syntax**

::

  abstract_state_list   ::= null
                          | state_name
                          | (state_name_with_properties { , state_name_with_properties } )
  state_name_with_properties ::= state_name
                               | ( state_name with property_list )
  property_list ::= property { , property }
  property ::= simple_property
             | name_value_property
  simple_property ::= indentifier
  name_value_property ::= identifier => expression
  state_name ::= defining_identifier

.. note:: This grammar is new, proposed by RCC and TJJ following a comment from SB on
   12/11/2012. We feel the use of the "A with P1, P2" extension aggregate grammar is much
   more elegant than the old "nested aggregate" like grammar.

.. centered:: **Static Semantics**

Each state_name occurring in an Abstract_State aspect specification
for a given package P introduces an implicit
declaration of a *state abstraction* entity. This implicit declaration
occurs at the beginning of the visible part of P. This implicit
declaration requires completion.

[A state abstraction shall only be
named in contexts where this is explicitly permitted (e.g., as part of a
Globals aspect specification), but this is not a name resolution rule.
Thus, the declaration of a state abstraction has the same visibility
as any other nonoverloadable declaration (e.g., an exception declaration).
A state abstraction is not an object; it does not have a type.
The completion of a state abstraction can only be provided as part of
a Refined_State aspect specification, provided when the body of P is
provided.]

.. note::
 (SB) I use the term "state abstraction" because I don't want to call
 it an object or a variable. Every variable is an object, every object
 has a type, and these guys don't have a type. Like, for example,
 exceptions or packages, these guys are (nonoverloadable)
 entities but are not objects. We could call them "abstract state
 entities" if that seems better. I understand that introducing this
 new terminology will require changing some existing wording, but calling
 these guys objects or variables is asking for trouble. Ask Robert for
 his opinion of Ada's "a generic subprogram is not a subprogram, a
 generic package is not a package" rule.

.. note::
 (SB) removing references to "observable" state for now. We can
 defer mention of caches until we get to refinement.

.. centered:: **Legality Rules**

#. The ``identifier`` of a ``simple_property`` shall be "Volatile",
   "Input", or "Output".
#. If a ``property_list`` includes "Volatile",
   then it shall also include exactly one of ``Input`` or ``Output``.
#. If a ``property_list`` includes either "Input" or "Output",
   then it shall also include "Volatile".
#. The ``identifier`` of a ``name_value_property`` shall be
   "Integrity".
#. The ``expression`` of an "Integrity" property shall be a static
   expression of any integer type.

.. centered:: **Static Semantics**

#. The "hidden state" of a package is the set of variables declared
   within the private part or body of a package and also includes the
   hidden state of any private child units of the package.

#. A **null** ``abstract_state_list`` specifies that the set of variables
   comprising the hidden state of the package shall be empty.
   [The specification is verified during flow analysis.]

#. A volatile state abstraction is one declared with a property list
   which includes the **Volatile** property, and similarly for
   **Input** and **Output**.
   Volatile variables (and volatile state abstractions) may not
   be part of the implementation of a non-volatile state abstraction.
   [This rule is verified during flow analysis.]

.. note::
 (SB) further cleanup needed here. I'll get back to this if I have time.
 Review of volatility-related stuff needed.

#. A Volatile Input state abstraction shall not be named in a moded_item of
   mode **in out** or  **out**.
#. A Volatile Input state abstraction shall not be named in a moded_item of
   mode **out**.
#. A Volatile Output may only occur where a ``state_name`` may appear
   as a ``moded_item`` of mode **out**.
#. A ``state_name`` of a package is generally considered to be
   representing hidden state in one of the following categories:
 
   * Non-Volatile Uninitialized State - state which is not initialized
     during the elaboration of the package
   * Non-Volatile Initialized State - state which is initialized
     during the elaboration of the package
   * Volatile Input State - Volatile state which is an input only and
     is considered to be implicitly initialized.
   * Volatile Output State - Volatile state which is an output only
     and is considered to be implicitly initialized.

#. A Volatile Input or Output ``state_name`` represents a sequence of state
   changes brought about by reading or writing successive values to or
   from a Volatile *variable*.
#. Each time a subprogram is called which has a Volatile Input
   ``state_name`` in its Global Aspect it ultimately reads a
   Volatile *variable*.  The value of this *variable* may be different
   each time it is read. A normal non-volatile *variable* would have
   the same value unless there was an intervening update of the
   *variable*. This distinction with a normal non-volatile variable or
   ``state_name`` is important for both flow analysis and proof.
#. Each time a subprogram is called which has a Volatile Output
   ``state_name`` in its Global Aspect it ultimately writes to a
   Volatile *variable*.  This *variable* may be written to many times
   without intervening reads.  This is in contrast with a normal
   non-volatile variable or state where successive updates with no
   intervening reads would indicate that earlier updates were
   ineffective.  Flow analysis and proof have to take account of this
   difference.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. If a package has hidden state but no Abstract State Aspect is
   provided, an implicit ``state_name`` is generated for each category
   of hidden state.  The implicit ``state_names`` cannot be referenced
   directly but they may be indirectly accessed using the following
   attributes for the different categories of hidden state:

   * *package_*\ ``name'Uninitialized_State``
   * *package_*\ ``name'Initialized_State``
   * *package_*\ ``name'Volatile_Input_State``
   * *package_*\ ``name'Volatile_Output_State``

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
Abstract State Aspect the rules are checked by static analysis.

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

        procedure Op1 (V : Integer)     -- Another procedure providing some operation on State
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

   package MILS -- a package that manages distinct state of differing Integrities
      with Abstract_State => ((Top_Secret   with Integrity => 4),
                              (Unclassified with Integrity => 0));
   is                          
      ...                      
   end MILS; 

   package Sensor -- simple volatile, input device driver
      with Abstract_State => ((Port with Volatile, Input));
   is
      ...
   end Sensor;


Input, Output and Integrity Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For variables which are declared directly within the visible part of a
package specification, the Volatile, Input, Output,
and Integrity aspects may be specified directly as part of the
variable's declaration.

.. centered:: **Legality Rules**

#. Input and Output are Boolean aspects, so have no ``aspect_definition`` part.
#. Integrity requires an ``aspect_definition`` which is a static expression of any integer type.
#. The Input, Output and Integrity aspects may only be applied to a variable declaration
   that appears in the visible part of a package specification.
#. If a variable has the Volatile aspect, then it must also have exactly one of the Input or Output
   aspects.

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

Package Dependency Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~

An important property of a package is the state components it
initializes during its elaboration and on what the inital value of
each depends.  This information is required for flow analysis which is
used to demonstrate that every variable in a |SPARK| program is
initialized before use.

.. centered:: **Legality Rules**

#. A Dependency Aspect may appear in the ``aspect_specification``
   of a package specification but it must follow the
   Abstract State Aspect if one is present.
#. A Dependency Aspect of a package has extended visibility; it is
   able to refer to *variables* declared in the visible part of the
   package.

.. centered:: **Static Semantics**

#. The Dependency Aspect of a package declaration describes for
   each *variable* or ``state_name`` that the package initializes
   during its elaboration a list of every ``moded_item`` on which each
   initial value depends.  A package may initialize an item at the
   point of declaration of the item, in the sequence of statements of
   its body, within an embedded package or a private descendent of the
   package.
#. A package that does not initialize any state components can be
   explicitly indicated using a **null** ``dependency_relation``.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. If a Dependency Aspect is provided on a package declaration
   then flow analysis does not require the package body to proceed
   with the analysis of clients of the package.  Flow analysis will
   check that the body of the package satisfies its
   Dependency Aspect when it is analyzed.
#. Only state components initialized by the package or its private
   descendants shall appear in its Dependency Aspect.
#. Each *variable* or ``state_name`` initialized by a package must
   appear as an ``export`` in the Dependency Aspect of the
   package, if one is present.
#. A ``state_name`` designated as Volatile shall only appear in a
   Dependency Aspect if the package reads or updates the Volatile
   variables represented by the ``state_name`` during its elaboration
   or the elaboration of its private descendants. 
#. If a Dependency Aspect (or an equivalent
   Initializes Aspect) is not provided on a package declaration,
   its body and any private descendants must be present as well as the
   bodies of any packages on which the package depends to synthesize
   an implicit Dependency Aspect for the package.  Ultimately this
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
   within a subprogram or block statement is modelled as a subporgram
   call immediately following the package declaration.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
Dependency Aspect the rules are checked by static analysis.

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
       Depends        => (A => null,  -- A and visible variable B are initialized
                          B => null)  -- during package initialization.
                                
    is                           
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
		          -- in the Dependency Aspect.
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

  initialization_list   ::= null
                          | export_list
  initialized_item_list ::= export
                          | (export {, export})


.. centered:: **Legality Rules**

#. An Initializes Aspect may only appear in the
   ``aspect_specification`` of a package specification.
#. The Initializes Aspect must follow the
   Abstract State Aspect if one is present.
#. An ``aspect_specification`` shall not have an
   Initializes Aspect if it has a Dependency Aspect.
#. An Initializes Aspect of a package has extended visibility; it
   is able to refer to *variables* declared in the visible part of the
   package.
#. An ``export`` may not appear more than once in an
   Initializes Aspect.
#. A *variable* appearing in an Initializes Aspect must be entire,
   it cannot be a subcomponent of a containing object.
#. A ``state_name`` which is designated as ``Volatile`` must not
   appear in an Initializes Aspect.


.. centered:: **Static Semantics**

#. An Initializes Aspect is a shorthand notation for a
   Dependency Aspect of the form:

   ::

     Depends => (S1 => null,
                 S2 => null,
                 ...
                 Sn => null)

     where
    
       each S1 .. Sn is a *variable* or ``state_name`` initialized
       during the elaboration of the package.

#. A **null** ``initialization_list`` is equivalent to a **null**
   ``dependency_relation``.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
Initializes Aspect the rules are checked by static analysis.


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

#. An Initial Condition Aspect may only be placed in a
   ``aspect_specification`` of a ``package_specification``.
#. The Initial Condition Aspect must follow the
   Abstract State Aspect, Dependency Aspect and
   Initializes Aspect if they are present.
#. The predicate of an Initial Condition Aspect appearing in a
   package Q has extended visibility.  It may reference declarations
   from the visible part of Q.

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
   anInitial Condition Aspect but it may be indirectly referenced
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
       Abstract_State    =>  A,    -- Declares an abstract state neme A
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
abstract view of the ``state_name``.  Refined global, dependency, pre
and post aspects are provided to express the refined view.

In the refined view the constituents of each ``state_name`` have to be
initialized consistently with their appearance or omission from the
Package Dependency or Initializes Aspect of the package.


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

.. centered:: **Legality Rules**

#. A Refined State Aspect may only appear in the body of a
   package.
#. If a package declaration has an Abstract State Aspect its body
   must have a Refined State Aspect.
#. If a package declaration does not have an Abstract State Aspect,
   then the corresponding package body *may* have a Refined State Aspect
   with exactly one ``state_and_category`` where the ``abstract_state_name`` is **null**.
#. A Refined State Aspect of a package body has extended
   visibility; it is able to refer to a *variable* declared in the
   package body, or a ``state_name`` or *variable* declared in the
   visible part of a package, declared immediately within the package
   body.
#. Each ``state_name`` declared in a package specification must appear
   exactly once as an ``abstract_state_name`` in the
   Refined State Aspect of the body of the package.
#. If a ``constituent`` has the same name as an
   ``abstract_state_name`` it can only be a ``constituent`` of that
   ``abstract_state_name`` and it must be the only ``constituent`` of
   the ``abstract_state_name``.
#. The ``identifier`` of a ``simple_property`` shall be "Volatile",
   "Input", or "Output".
#. If a ``property_list`` includes the ``simple_property`` "Volatile",
   then the same ``property_list`` shall also include exactly one of
   ``Input`` or ``Output``.
#. The ``identifier`` of a ``name_value_property`` shall be
   "Integrity".
#. The ``expression`` of an "Integrity" property shall be a static
   expression of any integer type.
#. The same identifier shall not appear more than once in a property
   list.
#. There should be at most one **null** ``abstract_state_name`` and,
   if it is present it must be non-volatile and the last entry of the 
   ``state_and_category_list``.


.. centered:: **Static Semantics**

#. A Refined State Aspect defines the *variables* and each
   subordinate ``state_name`` which are the constituents that comprise
   the hidden state represented by the ``state_name`` declared in the
   Abstract State Aspect.
#. A ``constituent`` of the hidden state of a package Q is one of:

   * A *variable* declared in the ``private_part`` or body of Q;
   * A *variable* declared in the ``visible_part`` of a package
     declared immediately within the ``private_part`` or body of Q;
   * A *variable* declared in the ``visible_part`` of a private child
     package of Q;
   * A ``state_name`` declared in the Abstract State Aspect of a
     package declared immediately within the ``private_part`` or body
     of a package Q; or
   * A ``state_name`` declared in the Abstract State Aspect of a
     private child package of Q.

#. Each ``constituent`` of the hidden state of must appear exactly
   once in a ``constituent_list`` of exactly one
   ``state_and_category``; that is each ``constituent`` must
   be a constituent of one and only one ``state_name``.
#. A *variable* which is a ``constituent`` is an *entire variable*; it
   is not a component of a containing object.
#. If an ``abstract_state_name`` and its ``constituent`` have the same
   name this represents the simple mapping of a an abstract
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
be volatile. The volatile *variable* will declared in the body of a
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
   external variables different to the broken 'Tail scheme in SPARK95.
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
   read after writing but need not be. This scheme has beeen
   requested by secunet.  In this scheme the output would be volatile
   but the input non-volatile. Target: rel2+.


Initialization Refinement
~~~~~~~~~~~~~~~~~~~~~~~~~

If a package has a Dependency Aspect or an
Initializes Aspect which contains a ``export`` which is a
``state_name`` then each ``constituent`` of the ``state_name`` must be
initialized during package elaboration or be designated as Volatile,
in which case they are implicitly initialized.  A ``constituent`` of a
non-volatile ``state_name`` of a package which does not appear in the
Initializes Aspect of the package must not be initialized during
package elaboration.  A ``constituent`` of a Volatile ``state_name``
which is non-volatile must initialized during package elaboration.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. For each ``export`` that appears in a Dependency Aspect or
   Initializes Aspect of a package declaration the following must
   be satisfied:

   * Each ``export`` that is a *variable* must be initialized at its
     point of declaration, initialized by the sequence of statements
     of the package, or by an embedded package or a private child
     package which names the ``export`` in its Dependency Aspect
     or Initializes Aspect;
   * For an ``export`` which is a ``state_name``, each ``constituent``
     of the ``export`` that is a *variable* must be initialized at
     its point of declaration, initialized by the sequence of
     statements of the package, or by an embedded package or a private
     child package which names the ``export`` in its
     Dependency Aspect or Initializes Aspect; 
   * For an ``export`` which is a ``state_name`` each ``constituent``
     of the ``export`` that is a ``state_name`` must appear in the
     Dependency Aspect or Initializes Aspect of an embedded
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
the grammar of ``mode_refinement`` in :ref:`mode-refinement`.

.. centered:: **Legality Rules**

#. A Refined Global Aspect may only appear on the body or body stub
   of a subprogram P in a package whose ``visible_part`` contains the
   declaration of P.
#. A Refined Global Aspect on the body or body stub of a
   subprogram P may only mention ``constituents`` of a ``state_name``
   given in the Global Aspect in the declaration of P, a *global*
   item, which is not a ``state_name`` of the enclosing package, named
   in the the Global Aspect of P or a ``constituent`` of a
   **null** ``abstract_state_name``.


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
  a pakage Q does not have a Global Aspect, first an implicit
  Refined Global Aspect is synthesized from the body of P, then an
  implicit Global Aspect is synthesized from the synthesized
  Refined Global Aspect and the Refined State Aspect (which may also
  have been synthesized).

.. _refined-dependency-aspect:

Refined Dependency Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~

A subprogram declared in the visible part of a package may have a
Refined Dependency Aspect applied to its body or body stub. The
Refined Dependency Aspect defines the ``dependency_relation`` of the
subprogram in terms of the ``constituents`` of a ``state_name`` of the
package rather than the ``state_name``.

The Refined Dependency Aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is "Refined_Depends" and the ``aspect_definition`` must follow
the grammar of ``dependency_relation``.

.. centered:: **Legality Rules**

#. A Refined Dependency Aspect may only appear on the body or body
   stub of a subprogram P in a package whose ``visible_part`` contains
   the declaration of a subprogram P.
#. A Refined Dependency Aspect on the body or body stub of a
   subprogram P may only mention a formal parameter of P,
   ``constituents`` of a ``state_name`` of the enclosing package given
   in the Dependency Aspect in the declaration of P, a *global*
   item that is not a ``state_name`` of the enclosing package or a
   ``constituent`` of a **null** ``abstract_state_name``.

.. centered:: **Static Semantics**

#. A Refined Dependency Aspect of a subprogram defines a *refinement*
   of the Dependency Aspect of the subprogram.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. If the subprogram declaration declared in the visible part of
   package Q has a Dependency Aspect D then the
   Refined Dependency Aspect defines a *refinement* D' of D
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
       
   * function may have a Refined Dependency Aspect D' which
     mentions a ``constituent`` of a **null** ``abstract_name`` but
     the constituent must appear as both an ``import`` and an
     ``export`` in D'.
   * A ``constituent`` of a **null** ``abstract_state_name`` is
     ignored in showing conformance between the Dependency Aspect
     and the Refined Dependency Aspect according to the rules
     given for a Dependency Aspect.

#. If a subprogram has a Refined Dependency Aspect which satisfies
   the flow analysis rules, it is used in the analysis of the
   subprogram body rather than its Dependency Aspect.
   
* If the declaration of a subprogram P in the visible part of package
  Q has a Dependency Aspect which mentions a ``state_name`` of Q,
  but P does not have a Refined Dependency Aspect then an implicit
  Refined Dependency Aspect will be synthesized from the body of P.`

* if the declaration of a subprogram P declared in the visible part of
  a pakage Q does not have a Dependency Aspect, an implicit one is
  synthesized from the Refined Dependency Aspect and the
  Refined State Aspect (both of which which may also have been
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
#. The same legality rules apply to a Refined Precondition as for
   a precondition.

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
   the precondition is evaluated as defined in the Ada LRM.  If the
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
#. The same legality rules apply to a Refined Postcondition as for
   a postcondition.

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
   LRM.  If either the Refined Postcondition or the postcondition
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

#. The Ada 2012 LRM lists places at which an invariant check is performed. In
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

