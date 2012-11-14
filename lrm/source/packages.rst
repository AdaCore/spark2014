Packages
========

Package Specifications and Declarations
---------------------------------------

.. centered:: **Restrictions that may be Applied**
.. include:: restrictions-and-profiles.rst
   :start-after: 7.1 Packages
   :end-before: 7.1.2

.. _abstract-state:

Abstraction of State
^^^^^^^^^^^^^^^^^^^^

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
differently to standard-non-volatile *variables*.  The abstract state
aspect provides a way to designate a named abstract state as being
volatile, usually representing an external input or output.  This
abstract state may be refined on to actual *variables* which are the
input or output ports connected to the external device.

The modelling of volatile variables in this way may only be achieved
by explicitly providing the abstract state aspect and state refinement
aspect described in the following subsections.

.. _abstract-state-aspect:

Abstract State Aspect
^^^^^^^^^^^^^^^^^^^^^

An abstract state is a name representing the state embodied by the
hidden state of a package. The overall state of a package may be
represented by one or more visible *variables* and abstract state
names, each abstract state name representing a mutually exclusive part
of the hidden state.  An abstract state name has no type and may only
be used within an ``initializes_aspect`, a ``global_aspect``, a
``dependency_aspect`` or the refined counterparts of a global or
dependency aspect.

If a subprogram P with a ``global_aspect`` is declared in the
``visible_part`` of a package and P reads or updates any of the hidden
state of the package then P must include in its ``global_aspect`` the
abstract state names with the correct mode that represent the hidden
state referenced by P.  If P has a ``dependency_aspect`` then the
abstract state names must appear as imports and exports, as
appropriate, in the ``dependency_relation`` of the aspect.


.. centered:: **Syntax**

::

  abstract_state_aspect  ::= Abstract_State => abstract_state_list
  abstract_state_list    ::= null
                           | state_name
                           | (category_state {, category_state})
  category_state         ::= [Non_Volatile =>] state_name_list
                           | Volatile => (moded_state_name_list {, moded_state_name_list})
  moded_state_name_list  ::= mode_selector => state_name_list
  state_name_list        ::= state_name
                           | (extended_state_name {, extended_state_name)
  extended_state_name    ::= state_name [=> Integrity]
  state_name             ::= defining_identifier

where

  ``integrity ::=`` *integer_*\ ``expression``

.. todo:: Consider whether we need the extended state_name with integrity

.. todo:: Consider whether we need Volatile => In_Out.

.. todo:: Consider a latched output mode selector, one that can be
   read after writing but need not be.  This scheme has beeen
   requested by secunet.  In this scheme the output would be volatile
   but the input non-volatile.

.. todo:: May introduce a way to provide a "history" parameter for
   Volatile variables.

.. centered:: **Legality Rules**

#. An ``abstract_state_aspect`` may only be placed in a
   ``aspect_specification`` of a ``package_specification``.
#. The ``defining_identifier`` of a ``state_name`` must not be the
   same as a directly visible name or a name declared immediately
   within the package containing the ``abstract_state_aspect``.
#. The ``defining_identifier`` of a ``state_name`` shall not be
   repeated within the ``abstract_state_list``.
#. A ``state_name`` can only appear in a ``initializes_aspect``, a
   ``global_aspect``, a ``dependency_aspect``, their refined
   counterparts, or their equivalent pragmas.  It may also appear as
   an ``abstract_state_name`` in a ``refined_state_aspect``.
#. At most one ``category_state`` of Volatile is permitted in an
   ``abstract_state_aspect``.
#. At most one of a Non_Volatile or a default ``category_state`` is
   permitted in an ``abstract_state_aspect``.
#. The only ``mode_selector`` values permitted are Input or Output.

.. centered:: **Static Semantics**

#. An abstract ``state_name`` is declared using a
   ``abstract_state_aspect`` appearing in an ``aspect_specification``
   of a ``package_specification``.  The ``state_name`` is an
   abstraction representing some or all of the hidden state of
   package, its embedded packages and its private descendants.
#. A ``state_name`` has the same scope and visibility as a declaration
   in the ``visible part`` of the package to which the
   ``abstract_state_aspect`` is applied.
#. A **null** ``abstract_state_list`` indicates that a package
   contains no observable hidden state and does not declare any
   ``state_name``.  The package may contain hidden state that has no
   observable effect, for instance a cache.  The package may contain
   visible state, that is, a *variable* declared in its visible part.
#. Volatile designates a volatile state, usually representing an
   external input or output.  The mode selector determines whether the
   volatile state is an input or an output.
#. A volatile Input may only occur where a ``state_name`` may appear
   as a ``moded_item`` of mode **in**.
#. A volatile Output may only occur where a ``state_name`` may appear
   as a ``moded_item`` of mode **out**.
#. A `state_name`` of a package is generally considered to be
   representing hidden state in one of the following categories:
 
   * Non_Volatile Uninitialized State - state which is not initialized
     during the elaboration of the package
   * Non_Volatile Initialized State - state which is initialized
     during the elaboration of the package
   * Volatile Input State - Volatile state which is an input only and
     is considered to be implicitly initialized.
   * Volatile Output State - Volatile state which is an output only
     and is considered to be implicitly initialized.

#. The category is specified using the ``category_state`` syntax
   supplemented by the ``initializes_aspect``.  A ``category_state``
   without a category defaults to Non_Volatile.
#. A Volatile In or Out ``state_name`` represents a sequence of state
   changes brought about by reading or writing successive values to or
   from a Volatile *variable*.
#. Each time a subprogram is called which has a Volatile Input
   ``state_name`` in its ``global_aspect`` it ultimately reads a
   Volatile *variable*.  The value of this *variable* may be different
   each time it is read. A normal non-volatile *variable* would have
   the same value unless there was an intervening update of the
   *variable*. This distinction with a normal non-volatile variable or
   ``state_name`` is important for both flow analysis and proof.
#. Each time a subprogram is called which has a Volatile Output
   ``state_name`` in its ``global_aspect`` it ultimately writes to a
   Volatile *variable*.  This *variable* may be written to many times
   without intervening reads.  This is in contrast with a normal
   non-volatile variable or state where successive updates with no
   intervening reads would indicate that earlier updates were
   ineffective.  Flow analysis and proof have to take account of this
   difference.
#. As a *variable* declared in the visible part of a public package
   cannot appear in an ``abstract_state_aspect`` it follows from the
   rules that it cannot be considered to be Volatile.

.. todo:: 
   Should we provide a way of allowing volatile variables 
   in the visible part of a public package?

.. todo:: Should we allow Volatile => In_Out?

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. If a package has hidden state but no ``abstract_state_aspect`` is
   provided, an implicit ``state_name`` is generated for each category
   of hidden state.  The implicit ``state_names`` cannot be referenced
   directly but they may be indirectly accessed using the following
   attributes for the different categories of hidden state:

   * *package_*\ ``name'Uninitialized_State``
   * *package_*\ ``name'Initialized_State``
   * *package_*\ ``name'Volatile_Input_State``
   * *package_*\ ``name'Volatile_Output_State``


.. centered:: **Restrictions that may be Applied**

.. include:: restrictions-and-profiles.rst
   :start-after: 7.1.2 Abstract State Aspect
   :end-before: 7.1.3 

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
``abstract_state_aspect`` the rules are checked by static analysis.

.. centered:: **Examples**

.. code-block:: ada

   package Q
   with 
      Abstract_State => State           -- Declaration of abstract state name State
   is                                   -- representing internal state of Q.
     function Is_Ready return Boolean   -- Function checking some property of the State.
     with 
        Global => State;                -- State may be used in a global aspect.

        procedure Init                  -- Procedure to initialize the internal state of Q.
        with 
	   Global => (Output => State), -- State may be used in a global aspect.
	   Post   => Is_Ready;

        procedure Op1 (V : Integer)     -- Another procedure providing some operation on
        with                            -- State.
           Global => (In_Out => State),
	   Pre    => Is_Ready,
	   Post   => Is_Ready;   
   end Q;

   package X
   with 
      Abstract_State => (A, B, 
                         (Volatile => (Input => C)))
   is                                   -- Three abstract state names are declared A, B & C. 
      ...                               -- C is designated as a volatile input.
   end X; 


Dependency  Aspects
^^^^^^^^^^^^^^^^^^^

An important property of a package is the state components it
initializes during its elaboration and on what the inital value of
each depends.  This information is required for flow analysis which is
used to demonstrate that every variable in a |SPARK| program is
initialized before use.

.. centered:: **Legality Rules**

#. A ``dependency_aspect`` may appear in the ``aspect_specification``
   of a package specification but it must follow the
   ``abstract_state_aspect`` if one is present.
#. A ``dependency_aspect`` of a package has extended visibility; it is
   able to refer to *variables* declared in the visible part of the
   package.

.. centered:: **Static Semantics**

#. The ``dependency_aspect`` of a package declaration describes for
   each *variable* or ``state_name`` that the package initializes
   during its elaboration a list of every ``moded_item`` on which each
   initial value depends.  A package may initialize an item at the
   point of declaration of the item, in the sequence of statements of
   its body, within an embedded package or a private descendent of the
   package.
#. A package that does not initialize any state components can be
   explicitly indicated using a **null** ``dependency_relation``.


.. centered:: **Restrictions that may be Applied**
.. include:: restrictions-and-profiles.rst
   :start-after: 7.1.3 Initializes Aspect
   :end-before: 7.1.4

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. If a ``dependency_aspect`` is provided on a package declaration
   then flow analysis does not require the package body to proceed
   with the analysis of clients of the package.  Flow analysis will
   check that the body of the package satisfies its
   ``dependency_aspect`` when it is analyzed.
#. Only state components initialized by the package or its private
   descendants shall appear in its ``dependency_aspect``.
#. Each *variable* or ``state_name`` initialized by a package must
   appear as an ``export`` in the ``dependency_aspect`` of the
   package, if one is present.
#. A ``state_name`` designated as Volatile shall only appear in a
   ``dependency_aspect`` if the package reads or updates the Volatile
   variables represented by the ``state_name`` during its elaboration
   or the elaboration of its private descendants. 
#. If a ``dependency_aspect`` (or an equivalent
   ``initializes_aspect``) is not provided on a package declaration,
   its body and any private descendants must be present as well as the
   bodies of any packages on which the package depends to synthesize
   an implicit ``dependency_aspect`` for the package.  Ultimately this
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

.. todo:: Consider rules for:
   
   elaboration order independence,

   constraining packages to initializing only their own variables,

   when depends/initializes aspects required by some rule assume no
   depends or initializes aspect implies Initializes => **null**.


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
``dependency_aspect`` the rules are checked by static analysis.

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
       Abstract_State => (A, B,
                          Volatile => (Input => C)),
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
		          -- in the dependency_aspect.
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



Initializes Aspects
^^^^^^^^^^^^^^^^^^^

The ``initializes_aspect`` is a shorthand notation for the most common
form of package initialization where none of the initialized items
have any dependence.  They are initialized from static or compile-time
constants.  


.. centered:: **Syntax**

::

  initializes_aspect    ::= Initializes => initialization_list
  initialization_list   ::= null
                          | export_list
  initialized_item_list ::= export
                          | (export {, export})


.. centered:: **Legality Rules**

#. An ``initializes_aspect`` may only appear in the
   ``aspect_specification`` of a package specification.
#. The ``initializes_aspect`` must follow the
   ``abstract_state_aspect`` if one is present.
#. An ``aspect_specification`` shall not have an
   ``initializes_aspect`` if it has a ``dependency_aspect``.
#. An ``initializes_aspect`` of a package has extended visibility; it
   is able to refer to *variables* declared in the visible part of the
   package.
#. An ``export`` may not appear more than once in an
   ``initializes_aspect``.
#. A *variable* appearing in an ``initializes_aspect`` must be entire,
   it cannot be a subcomponent of a containing object.
#. A ``state_name`` which is designated as ``Volatile`` must not
   appear in an ``initializes_aspect``.


.. centered:: **Static Semantics**

#. An ``initializes_aspect`` is a shorthand notation for a
   ``dependency_aspect`` of the form:

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

.. centered:: **Restrictions that may be Applied**
.. include:: restrictions-and-profiles.rst
   :start-after: 7.1.3 Initializes Aspect
   :end-before: 7.1.4


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
``initializes_aspect`` the rules are checked by static analysis.


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
       Abstract_State => (A, B,
                          Volatile => (Input => C)),
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
^^^^^^^^^^^^^^^^^^^^^^^^

The ''initial_condition_aspect`` is a predicate that may be used to
describe formally the initial state of a package.  It behaves as a
postcondition for the result of package elaboration.

.. centered:: **Syntax**

::
  
  initial_condition_aspect ::= Initial_Condition => predicate


 .. centered:: **Legality Rules**

#. An ``initial_condition_aspect`` may only be placed in a
   ``aspect_specification`` of a ``package_specification``.
#. The ``initial_condition_aspect`` must follow the
   ``abstract_state_aspect``, ``dependency_aspect`` and
   ``initializes_aspect`` if they are present.
#. The predicate of an ``initial_condition_aspect`` appearing in a
   package Q has extended visibility.  It may reference declarations
   from the visible part of Q.

.. centered:: **Static Semantics**

#. The predicate of an ``initial_condition_aspect`` of a package
   defines the initial state of the package after its elaboration and
   the elaboration of its private descendants.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. Each *variable* appearing in an ``initial_condition_aspect`` of a
   package Q which is declared in the visible part of Q must be
   initialized during the elaboration of Q and its private descendants.
#. A ``state_name`` cannot appear directly in
   an``initial_condition_aspect`` but it may be indirectly referenced
   through a function call.
#. Each ``state_name`` referenced in ``initial_condition_aspect`` must
   be initialized during package elaboration.

.. centered:: *Checked by Proof*

#. Verification conditions are generated which have to be proven to
   demonstrate that the implementation of a package Q and its private
   descendants satisfy the predicate given in the
   ``initial_condition_aspect`` of Q.

.. centered:: **Restrictions that may be Applied**

.. include:: restrictions-and-profiles.rst
   :start-after: 7.1.4 Initial Condition Aspect
   :end-before:  7.2.2 

.. centered:: **Dynamic Semantics**

#. An ``initial_condition_aspect`` is like a postcondition.  It
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

    with Another_Package;
    package Y
    with 
       Abstract_State    => (A, B, D),
       Initializes       => (A, Another_Package => D),
       Initial_Condition => A_Is_Ready and D_Property 
					-- Only the initial conditions of A and D are given
					-- B cannot be specified because it is not
					-- initialized during package elaboration.
                                        -- D can only be initialized in the sequence of statements of
                                        -- the body of Another_Package that has a with clause naming Y.
                                        -- For Another_Package to initialize D, D must be declared in
                                        -- the visible part of Y or a subprogram which initializes D
                                        -- must be declared in the visible part of Y.
    is                      
      function A_Is_Ready return Boolean;
      with
	 Global => A;

      function D_Property return Boolean
      with
	 Global => D;

      procedure Init_D
      with
         Global => (Output => D);

    end Y; 


.. todo:: Aspects for RavenSpark, e.g., Task_Object and Protected_Object



Package Bodies
--------------

State Refinement
^^^^^^^^^^^^^^^^

A ``state_name`` declared by an ``abstract_state_aspect`` in the
specification of a package Q is an abstraction of the non-visible
*variables* declared in the private part, body, or private descendants
of Q, which together form the hidden state, of Q.  In the body of Q
each ``state_name`` has to be refined by showing which *variables* and
subordinate abstract states are represented by the ``state_name`` (its
constituents).  A ``refined_state_aspect`` in the body of Q is used
for this purpose.

In the body of a package the constituents of the refined
``state_name``, the refined view, has to be used rather than the
abstract view of the ``state_name``.  Refined global, dependency, pre
and post aspects are provided to express the refined view.

In the refined view the constituents of each ``state_name`` have to be
initialized consistently with their appearance or omission from the
``initializes_aspect_clause`` of the package.


Refined State Aspect
^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

::

  refined_state_aspect             ::= Refined_State => state_and_category_list
  state_and_category_list          ::= (state_and_category {, state_and_category})
  state_and_category               ::= abstract_state_name => categorised_constituent_list
  categorised_constituent_list     ::= constituent_list
                                     | (Non_Volatile => constituent_list)
                                     | (Volatile     => moded_list)
  moded_list                       ::= (moded_constituent_list {, moded__constituent_list})
  moded_constituent_list           ::= mode_selector => constituent_list
  abstract_state_name              ::= state_name | null
  constituent_list                 ::= constituent
                                     | (constituent {, constituent})


where

  ``constituent ::=`` *variable_*\ ``name | state_name``

.. centered:: **Legality Rules**

#. A ``refined_state_aspect`` may only appear in the body of a
   package.
#. If a package declaration has an ``abstract_state_aspect`` its body
   must have a ``refined_state_aspect``.
#. A package body may only have a ``refined_state_aspect`` if its
   declaration does not have an ``abstract_state_aspect``, if its
   one and only ``abstract_state_name`` is **null**.
#. A ``refined_state_aspect`` of a package body has extended
   visibility; it is able to refer to a *variable* declared in the
   package body, or a ``state_name`` or *variable* declared in the
   visible part of a package, declared immediately within the package
   body.
#. Each ``state_name`` declared in a package specification must appear
   exactly once as an ``abstract_state_name`` in the
   ``state_refinement_aspect`` of the body of the package.
#. If a ``constituent`` has the same name as an
   ``abstract_state_name`` it can only be a ``constituent`` of that
   ``abstract_state_name`` and it must be the only ``constituent`` of
   the ``abstract_state_name``.
#. An entry of a ``categorised_constituent_list`` without a Volatile
   or Non_Volatile designator is taken to have the default designator
   of Non_Volatile.
#. At most one Volatile entry is permitted in a
   ``categorised_constituent_list``.
#. At most one of a Non_Volatile or a default entry is permitted in a
   ``categorised_constituent_list``.
#. There should be at most one **null** ``abstract_state_name`` and,
   if it is present it must be Non_Volatile and the last entry of the 
   ``state_and_category_list``.
#. Only ``mode_selector`` values of Input and Output may be used.

.. centered:: **Static Semantics**

#. A ``refined_state_aspect`` defines the *variables* and each
   subordinate ``state_name`` which are the constituents that comprise
   the hidden state represented by the ``state_name`` declared in the
   ``abstract_state_aspect``.
#. A ``constituent`` of the hidden state of a package Q is one of:

   * A *variable* declared in the ``private_part`` or body of Q;
   * A *variable* declared in the ``visible_part`` of a package
     declared immediately within the ``private_part`` or body of Q;
   * A *variable* declared in the ``visible_part`` of a private child
     package of Q;
   * A ``state_name`` declared in the ``abstract_state_aspect`` of a
     package declared immediately within the ``private_part`` or body
     of a package Q; or
   * A ``state_name`` declared in the ``abstract_state_aspect`` of a
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
#. The category of a ``constituent`` is specified using the Volatile,
   Non_Volatile or default designator in a
   ``categorised_constituent_list``.
#. A ``state_name`` declared in the ``abstract_state_aspect`` which
   has not designated as Volatile may be refined on to one or more
   Volatile Input or Output ``constituents`` as well as Non_Volatile
   ``constituents``.
#. If a ``state_name`` declared in the ``abstract_state_aspect`` has
   been designated as Volatile with a ``mode_selector`` M then at least
   one ``constituent`` of the ``state_name`` must also be designated
   as Volatile with a ``mode_selector`` M in the
   ``refined_state_aspect``.
#. A **null** ``abstract_state_name`` represents a hidden state
   component of a package which has no logical effect on the view of
   the package visible to a user.  An example would be a cache used to
   speed up an operation but does not have an effect on the result of
   the operation.
#. A Non_Volatile ``constituent`` of a **null** ``abstract_state_name``
   must be initialized by package elaboration.


.. todo:: Think about whether **null** abstract state can introduce a
   covert channel.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. If a package has no ``abstract_state_aspect`` or no Pure aspect or
   pragma it may have internal state.  First an implicit
   ``refined_state_aspect`` is synthesized using the predefined
   categories of state, Non_Volatile_Initialized,
   Non_Volatile_Uninitialized, Volatile_Input and Volatile_Output.  An
   implicit ``abstract_state_aspect`` is synthesized from the
   synthesized ``refined_state_aspect``.

.. centered:: **Restrictions that may be Applied**

.. include:: restrictions-and-profiles.rst
   :start-after: 7.2.2 Refined State Aspect
   :end-before:  END OF FILE 

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with state abstraction and refinement.

Abstract State and Package Hierarchy
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. todo::
   
   We need to consider the interactions between package hierarchy and abstract state.
   
   Do we need to have rules restricting access between parent and child packages?

   Can we ensure abstract state encapsulation?

Volatile Variables
^^^^^^^^^^^^^^^^^^

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

Initialization Refinement
^^^^^^^^^^^^^^^^^^^^^^^^^

If a package has a ``dependency_aspect`` or an
``initialization_aspect`` which contains a ``export`` which is a
``state_name`` then each ``constituent`` of the ``state_name`` must be
initialized during package elaboration or be designated as Volatile,
in which case they are implicitly initialized.  A ``constituent`` of a
Non_Volatile ``state_name`` of a package which does not appear in the
``initializes_aspect`` of the package must not be initialized during
package elaboration.  A ``constituent`` of a Volatile ``state_name``
which is Non_Volatile must initialized during package elaboration.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. For each ``export`` that appears in a ``dependency_aspect`` or
   ``initializes_aspect`` of a package declaration the following must
   be satisfied:

   * Each ``export`` that is a *variable* must be initialized at its
     point of declaration, initialized by the sequence of statements
     of the package, or by an embedded package or a private child
     package which names the ``export`` in its ``dependency_aspect``
     or ``initializes_aspect``;
   * For an ``export`` which is a ``state_name``, each ``constituent``
     of the ``export`` that is a *variable* must be initialized at
     its point of declaration, initialized by the sequence of
     statements of the package, or by an embedded package or a private
     child package which names the ``export`` in its
     ``dependency_aspect`` or ``initializes_aspect``; 
   * For an ``export`` which is a ``state_name`` each ``constituent``
     of the ``export`` that is a ``state_name`` must appear in the
     ``dependency_aspect`` or ``initializes_aspect`` of an embedded
     package or private child package.

#. A Non_Volatile ``constituent`` of a Volatile ``state_name`` must be
   initialized during package elaboration.
#. Each ``constituent`` of a **null** ``abstract_state_name`` must be
   initialized implicitly or during package elaboration.

.. _refined-global-aspect:

Refined Global Aspect
^^^^^^^^^^^^^^^^^^^^^

A subprogram declared in the visible part of a package may have a
``refined_global_aspect`` applied to its body or body stub. The
``refined_global_aspect`` defines the global items of the subprogram
in terms of the ``constituents`` of a ``state_name`` of the package
rather than the ``state_name``.

.. centered:: **Syntax**

::

  refined_global_aspect ::= Refined_Global => mode_refinement

.. centered:: **Legality Rules**

#. A ``refined_global_aspect`` may only appear on the body or body stub
   of a subprogram P in a package whose ``visible_part`` contains the
   declaration of P.
#. A ``refined_global_aspect`` on the body or body stub of a
   subprogram P may only mention ``constituents`` of a ``state_name``
   given in the ``global_aspect`` in the declaration of P, a *global*
   item, which is not a ``state_name`` of the enclosing package, named
   in the the ``global_aspect`` of P or a ``constituent`` of a
   **null** ``abstract_state_name``.


.. centered:: **Static Semantics**


#. A ``refined_global_aspect`` of a subprogram defines a *refinement*
   of the ``global_aspect`` of the subprogram.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. A *refinement* G' of a ``global_aspect`` G declared within package
   Q shall satisfy the following rules:
 
   * For each item in G which is not a ``state_name`` of Q, the same
     item must appear with the same mode in G';
   * For each item in G which is a ``state_name`` S of package Q that
     is Non_Volatile at least one ``constituent`` of S must appear in
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

   * function may have a ``refined_global_aspect`` G' which mentions a
     ``constituent`` of a **null** ``abstract_name`` but its mode must
     be **in out**.  The **null** ``abstract_state`` does not appear
     in G. The **null** ``abstract_state`` must not affect the value of the
     result of the function it must be purely for optimization.

#. If a subprogram has a ``refined_global_aspect`` which satisfies the
   flow analysis checks, it is used in the analysis of the subprogram
   body rather than its ``global_aspect``.
   
* If the declaration of a subprogram P in the visible part of package
  Q has a ``global_aspect`` which mentions a ``state_name`` of Q, but
  P does not have a ``refined_global_aspect`` then an implicit
  ``refined_global_aspect`` will be synthesized from the body of P.`

* if the declaration of a subprogram P declared in the visible part of
  a pakage Q does not have a ``global_aspect``, first an implicit
  ``refined_global_aspect`` is synthesized from the body of P, then an
  implicit ``global_aspect`` is synthesized from the synthesized
  ``refined_global_aspect`` and the ``refined_state_aspect`` (which may also
  have been synthesized).


.. todo:: Consider subprogram body renaming declarations.

.. _refined-dependency-aspect:

Refined Dependency Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^

A subprogram declared in the visible part of a package may have a
``refined_dependency_aspect`` applied to its body or body stub. The
``refined_dependency_aspect`` defines the ``dependency_relation`` of the
subprogram in terms of the ``constituents`` of a ``state_name`` of the
package rather than the ``state_name``.

.. centered:: **Syntax**

::

  refined_depends_aspect ::= Refined_Depends => dependency_relation



.. centered:: **Legality Rules**

#. A ``refined_dependency_aspect`` may only appear on the body or body
   stub of a subprogram P in a package whose ``visible_part`` contains
   the declaration of a subprogram P.
#. A ``refined_dependency_aspect`` on the body or body stub of a
   subprogram P may only mention a formal parameter of P,
   ``constituents`` of a ``state_name`` of the enclosing package given
   in the ``dependency_aspect`` in the declaration of P, a *global*
   item that is not a ``state_name`` of the enclosing package or a
   ``constituent`` of a **null** ``abstract_state_name``.

.. centered:: **Static Semantics**

#. A ``refined_dependency_aspect`` of a subprogram defines a *refinement*
   of the ``dependency_aspect`` of the subprogram.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. If the subprogram declaration declared in the visible part of
   package Q has a ``dependency_aspect`` D then the
   ``refined_dependency_aspect`` defines a *refinement* D' of D
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
       
   * function may have a ``refined_dependency_aspect`` D' which
     mentions a ``constituent`` of a **null** ``abstract_name`` but
     the constituent must appear as both an ``import`` and an
     ``export`` in D'.
   * A ``constituent`` of a **null** ``abstract_state_name`` is
     ignored in showing conformance between the ``dependency-aspect``
     and the ``refined_de according to
   the rules given for a ``dependency_aspect``.

#. If a subprogram has a ``refined_dependency_aspect`` which satisfies
   the flow analysis rules, it is used in the analysis of the
   subprogram body rather than its ``dependency_aspect``.
   
* If the declaration of a subprogram P in the visible part of package
  Q has a ``dependency_aspect`` which mentions a ``state_name`` of Q,
  but P does not have a ``refined_dependency_aspect`` then an implicit
  ``refined_dependency_aspect`` will be synthesized from the body of P.`

* if the declaration of a subprogram P declared in the visible part of
  a pakage Q does not have a ``dependency_aspect``, an implicit one is
  synthesized from the ``refined_dependency_aspect`` and the
  ``refined_state_aspect`` (both of which which may also have been
  synthesized).

.. centered:: **Dynamic Semantics**

Abstractions do not have dynamic semantics.

Refined Precondition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^

A subprogram declared in the visible part of a package may have a
``refined_precondition`` applied to its body or body stub.  The
``refined_precondition`` may be used to restate a precondition given on
the declaration of a subprogram in terms the full view of a private
type or the ``constituents`` of a refined ``state_name``.


.. centered:: **Syntax**

``refined_precondition_aspect ::= Refined_Pre =>`` *Boolean_*\ ``expression``

.. centered:: **Legality Rules**

#. A ``refined_precondition`` may only appear on the body or body stub
   of a subprogram P in a package whose ``visible_part`` contains the
   declaration of P.
#. The same legality rules apply to a ``refined_precondition`` as for
   a precondition.

.. centered:: **Static Semantics**

#. A ``refined_precondition`` of a subprogram defines a *refinement*
   of the precondition of the subprogram.
#. Logically, the precondition of a subprogram must imply its
   ``refined_precondition`` which in turn means that this relation
   cannot be achieved with a default precondition (True) and therefore
   a subprogram with a ``refined_precondition`` will require a
   precondition also in order to perform proofs.
#. The static semantics are otherwise as for a precondition.


.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

#. The precondition of a subprogram declaration shall imply the the
   ``refined_precondition``

.. centered:: **Dynamic Semantics**

#. When a subprogram with a ``refined_precondition`` is called; first
   the precondition is evaluated as defined in the Ada LRM.  If the
   precondition evaluates to True, then the ``refined_precondition``
   is evaluated.  If either precondition or ``refined_precondition``
   do not evaluate to True an exception is raised.

Refined Postcondition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^


A subprogram declared in the visible part of a package may have a
``refined_postcondition`` applied to its body or body stub.  The
``refined_postcondition`` may be used to restate a postcondition given
on the declaration of a subprogram in terms the full view of a private
type or the ``constituents`` of a refined ``state_name``.


.. centered:: **Syntax**

``refined_postcondition_aspect ::= Refined_Post =>`` *Boolean_*\
``expression``

.. centered:: **Legality Rules**

#. A ``refined_postcondition`` may only appear on the body or body stub
   of a subprogram P in a package whose ``visible_part`` contains the
   declaration of P.
#. The same legality rules apply to a ``refined_postcondition`` as for
   a postcondition.

.. centered:: **Static Semantics**

#. A ``refined_postcondition`` of a subprogram defines a *refinement*
   of the postcondition of the subprogram.
#. Logically, the ``refined_postcondition`` of a subprogram must imply
   its postcondition.  This means that it is perfectly logical for the
   declaration not to have a postcondition (which in its absence
   defaults to True) but for the body or body stub to have a
   ``refined_postcondition``.
#. The static semantics are otherwise as for a postcondition.


.. centered:: **Verification Rules**

.. centered:: *Checked by Proof*

#. The precondition of a subprogram declaration with the
   ``refined_precondition`` of its body or body stub and its
   ``refined_postcondition`` together imply the postcondition of the
   declaration, that is:

   ::
     precondition and refined_precondition and refined_postcondition => postcondition


.. centered:: **Dynamic Semantics**

#. When a subprogram with a ``refined_postcondition`` is called; first
   the subprogram is evaluated.  If it terminates without exception
   the ``refined_postcondition`` is evaluated.  If this evaluates to
   True then the postcondition is evaluated as described in the Ada
   LRM.  If either the ``refined_postcondition`` or the postcondition
   do not evaluate to True an exception is raised.

.. todo:: Class wide pre and post conditions.

.. todo:: package dependencies: circularities, private/public child
     packages and their relationship with their parent especially in
     regard to data abstraction.

.. todo:: Restrictions related to package interactions.

.. todo:: refined contract_cases


Private Types and Private Extensions
------------------------------------

.. centered:: **Extended Static Semantics**

#. The partial view of a private type or private extension may be in
   |SPARK| even if its full view is not in |SPARK|. The usual rule
   applies here, so a private type without discriminants is in
   |SPARK|, while a private type with discriminants is in |SPARK| only
   if its discriminants are in |SPARK|.

Private Operations
^^^^^^^^^^^^^^^^^^


Type Invariants
^^^^^^^^^^^^^^^

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
