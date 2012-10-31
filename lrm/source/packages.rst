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

The *variables* declared in a package Q, embedded packages declared
within Q, and the private children of Q constitute the state of a
package.  The *variable* declarations are only visible to clients of Q
if they are declared in the ``visible_part`` of Q which is not
considered good practice in general for public (non-private) packages.
The declarations of all other variables are hidden from the user of Q.
Though the variables are hidden they still form part (or all) of the
state of Q and this hidden state cannot be ignored for static analyses
and proof.

|SPARK| extends the concept of state abstraction to provide
hierachical data abstraction whereby the state of a package Q may be
refined over a tree of subordinate embedded packages or private child
packages of Q.  This provides data refinement similar to the
refinement available to types whereby a record may contain fields
which are themselves records.

The other feature supported using state abstraction is a logical model
of volatile *variables*.  A volatile *variable* does not behave like
standard non-volatile *variable* as its value may change between two
successive reads without an intervining update, or successive updates
may occur without any intervining reads and appear to have no effect
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
  abstract_state_list    ::= state_name
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

.. todo Consider whether we need Volatile => In_Out.

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
   ``global_aspect``, a ``dependency_aspect``, their refinded
   counterparts, or their equivalent pragmas.
#. At most one ``category_state`` of Volatile is permitted in an
   ``abstract_state_aspect``.
#. At most one of a Non_Volatile or a default ``category_state`` is
   permitted in an ``abstract_state_aspect``.
#. The only ``mode_selector`` values permitted are Input or Output.

.. centered:: **Static Semantics**

#. An abstract ``state_name`` is declared using a
   ``abstract_state_aspect`` appearing in an ``aspect_specification``
   of a ``package_specification``.
#. A ``state_name`` has the same scope and visibility as a declaration
   in the ``visible part`` of the package to which the
   ``abstract_state_aspect`` is applied.
#. Volatile designates a volatile state, usually representing an
   external input or output.  The mode selector determines whether the
   volatile state is an input or an output.
#. A volatile Input may only oocur where a ``moded_item`` of mode
   **in** is permitted.
#. A volatile Output may only oocur where a ``moded_item`` of mode
   **out** is permitted.
#. A `state_name`` of a package is generally considered to be
   representing hidden state in one of the following categories:
 
   * Non_Volatile Unititalized State - state which is not initialized
     during package elaboration
   * Non_Volatile Initialized State - state which is initialized
     during package elaboration
   * Volatile Input State - Volatile state which is an input only and
     is considered to be implicitly initialized.
   * Volatile Output State - Volatile state which is an output only
     and is considered to be implicitly initialized.

#. The category is specified using the ``category_state`` syntax
   supplimented by the ``initializes_aspect.  A ``category_state``
   without a category defaults to Non_Volatile.
#. A Volatile In or Out ``state_name`` represents a sequence of state
   changes brought about by reading or writing successive values to or
   from a Volatile *variable*.
#. Each time a subprogram is called which has a Volatile Input
   ``state_name`` in its ``global_aspect`` it ultimatly reads a
   Volatile *variable*.  The value of this *variable* may be different
   each time it is read. A normal non-volatile *variable* would have
   the same value unless there was an intervining update of the
   *variable*. This distinction with a normal non-volatile variable or
   state_state name is important for both flow analysis and proof.
#. Each time a subprogram is called which has a Volatile Output
   ``state_name`` in its ``global_aspect`` it ultimatly writes to a
   Volatile *variable*.  This *variable* may be written to many times
   without intervining reads.  This is in contrast with a normal
   non-volatile variable or state where successive updates with no
   intervining reads would indicate that earlier updtaes were
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
      Absatract_State => (A, B, 
                         (Volatile => (Input => C)))
   is                                   -- Three abstract state names are declared A, B & C. 
      ...                               -- C is designated as a volatile input.
   end X; 


Initializes Aspect
^^^^^^^^^^^^^^^^^^

An important property of the state components of a package is whether
they are initialized during package elaboration.  Flow analysis
determines that the program state has been initialized and the
``initializes_aspect`` provides this information without having to
analyse the bodies of packages.

.. centered:: **Syntax**

::

  initializes_aspect    ::= Initializes => initialization_list
  initialization_list   ::= initialized_item_list
                          | (initialization {, initialization})
  initialization        ::= [initializing_package =>] initialized_item_list
  initialized_item_list ::= initialized_item
                          | (initialized_item {, initialized_item})


where

   ``initializing_package ::=`` *package_*\ ``name``

   ``initialized_item     ::= state_name |`` *variable_*\ ``name``


.. centered:: **Legality Rules**

#. An ``initializes_aspect`` may only appear in the
   ``aspect_specification`` of a package specification.
#. The ``initializes_aspect`` must follow the
   ``abstract_state_aspect`` if one is present.
#. An ``initializes_aspect`` of a package has extended visibility; it
   is able to refer to *variables* declared in the visible part of the
   package.
#. An ``initialized_item`` is either:

   * a ``state_name`` declared in a previous ``abstract_state_aspect``
     within the same ``aspect_specification``; or
   * the name of a *variable* declared in the visible part of the
     package specification which contains the ``initializes_aspect``.

#. An ``initializing_package`` may not appear more than once in an
   ``initializes_aspect``
#. There can be at most one ``initialized_item_list`` without an
   associated ``initializing_package``.
#. An ``initialized_item`` may not appear more than once in an
   ``initializes_aspect``.
#. A *variable* appearing in an ``initializes_aspect`` must be entire,
   it cannot be a subcomponent of a containing object.
#. A ``state_name`` which is designated as ``Volatile`` must not
   appear in an initializes aspect.


.. centered:: **Static Semantics**

#. An ``initialized_item`` appearing in an ``initialization``
   indicates that it is initialized during the elaboration of the
   package named by the ``initializing_package`` of the
   ``initialization`` or one of its non-visible subordinate packages.
#. An ``initialized_item_list`` whithout an associated
   ``initializing_package`` defaults to the package containing the
   ``initialization_aspect``.
#. The absence of a ``state_name`` or a *variable* in an
   ``initializes_aspect`` of a package indicates that it is not
   initialized during package elaboration.
#. A ``state_name`` designated as ``Volatile`` is considered to be
   implicitly initialized during package initialization and cannot
   appear in an initialization.
#. If a package has an ``abstract_state_aspect`` but no
   ``initializes_aspect`` it follows that none of its state components
   are initialized during package initialization.

.. centered:: **Restrictions that may be Applied**
.. include:: restrictions-and-profiles.rst
   :start-after: 7.1.3 Initializes Aspect
   :end-before: 7.1.4

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. If a package has an ``initializes_aspect`` and it has non-visible
   state components, it must be preceded by an
   ``abstract_state_aspect`` in the same ``aspect_specification``.
#. Each *variable* or ``state_name`` appearing in an
   ``initialized_item_list`` must be initialized during the
   elaboration of the given ``initializing_package`` or the package
   conntaining the ``initializes_aspect`` if one is not given.
#. If a package has an ``initializes_aspect`` and it does not a
   contain a *variable* or ``state_name`` V, then V shall not be
   initialized during package elaboration.
#. If a package Q has neither an ``abstract_state_aspect`` nor an
   ``initializes_aspect`` but it has state components, then analysis
   of the package specification and body (if it exists) of Q and any
   packages which mention Q within a ``with_clause`` will determine
   the *varibles* declared in the package and whether they are
   initialized during elaboration of the packages.  For *variables*
   not declared in the visible part of the package an implicit
   ``state_name`` is generated to represent the *variables* which are
   not initialized and another for the *variables* which are
   initialized. The ``state_name`` representing the initialized
   *variables* is added to an implicitly generated
   ``initialization_aspect`` along with any *variables* which are
   declared in the visible part of the package wich are initialized
   during the elaboration of the packages.  If the package has
   embedded or private child packages, the same process is applied to
   them and each implicitly declared ``state_name`` arising from this
   analysis becomes a constituent of the appropriate implicitly
   declared ``state_name`` of the parent. The initialized visible
   *variables* and each initialized *state_name* is associated with
   the ``initializing_package`` in the implicit ``initializes_aspect``

.. todo:: I anm not sure we can automatically determine volatile
   variables.  Possibly use the volatile pargma/aspect - how to
   determine whether it is Input or Output. Perhaps assume
   Input if it is designated to be a constant.

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
				 -- or its subordinate non-visible packages.
      ...
    end Q;

    package X
    with 
       Abstract_State =>  A,    -- Declares an abstract state neme A
       Initializes    => (A, B) -- A and visible variable B are initialized
                                -- during package initialization.
    is                           
      ...
      B : Integer;
     -- 
    end X; 

    package Y
    with 
       Abstract_State => (A, B, D,
                          Volatile => (Input => C)),
       Initializes    => (A, Another_Package => D)
    is                          -- Four abstract state names are declared A, B, C & D.
                                -- A is ininialized during the elaboration of Y or
				-- its non-visible subordinate packages.  
       ...                      -- C is designated as a volatile input and cannot appear
				-- in an initializes aspect clause
				-- D is initialized by a different visible package
                                -- B is not initialized during package initialization.
    end Y; 


Initial Condition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^

The ''initial_condition_aspect`` is a predicate that may be used to
describe formally the initial state of a package.  It behaves as a
postcondition for the result of package elaboration.

.. centered:: **Syntax**
  
``initial_condition_aspect ::= Initial_Condition =>`` *Boolean_*\ ``expression``


 .. centered:: **Legality Rules**

#. An ``initial_condition_aspect`` may only be placed in a
   ``aspect_specification`` of a ``package_specification``.
#. The ``initial_condition_aspect`` must follow the
   ``abstract_sate_aspect`` and ``initializes_aspect`` if they are
   present.
#. The expression of an ``initial_condition_aspect`` appearing in a
   package Q has extended visibility.  It may reference declarations
   from the visible part of Q.

.. centered:: **Static Semantics**

#. The *boolean_*\ ``expression`` of an ``initial_condition_aspect``
   of a package is a predicate which defines the state of the package
   after its elaboration.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. Each *variable* appearing in an ``initial_condition_aspect`` of a
   package Q which is declared in the visible part of Q must be
   initialized during package elaboration.
#. A ``state_name`` cannot appear directly in
   an``initial_condition_aspect`` but it may be inditrctly referenced
   through a function call.
#. Each ``state_name`` referenced in ``initial_condition_aspect`` must
   be initialized during package elaboration.

.. centered:: *Checked by Proof*

#. Verification conditions are generated for the declarations of each
   ``initialized_item`` in the ``initial_condition_aspect`` and
   sequence of statements of the body of each ``initializing_package``
   The verification conditions must be proven to show that the
   declarations and statements satisfy the predicate given in the
   ``initial_condition_aspect`` of the package.

.. centered:: **Restrictions that may be Applied**

.. include:: restrictions-and-profiles.rst
   :start-after: 7.1.4 Initial Condition Aspect
   :end-before:  7.2.2 

.. centered:: **Dynamic Semantics**

An ``initial_condition_aspect`` is like a paostcondition.  It should
be evaluated following package elaboration.  if it does not evaluate
to True, then an exception should be raised.
 
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
                                        -- must be decared in the visible part of Y.
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
*variables* declared in the private part, body, embedded packages or
private child packages of Q, which together form the hidden state, of
Q.  In the body of Q each ``state_name`` has to be refined by showing
which *variables* and subordinate abstract states are represented by
the ``state_name`` (its constituents).  A ``refined_state_aspect`` in
the body of Q is used for this purpose.

In the body of a package the constituents of the refined ``state_name``,
the refined view, have to be used rather than the abstract view of the
``state_name``.  Refined global, dependency, pre and post aspects are
provided to express the refined view.

In the refined view the constituents of each ``state_name`` have to be
initialized consistently with their appearance or ommission from the
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
#. If a package specification has an ``abstract_state_aspect`` then
   its body must have a ``refined_state_aspect``.
#. A package body cannot have a ``refined_state_aspect`` if its
   specification does not have an ``abstract_state_aspect``.
#. A ``refined_state_aspect`` of a package body has extended
   visibility; it is able to refer to a *variable*, or a
   ``state_name`` or *variable* declared in the visible part of a
   package, declared immediately within the package body.
#. Each ``state_name`` declared in a package specification must appear
   exactly once as an ``abstract_state_name`` in the
   ``state_refinment_aspect`` of the body of the package.
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

#. A ``refined_state_aspect`` defines the *variables* and subordinate
   ``state_names`` which are the constituents that comprise the
   hidden state represented by the ``state_names`` declared in the
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
   ``state_and_category``; that is each ``constitutent`` must
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
   been desinated as Volatile with a ``mode_selector`` M then at least
   one ``constituent`` of the ``state_name`` must also be designated
   as Volatile with a ``mode_selector`` M in the
   ``refined_state_aspect``.
#. A **null** ``abstract_state_name`` represents a hidden state
   component of a package which has no logical effect on the view of
   the package visible to a user.  An example would be a cache used to
   speed up an operation but does not have an effect on the result of
   the operation.
#. A Non_Volatile``constituent`` of a **null** ``abstract_state_name``
   must be initialized by package elaboration.

.. todo:: Think about whether **null** abstract state can introduce a
   covert channel.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*


#. If a package has internal state but no but no
   ``abstract_state_aspect`` an implicit one is generated from the
   code as described in :ref:`abstract-state-aspect`.  Additionally
   an implicit ``refined_state_aspect`` giving for each implicitly
   defined ``state_name`` a ``constituent_list`` listing each
   ``constituent`` from which it is composed.

.. centered:: **Restrictions that may be Applied**

.. include:: restrictions-and-profiles.rst
   :start-after: 7.2.2 Refined State Aspect
   :end-before:  END OF FILE 

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with state abstraction and refinement.

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
   Perhaps wait for a more general soulution which allows non-pure
   functions in certain situations.

   We need to consider a way of providing features for reasoning about
   external variables different to the broken 'Tail scheme in SPARK95.
   This will require some form of attribute as we cannot mention
   volatile variables directly in a contract.

   If we want to reason about succesive reads (writes) from a Volatile
   Input (Output) ``state_name`` we need to have a way to refer to
   these individual operations.

   At the very least, if V is a Volatile Input variable should not
   have the following assertion provable:  

   T1 := V;
   T2 := V;
   
   pragma Assert (T1 = T2);

Initialization Refinement
^^^^^^^^^^^^^^^^^^^^^^^^^

If a package has an ``initialization_aspect`` which constain a
``state_name`` then each ``constituent`` of the ``state_name`` must be
initialized during package elaboration or be desinated as Volatile, in
which case they are implicitly initialized.  A ``constituent`` of
``state_name`` of a package which does not appear in the
``initializes_aspect`` of the package must not be initialized during
package elaboration.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. Each ``constituent`` of a ``state_name`` declared in a package Q
   that is a *variable* declared immediately within Q must be
   initialized at its point of declaration or within the sequence of
   statements of the body of Q.  
#. Each ``constituent`` of a ``state_name`` declared in a package Q
   that is a *variable* declared in the visible part of a private
   child or embedded package package of Q, must appear in the
   ``initializes_aspect`` of the private child or embedded package.
#. Each ``constituent`` of a ``state_name`` which is a ``state_name``
   of a private child or embedded package must appear in the
   ``initializes_aspect`` of the private child or embedded package.
#. Each ``constituent`` of a **null** ``abstract_state_name`` must be
   initialized implicitly or during package elaboration.

.. _refined-global-aspect:

Refined Global Aspect
^^^^^^^^^^^^^^^^^^^^^

If a subprogram declaration in the visible part of a package names a
``state_name`` of a package in its ``global_aspect`` then the body, or
body stub of the subprogram in the body of the package must have a
``refined_global_aspect`` replacing the ``state_name`` by one or more
of its ``constituents``.

.. centered:: **Syntax**

::

  refined_global_aspect ::= Refined_Global => mode_refinement

.. centered:: **Legality Rules**

#. A ``refined_global_aspect`` may only appear on the body or body stub
   of a subprogram P in a package whose ``visible_part`` contains the
   declaration of P which has a ``global_aspect``.
#. If the ``global_aspect`` of a subprogram declaration P in the
   visible part of a package refers to a ``state_name`` declared in
   the ``abstract_state_aspect`` of the package, then in the body of
   the package the body or body stub of P must have a
   ``refined_global_aspect`` unless the body is an expression function
   when it is optional.
#. A ``refined_global_aspect`` on the body or body stub of a
   subprogram P may only mention ``constituents`` of a ``state_name``
   given in the ``global_aspect`` in the declaration of P, a *global*
   item that is not a ``state_name`` of the enclosing package named in
   the the ``global_aspect`` of P or a ``constituent`` of a **null**
   ``abstract_state_name``.


.. centered:: **Static Semantics**


#. A ``refined_global_aspect`` of a subprogram defines a *refinement*
   of the ``global_aspect`` of the subprogram.
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
       G'must be of mode **in**.
     * if S is a Volatile Output at least one ``constituent`` of S in
       G'must be of mode **out**.

   * A ``constituent`` a **null** ``abstract_name`` may also be
     mentioned in G' provided its mode is **in out**.

   * function may have a ``refined_global_aspect`` G' which mentions a
     ``constituent`` of a **null** ``abstract_name`` but its mode must
     be **in out**.  The **null** ``abstract_state`` does not appear
     in G. The **null** ``abstract_state`` must not affect the value of the
     result of the function it must be purely for optimization.


.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. If a subprogram has a ``refined_global_aspect`` which satisfies the
   legality rules, its ``refined_global_aspect`` is used in the
   analysis of the subprogram body rather than its ``global_aspect``.

.. todo:: Consider subprogram body renaming declarations.

.. _refined-dependency-aspect:

Refined Dependency Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

::

  refined_depends_aspect ::= Refined_Depends => dependency_relation



.. centered:: **Legality Rules**

#. A ``refined_dependency_aspect`` may only appear on the body or body
   stub of a subprogram P in a package whose ``visible_part`` contains
   the declaration of P which has a ``dependency_aspect`` or is the
   declaration of a function which has implicit ``dependency_aspect``.
#. If a ``dependency_aspect`` of a subprogram declaration P in the
   visible part of a package refers to a ``state_name`` declared in
   the ``abstract_state_aspect`` of the package, then in the body of
   the package the body or body stub of P must have a
   ``refined_dependency_aspect``.
#. A ``refined_dependency_aspect`` on the body or body stub of a
   subprogram P may only mention ``constituents`` of a ``state_name``
   given in the ``dependency_aspect`` in the declaration of P, a
   *global* item that is not a ``state_name`` of the enclosing or a
   ``constituent`` of a **null** ``abstract_state_name``.

.. centered:: **Static Semantics**

#. A ``refined_dependency_aspect`` of a subprogram defines a *refinement*
   of the ``dependency_aspect`` of the subprogram.
#. A *refinement* D' of a ``dependecny_aspect`` D declared within package
   Q shall satisfy the following rules:
 
   * For each ``export`` in D which is not a ``state_name`` of Q, 

     * the same item must appear as an ``export`` in D';
     * its ``dependency_list`` will be unchanged except that an
       ``import`` which is a ``state_name`` of Q will be replaced in
       D' by at least one ``constituent`` of the ``state_name`` and a
       ``constituent`` of a **null** , ``abstract_state_name`` may be
       an additional ``import``.

   * for each ``export`` in D which is a ``state_name`` declared in Q,

     * the item is replaced in D' by at least one export which is a
       ``constituent`` of S,
     * its ``dependency_list`` in D' cannot contain an ``import` which is a
       ``state_name`` of Q but may a ``constituent`` of the ``state_name``,
     * the union of every ``import`` from the ``dependency_list`` of
       each ``export`` which is a ``constituent`` of S in D', with
       every ``import`` which is a ``constituent`` of a ``state_name``
       of Q replaced by its ``state_name`` (a ``constituent`` of a
       **null** ``abstract_state_name`` is ignored) should give the
       same set as the set of obtained by the union of every
       ``import`` in the ``dependency_list`` of S in D.
       
   * function may have a ``refined_dependency_aspect`` D' (even if it
     does not have an explicit ``dependency_aspect`` which mentions a
     ``constituent`` of a **null** ``abstract_name`` but the must must
     appear as both an ``import`` and an ``export`` in D'. 
   * A ``constituent`` of a **null** ``abstract_state_name`` is
     ignored in showing conformance between the ``dependency-aspect``
     and the ``refined_dependency_aspect``.


.. centered:: **Dynamic Semantics**

Abstractions do not have dynamic semantics.

Refined Precondition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

``refined_precondition_aspect ::= Refined_Pre =>`` *Boolean_*\ ``expression``

.. centered:: **Static Semantics**

#. A ``refined_precondition`` may only appear on the body of a
   subprogram P in a package whose ``visible_part`` contains the
   declaration of P.
#. The *boolean_*\ ``expression`` of a ``refined_precondition`` of a
   subprogram body may only reference a *variable* if it is a *formal
   parameter* of the subprogram or if the subprogram has:

  #.  a ``refined_global_aspect``, then the *variable* may be a
      *global variable* including a ``constituent`` which is a
      *variable* of the ``refined_global_aspect``;
  #. a ``global_aspect`` but no ``refined_global_aspect``, then the
     *variable* must be a *global variable* of the ``global_aspect``;
     or
  #. no ``global_aspect``, then no *global variables* may be
     referenced in a ``refined-precondition``.

.. centered:: **Proof Semantics**

#. The precondition of a subprogram declaration shall imply the the
   ``refined_precondition``

.. centered:: **Dynamic Semantics**

#. The call of a subprogram with a ``refined_precondition`` needs to
   satisfy the expression (**if** precondition **then**
   ``refined_precondition`` **else** ``false``) otherwise the
   constraint error Assertions.Assertion_Error is raised.  The
   precondition is evaluated in the context of the calling environment
   whereas the ``refined_precondition`` is evaluated in the context of
   the body of the subprogram.

Refined Postcondition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

``refined_postcondition_aspect ::= Refined_Post =>`` *Boolean_*\
``expression``

.. centered:: **Static Semantics**

#. A ``refined_precondition`` may only appear on the body of a
   subprogram.
#. The *boolean_*\ ``expression`` of a ``refined_precondition`` of a
   subprogram body may only reference a *variable* if it is a *formal
   parameter* of the subprogram and if the subprogram has:

  #.  a ``refined_global_aspect``, then the *variable* must be a
      *global variable* including a ``constituent`` which is a
      *variable* of the ``refined_global_aspect``;
  #. a ``global_aspect`` but no ``refined_global_aspect``, then the
     *variable* must be a *global variable* of the ``global_aspect``;
     or
  #. no ``global_aspect``, then no *global variables* may be
     referenced in a ``refined-precondition``.

.. centered:: **Proof Semantics**

#. The precondition and the ``refined_precondition`` and the
   ``refined_postcondition`` of a subprogram declaration shall imply
   the postcondition.

.. centered:: **Dynamic Semantics**

#. The call of a subprogram with a ``refined_postcondition`` needs to
   satisfy the expression (**if** ``refined_postcondition`` **then**
   postcondition **else** ``false``) otherwise the constraint error
   Assertions.Assertion_Error is raised.  The
   ``refined_postcondition`` is evaluated in the context of the body
   of the subprogram whereas the postcondition is evaluated in the
   context of the calling environment.

.. todo:: Class wide pre and post conditions.

.. todo:: package dependencies: circularities, private/public child
     packages and their relationship with their parent especially in
     regard to data abstraction.

.. todo:: Restrictions related to package interactions.


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
