Package Initialized Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~~

Two important properties of a package are the state components that are
initialized during its elaboration and the other state components on which
that initialization depends. This information is required for flow analysis
which is used to demonstrate that every variable in a |SPARK| program is
initialized before use.

The meaning of X is initialized using Y in this context is that the final value
of X on completion of elaboration of this package is at least partly determined
from the value of Y prior to this elaboration. This is written as
X => Y.

If a state component, X,  is initialized without reference to another state
component then X appears as a stand-alone item. **Wording to be improved.**

If given, the Initialized aspect has to be complete in the sense that
it lists all state components initialized during elaboration and all other state
components on which that initialization depends.

The package-level Initialized aspect is introduced by an
``aspect_specification`` where the ``aspect_mark`` is Initialized and the
``aspect_definition`` must follow the grammar of ``initialized_relation``
given below.

.. centered:: **Syntax**

::

   initialized_relation    ::= null
                             | initialized_by_null_list
                             | (initialized_clause {, initialized_clause})
   initialized_clause      ::= initialized_by_null_list
                             | initialized_by_expr
   initialized_by_expr     ::= initialized_list => initializing_list
   initialized_by_null_list::= initialized_list
   initialized_list        ::= elaboration_output
                             | (elaboration_output {, elaboration_output})
   initializing_list       ::= elaboration_input
                             | (elaboration_input {, elaborateion_input})
   elaboration_input       ::= name
   elaboration_output      ::= name


**Need to define what is meant by elaboration input and elaboration output.**

.. centered:: **Legality Rules**

#. Every ``elaboration_input`` and ``elaboration_output`` of an ``initialized_relation`` of an Initialized
   aspect of a package specification is a state abstraction or a whole object (not part
   of a containing object).
#. An Initialized aspect may only appear in the ``aspect_specification`` of a
   package specification.
#. The Initialized aspect must follow the Abstract State aspect if one is present.

#. There can be at most one ``initialized_by_null_list`` within an ``initialized_relation``.

#. A ``state_name`` that is designated as ``Volatile`` must not appear in
   an ``initialized_list`` in an Initialized aspect of a package.

#. Each ``elaboration_output`` in an ``initialized_relation`` shall denote a
   distinct entity.

#. Each ``elaboration_input`` in an ``initialized_relation`` shall denote a
   distinct entity.

#. **Rule to say that elaboration outputs are declared within the package and
   elaboration inputs aren't? Or is this just picked up when we do the checks
   in the body?**

.. centered:: **Static Semantics**

#. An *elaboration output* of a package elaboration is a state abstraction (**or variable?*) such that the
   set of variables represented by the state abstraction is initialized during
   elaboration. **Review comment from Steve applies here. Also, tidy up text wrt elaboration output of an elaboration.**
#. An *elaboration input* of a package elaboration is a state abstraction (**or variable**?) such that the
   initial value of one or more of the set of variables represented by that
   state abstraction may be used to determine the final value of one or more
   members of the set of variables represented by the outputs of the
   package elaboration. **Apply comments applied to previous point.**
#. The set of state abstractions or variables that are initialized during elaboration
   is given by the set of ``elaboration_output`` items appearing in an
   ``initialized_relation``. [A package may
   initialize an item at the point of declaration of the item, in the
   sequence of statements of its body, within an embedded package or a
   private descendent of the package.]
#. The set of state abstractions or variables that are initialized during
   elaboration but whose initial value is not determined by the value of any
   other state abstractions or variables is given by ``initialized_by_null_list``.
#. The ``initialized_by_expr`` component of an ``initialized_relation`` describes for
   each ``elaboration_output`` of the package elaboration a list of every ``elaboration_input``
   on which the initial value of that ``elaboration_output`` depends.
#. A package that does not initialize any state components can be
   explicitly indicated using a **null** ``initialized_relation``. **State components is inconsistent with terminology above.**

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

** Do we not need some detail on refinement in relation to this aspect,
since when we check correctness then we are actually checking it in
terms of the refined state rather than the abstract state referred to
in the aspect. Otherwise, all the detail on refinement has to be hidden
away in terms of the definitions of elaboration input and
elaboration output: see how the 2005 LRM handles this.**

#. If an Initialized aspect is provided on a package declaration
   then flow analysis does not require the package body to proceed
   with the analysis of clients of the package.  Flow analysis will
   check that the body of the package satisfies its
   Initialized aspect when it is analyzed.
#. Only *elaboration inputs* - **Is it OK to use this terminology?** - of a package elaboration shall appear as an ``elaboration_input``
   in its Initialized aspect.
#. Every *elaboration output* - **Is it OK to use this terminology?** - of a package elaboration shall appear as an ``elaboration_output``
   in the Initialized aspect of the package, if one is present.
#. A ``state_name`` designated as Volatile shall only appear in an
   Initialized aspect if the package reads or updates the Volatile
   variables represented by the ``state_name`` during its elaboration
   or the elaboration of its private descendants.
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
Initialized aspect as the rules are checked by static analysis.


.. centered:: **Examples**

.. code-block:: ada

    package Q
    with
       Abstract_State => State,  -- Declaration of abstract state name State
       Initialized    => State   -- Indicates that State will be initialized
    is                           -- during the elaboration of Q
				 -- or its private descendants.
      ...
    end Q;

    package X
    with
       Abstract_State =>  A,    -- Declares an abstract state name A.
       Initialized    => (A, B) -- A and visible variable B are initialized
                                -- during the elaboration of X or its private descendants.
    is
      ...
      B : Integer;
     --
    end X;

    package Y
    with
       Abstract_State => (A, B, (C with Volatile, Input)),
       Initialized    => A
    is                          -- Three abstract state names are declared A, B & C.
                                -- A is initialized during the elaboration of Y or
				-- its private descendants.
       ...                      -- C is designated as a volatile input and cannot appear
				-- in an Initialized aspect clause
                                -- B is not initialized during the elaboration of Y
                                -- or its private descendants.
    end Y;

    with Q;
    package Y
    with
       Abstract_State => (A, B, (C with Volatile, Input)),
       Initialized    => (A,
                          B => Q.State)
    is                    -- Three abstract state names are declared A, B & C.
                          -- A is initialized during the elaboration of Y or
			  -- its private descendants.
       ...                -- B is initialized during the elaboration of Y or
                          -- its private descendants and is dependent on the
                          -- value of Q.State.
                          -- C is designated as a volatile input and is not
                          -- read during package elaboration and so does not appear
		          -- in the Initialized aspect.
    end Y;

    package Z
    with
       Abstract_State => A,
       Initialized    => null
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

.. centered:: **Comments on Initial Condition Aspect**

#. Do we need to incorporate/point out to the rules from the Ada RM
   that relate to postconditions since this is effectively a postcondition.

#. Verification Rules 1: need to be more precise regarding the definition
   of what it means for a variable to appear in an Initial Condition aspect:
   need to make the definition recursive and cover everything that could appear.

#. Verification Rules 1: would it not be easier to say that every variable
   appearing in the aspect also appears in the Initialized aspect?

#. Verification Rule 2: this is imprecise in terms of the definition of
   "referenced".

#. Verification Rule 3: I assume this means "referenced" via a function call.

#. Verification Rule 3: when you say each referenced ``state_name`` needs to be
   initialized during elaboration, do you mean ``state_names`` that appear
   in the Abstract State spec of this package? What about ``state_names`` - or
   variables for that matter - that are referenced from other packages? I
   assume we need to say they are initialized via an elaboration that happens
   before this one?

.. centered:: **Legality Rules**

#. An Initial Condition Aspect may only be placed in an
   ``aspect_specification`` of a ``package_specification``.
#. The Initial Condition Aspect must follow the
   Abstract State Aspect and Initialized aspect if they are present.

.. centered:: **Static Semantics**

#. The predicate of an Initial Condition Aspect of a package
   defines properties of the initial state of the package after its elaboration and
   the elaboration of its private descendants.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. Each *variable* appearing in an Initial Condition Aspect of a
   package Q which is declared in the visible part of Q must be
   initialized during the elaboration of Q and its private descendants.
#. A ``state_name`` cannot appear directly in
   an Initial Condition Aspect but it may be indirectly referenced
   through a function call. ** This rule needs to be removed since current syntax allows
   definition of parameterless functions. Do we need to retain something on
   not being able to reference the state_name? What we can reference needs to be stated
   somewhere, or we need to say what the Initial_Condition aspect is like in
   terms of an existing syntactic construct. **
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
       Initialized       => State,    -- State will be initialized during elaboration
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
       Initialized       => (A, B) -- A and visible variable B are initialized
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
