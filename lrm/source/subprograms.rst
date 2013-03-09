Subprograms
===========

.. _subprogram-declarations:

Subprogram Declarations
-----------------------

We distinguish the *declaration view* introduced by a ``subprogram_declaration``
from the *implementation view* introduced by a ``subprogram_body`` or an
``expression_function_declaration``. For subprograms that are not declared by
a ``subprogram_declaration``, the ``subprogram_body`` or
``expression_function_declaration`` also introduces a declaration view which
may be in |SPARK| even if the implementation view is not.

Rules are imposed in |SPARK| to ensure that the execution of a function
call does not modify any variables declared outside of the function.
It follows as a consequence of these rules that the evaluation
of any |SPARK| expression is side-effect free.

We also introduce the notion of a *global item*, which is a name that denotes a
global variable or a state abstraction (see :ref:`abstract-state`). 
Global items are presented in Global aspects (see :ref:`global-aspects`).

An *entire object* is an object which is not a subcomponent of a larger 
containing object.  More specifically, an *entire object* is
an object declared by an object_declaration (as opposed to, for example,
a slice or the result object of a function call) or a formal parameter of
a subprogram. An *entire variable* is an an entire object which is a 
variable.

.. centered:: **Static Semantics**

#. The *final* value of a global item or parameter of a subprogram is its 
   value immediately following the successful call of the subprogram.

#. The *initial* value of a global item or parameter of a subprogram is its
   value at the call of the subprogram.

   .. note::
      (SB) Given

         X : Integer := 123;

      , it seems confusing to say that the initial value of X is anything
      other than 123. Perhaps "incoming value" would be better?
   
#. An *output* of a subprogram is a global item or parameter whose final
   value may be updated by a call to the subprogram.  The result of a function
   is also an output.
   
#. An *input* of a subprogram is a global item or parameter whose initial
   value may be used in determining the final value of an output of the 
   subprogram.  
   
   [Static constants do not participate in dataflow analysis; in particular,
   a static constant is not considered to be an input to a subprogram.
   A named nonstatic constant may be an input of a subprogram. A named type or
   subtype whose elaboration evaluates one or more nonstatic expressions
   (thereby, in effect, declaring one or more anonymous constants) may
   be an input of subprogram if one or more of those anonymous constants
   may be used in determining the final value of an output of the
   subprogram. The name of the type or subtype acts, in effect, as a name
   for those anonymous constants. In the case of an anonymous subtype,
   this principle is repeated and the name of the enclosing named entity
   takes on this role (in addition, in the case of a named object
   declaration, to its normal role as the name of the declared object).]

   As a special case, a global item or parameter is also considered an input if
   it is deemed to have no observable effect on any output of the subprogram but 
   is only used in determining a **null** value.  Such a **null** value can only 
   be specified using a an explicit ``null_dependency_clause`` in the Depends 
   aspect of the subprogram (see :ref:`depends-aspects`).

.. centered:: **Verification Rules**

#. A function declaration shall not have a ``parameter_specification``
   with a mode of **out** or **in out**. This rule also applies to
   a subprogram_body for a function for which no explicit declaration
   is given.


   
.. todo::
   In the future we may be able to permit access and aliased formal parameter specs. Target: Release
   2 of |SPARK| language and toolset or later.

.. todo::
   What do we do regarding null exclusion parameters?
   To be completed in the Milestone 3 version of this document.

.. todo::
   What do we do regarding function access results and function null exclusion results?
   To be completed in the Milestone 3 version of this document.


Preconditions and Postconditions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As indicated by the ``aspect_specification`` being part of a
``subprogram_declaration``, a subprogram is in |SPARK| only if its specific
contract expressions (introduced by Pre and Post) and class-wide
contract expressions (introduced by Pre'Class and Post'Class), if any,
are in |SPARK|.

.. todo:: Think about Pre'Class and Post'Class.
          To be completed in the Milestone 3 version of this document.

Subprogram Contracts
~~~~~~~~~~~~~~~~~~~~

In order to extend Ada's support for specification of subprogram contracts
(e.g., the Pre, Post, Pre'Class and Post'Class aspects) by providing more
precise and/or concise contracts, the |SPARK| aspects, Global, Depends,
and Contract_Cases are defined.

.. centered:: **Legality Rules**

#. The Global, Depends and Contract_Cases aspects may be
   specified for a subprogram with an ``aspect_specification``.  More
   specifically, these aspects are allowed in the same
   contexts as a Pre or Post aspect.

See section :ref:`contract-cases` for further detail on Contract_Case aspects, section
:ref:`global-aspects` for further detail on Global aspects and section :ref:`depends-aspects`
for further detail on Depends aspects.

.. _contract-cases:

Contract Cases 
~~~~~~~~~~~~~~

High-Level Requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** It shall be possible to specify pre- and post-conditions
     in a concise way in the case that subprogram behaviour is specified in
     terms of what behaviour should be in each of a series of mutually-independent cases.

     **Rationale:** To provide a more structured way of specifying subprogram behaviour.

#. Constraints, Consistency, Semantics, General requirements:

    * Not applicable


Language Definition
^^^^^^^^^^^^^^^^^^^

The Contract_Cases aspect provides a structured way of defining a
subprogram contract using mutually exclusive subcontract cases.
The final case in the Contract_Case aspect may be the keyword **others** which means that, in a
specific call to the subprogram, if all the ``conditions`` are False
this ``contract_case`` is taken.  If an **others** ``contract_case``
is not specified, then in a specific call of the subprogram exactly
one of the guarding ``conditions`` should be True

A Contract_Cases aspect may be used in conjunction with the
language-defined aspects Pre and Post in which case the precondition
specified by the Pre aspect is augmented with a check that exactly one
of the ``conditions`` of the ``contract_case_list`` is satisfied and
the postcondition specified by the Post aspect is conjoined with
conditional expressions representing each of the ``contract_cases``.
For example:

.. code-block:: ada

 procedure P (...) with
      Pre  => General_Precondition,
      Post => General_Postcondition,
      Contract_Cases => (A1 => B1,
                         A2 => B2,
                         ...
                         An => Bn);

is short hand for

.. code-block:: ada

 procedure P (...) with
      Pre  => General_Precondition,
      Post => General_Postcondition
                and then Exactly_One_Of(A1,A2...An)
                and then (if A1'Old then B1)
                and then (if A2'Old then B2)
                and then ...
                and then (if An'Old then Bn);


where

  A1 .. An are Boolean expressions involving the initial values of
  formal parameters and global variables and

  B1 .. Bn are Boolean expressions that may also use the final values of
  formal parameters, global variables and results.

  ``Exactly_One_Of(A1,A2...An)`` evaluates to True if exactly one of its inputs evaluates
  to True and all other of its inputs evaluate to False.

The Contract_Cases aspect is specified with an ``aspect_specification`` where
the ``aspect_mark`` is Contract_Cases and the ``aspect_definition`` must follow
the grammar of ``contract_case_list`` given below.


.. centered:: **Syntax**

::

   contract_case_list  ::= (contract_case {, contract_case})
   contract_case       ::= condition => consequence
                         | others => consequence

where

   ``consequence ::=`` *Boolean_*\ ``expression``


.. centered:: **Legality Rules**

#. A Contract_Cases aspect may have at most one **others**
   ``contract_case`` and if it exists it must be the last one in the
   ``contract_case_list``.
#. A ``consequence`` expression is considered to be a postcondition
   expression for purposes of determining the legality of Old or
   Result ``attribute_references``.

.. centered:: **Static Semantics**

#. A Contract_Cases aspect is an assertion (as defined in RM
   11.4.2(1.1/3)); its assertion expressions are as described
   below. Contract_Cases may be specified as an
   ``assertion_aspect_mark`` in an Assertion_Policy pragma.

.. centered:: **Dynamic Semantics**

#. Upon a call of a subprogram or entry which is subject to an enabled
   Contract_Cases aspect, Contract_Cases checks are
   performed as follows:

   * Immediately after the specific precondition expression is
     evaluated and checked (or, if that check is disabled, at the
     point where the check would have been performed if it were
     enabled), all of the ``conditions`` of the ``contract_case_list``
     are evaluated in textual order. A check is performed that exactly
     one (if no **others** ``contract_case`` is provided) or at most
     one (if an **others** ``contract_case`` is provided) of these
     ``conditions`` evaluates to True; Assertions.Assertion_Error is
     raised if this check fails.

   * Immediately after the specific postcondition expression is
     evaluated and checked (or, if that check is disabled, at the
     point where the check would have been performed if it were
     enabled), exactly one of the ``consequences`` is evaluated. The
     ``consequence`` to be evaluated is the one corresponding to the
     one ``condition`` whose evaluation yielded True (if such a
     ``condition`` exists), or to the **others** ``contract_case`` (if
     every ``condition``\ 's evaluation yielded False).  A check
     is performed that the evaluation of the selected ``consequence``
     evaluates to True; Assertions.Assertion_Error is raised if this
     check fails.

.. centered:: **Verification Rules**

#. Each ``condition`` in a Contract_Cases aspect has to be proven to
   be mutually exclusive, that is only one ``condition`` can be
   True with any set of inputs conformant with the formal parameters
   and satisfying the specific precondition.
#. At the point of call a check that a single ``condition`` of the
   Contract_Cases aspect is True has to be proven, or if no
   ``condition`` is True then the Contract_Cases aspect must have an
   **others** ``contract_case``.
#. For every ``contract_case``, when its ``condition`` is True, or the
   **others** ``contract_case`` when none of the conditions are True,
   the implementation of the body of the subprogram must be proven to
   satisfy the ``consequence`` of the ``contract_case``.

.. note:: (TJJ 29/11/12) Do we need this verification rule?  Could it
   be captured as part of the general statement about proof?

.. _global-aspects:

Global Aspects
~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** It shall be possible to specify the list of global data read and updated
     when the subprogram is called. [Note that the data read can include data
     used in proof contexts, including assertions.]

     **Rationale:** to allow provision of at
     least the same functionality as SPARK 2005 and to allow modular analysis.

   * **Requirement:** It shall be possible to specify the mode (input, output or both)
     for each global data item.

     **Rationale:** This matches the presentation of
     formal parameters, and the information is used by both flow analysis and proof.

   * **Requirement:** It shall be possible to identify globals that are used only in proof contexts.
     
     **Rationale:** since the list of global data items constrains the data that can be read
     and updated when the subprogram is called, then the global data list needs to cover
     data items that are read in proof contexts.

#. Constraints:

   * No further Global-specific requirements needed.

#. Consistency:

   * **Requirement:** The mode associated with a formal parameter [of an enclosing subprogram]
     or volatile variable in a global data list
     shall be consistent with the mode associated with it at the point of its declaration.
     
     **Rationale:** this provides an early basic consistency check.

#. Semantics: 

   * **Requirement:** A global data item with an input mode is read on at least one
     executable path.

     **Rationale:** by definition.

   * **Requirement:** A global data item with an output mode is written on at least one
     executable path.
 
     **Rationale:** by definition.

   * **Requirement:** A global data item with an output mode but no input mode is written
     on all executable paths.

     **Rationale:** to ensure that data items with output mode are always initialized
     on completion of a call to the subprogram.

   * **Requirement:** A global data item that is only read in a proof context shall not have
     an input or output mode.

     **Rationale:** the effect of reading data items in a proof context is fundamentally
     different from the reading of data items outside of a proof context, since the
     former does not contribute to information flow relations.

#. General requirements:

    * See also section :ref:`generic_hlrs`.


Language definition
^^^^^^^^^^^^^^^^^^^

A Global aspect of a subprogram lists the global items whose values
are used or affected by a call of the subprogram.

The Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Global and the ``aspect_definition`` must
follow the grammar of ``global_specification``

.. centered:: **Syntax**

::

   global_specification        ::= (moded_global_list {, moded_global_list})
                                 | global_list
                                 | null_global_specification
   moded_global_list           ::= mode_selector => global_list
   global_list                 ::= global_item
                                 | (global_item {, global_item})
   mode_selector               ::= Input | Output | In_Out | Proof_In
   global_item                 ::= name
   
where
 ``null_global_specification`` ::= **null**
 

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 6.1.4 Syntax

.. centered:: **Static Semantics**

[As part of defining which entities are allowed as inputs, outputs,
and state constituents, the term "manifest" is defined as a generalization
of the Ada's notion of staticness.]
A type is said to be *manifest* if the elaboration of its
declaration does not include the evaluation of any non-static scalar
expression and each of its non-manifest component subtypes (if any)
is subject to a per-object constraint and is a subtype of manifest type.
A subtype is said to be *manifest* if its type is manifest, its
constraint, if any, is a static constraint, and no Dynamic_Predicate
aspect specification applies to the subtype. A scalar expression is
said to be *manifest* if it is static. A composite expression is
said to be *manifest* if its evaluation does not include the evaluation
of any non-static scalar expression and it is

- a static expression; or

- a parenthesized manifest expression; or

- a qualified expression or type conversion whose subtype mark
  designates a manifest subtype and whose operand is a manifest
  expression; or

- a name denoting a component of a manifest object; or

- a name denoting a slice of a manifest object having static bounds; or

- an aggregate whose applicable index constraint (if any) is static,
  whose component expressions are all manifest, and
  for which the evaluation of each "<>" component value (if any) fully
  initializes the associated component and does not involve the evaluation
  of any non-manifest expressions; or

- an extension aggregate which meets the above conditions for an aggregate
  and whose ancestor_part is either a manifest expression or a subtype_mark
  denoting a manifest subtype; or

- a conditional expression all of whose dependent expressions are
  manifest (TBD: could relax and only require that the selected
  dependendent expression must be manifest) and whose selected
  dependent expression is known statically (i.e., for a case expression,
  the selecting expression is static; for an if expression, either
  all conditions are static or the first N-1 conditions are statically
  False (for some value of N) and the Nth condition is statically True).

[TBD: given a one-part expression function whose expression
is manifest, should a call to the function be manifest? Since this is
all just for purposes of flow analysis, we could relax things even
further and allow a call to an arbitrary function to be manifest as
long as the function has no global inputs and we only pass in manifest
actuals.]

A constant object declared declared by an object_declaration or
an extended_return_object_declaration is manifest if its subtype
is manifest and its initialization expression is manifest. The result
object for the evaluation of a manifest composite expression is
manifest [; this rule is needed because such an object can be renamed].

.. centered:: **Legality Rules**

#. A ``global_item`` shall denote an entire object, a type, a subtype,
   or a state abstraction.

#. The rule that a ``global_item``
   shall not denote a function or a function call [(which is already
   implied by the preceding rule)] is a name resolution rule.
   [In particular, a ``global_item`` can unambiguously denote a
   state abstraction even if a function having the same fully qualified
   name is also present].

#. A ``global_item`` shall not denote a manifest object, type, or subtype.

#. A ``global_item`` shall not denote a state abstraction whose refinement
   is visible [(a state abstraction cannot be named within its enclosing
   package's body other than in its refinement)].

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR global_item shall denote an entire variable or a state abstraction

#. Each ``mode_selector`` shall occur at most once in a single
   Global aspect.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR Each mode_selector shall occur at most once in a single Global aspect

#. A function subprogram may not have a ``mode_selector`` of
   ``Output`` or ``In_Out`` in its Global aspect.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR Functions cannot have Output or In_Out as mode_selector

#. ``global_items`` in the same Global aspect specification shall denote
   distinct entities.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR global_items shall denote distinct objects or state abstractions.

#. A ``global_item`` occurring in a Global aspect of a subprogram aspect
   specification shall not denote a formal parameter of the subprogram.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR A global_item cannot denote a formal parameter


.. centered:: **Static Semantics**

#. A ``global_specification`` that is a ``global_list`` is considered to be a
   ``moded_global_list`` with the ``mode_selector`` Input.

#. A ``global_item`` is *referenced* by a subprogram if:

   * It is an input or an output of the subprogram, or;

   * Its initial value is used to determine the value of an assertion
     expression within the subprogram, or;

   * Its initial value is used to determine the value of an assertion
     expression within another subprogram that is called either directly or
     indirectly by this subprogram.
     
#. A ``null_global_specification`` indicates that the subprogram does not
   reference any ``global_item`` directly or indirectly.


.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Global aspect.

.. centered:: **Verification Rules**

There are no verification rules associated with a Global aspect of a subprogram
declaration.  The rules given in the Subprogram Bodies section under Global 
aspects are checked when a subprogram body is analyzed.

.. centered:: **Examples**

.. code-block:: ada

   with Global => null; -- Indicates that the subprogram does reference 
                        -- any global items.
   with Global => V;    -- Indicates that V is an input of the subprogram.
   with Global => (X, Y, Z);  -- X, Y and Z are inputs of the subprogram.
   with Global => (Input        => V); -- Indicates that V is an input of the subprogram.
   with Global => (Input        => (X, Y, Z)); -- X, Y and Z are inputs of the subprogram.
   with Global => (Output       => (A, B, C)); -- A, B and C are outputs of
                                               -- the subprogram.
   with Global => (In_Out       => (D, E, F)); -- D, E and F are both inputs and
                                               -- outputs of the subprogram
   with Global => (Proof_In     => (G, H));    -- G and H are only used in 
                                               -- assertion expressions within
                                               -- the subprogram
   with Global => (Input        => (X, Y, Z),   
                   Output       => (A, B, C),
                   In_Out       => (P, Q, R),  
                   Proof_In     => (T, U));                                                    
                   -- A global aspect with all types of global specification
                  

.. _depends-aspects:

Depends Aspects
~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** It shall be possible to specify the dependency relation - that is, which outputs
     are dependent on which inputs - that is met by a given subprogram.

     **Rationale:** To allow provision of at least the same functionality as SPARK 2005
     and to allow modular analysis.

   * **Requirement:** It shall be possible to refer to both global data and formal parameters
     in the dependency relation.

     **Rationale:** The inputs and outputs are given by both the global data and the
     formal parameters.

   * **Requirement:** It shall be possible to assume an implicit dependency relation on functions
     and so an explicit statement shall not be required.

     **Rationale:** this is typical usage and saves effort.

#. Constraints:

   * No further Depends-specific requirements needed.

#. Semantics: 

   * **Requirement:** That (X,Y) is in the dependency relation for a given subprogram
     (i.e. X depends on Y) means that X is an output of the subprogram
     such that the initial value of the input Y is used to set the final value of X on
     at least one executable path.

     **Rationale:** by definition.

#. Consistency:

    * **Requirement:** The dependency relation defines an alternative view of the inputs and outputs
      of the subprogram and that view must be equivalent to the list of global
      data items and formal parameters and their modes (ignoring data items used only in proof contexts).

      **Rationale:** this provides a useful early consistency check.

#. General requirements:

    * See also section :ref:`generic_hlrs`.


Language Definition
^^^^^^^^^^^^^^^^^^^

A Depends aspect defines a *dependency relation* for a
subprogram which may be given in the ``aspect_specification`` of the
subprogram.  The dependency relation is used in information flow
analysis. Depends aspects are simple specifications.

A Depends aspect for a subprogram specifies for each output every input on
which it depends. The meaning of X depends on Y in this context is that the
final value of output, X, on the completion of the subprogram is at least partly
determined from the initial value of input, Y and is written X => Y. As in UML,
the entity at the tail of the arrow depends on the entity at the head of the
arrow.

If an output does not depend on any input this is indicated
using a **null**, e.g., X => **null**.  An output may be
self-dependent but not dependent on any other input.  The shorthand
notation denoting self-dependence is useful here, X =>+ **null**.

The functional behavior of a subprogram is not specified by the Depends
aspect but, unlike a postcondition, the Depends aspect has
to be complete in the sense that every input and output of the subprogram must
appear in the Depends aspect.

The Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Depends and the ``aspect_definition`` must follow
the grammar of ``dependency_relation`` given below.


.. centered:: **Syntax**

::

   dependency_relation    ::= null
                            | (dependency_clause {, dependency_clause})
   dependency_clause      ::= output_list =>[+] input_list
                            | null_dependency_clause
   null_dependency_clause ::= null => input_list
   output_list            ::= output
                            | (output {, output})
   input_list             ::= input
                            | (input {, input})
                            | null
   input                  ::= name
   output                 ::= name | function_result

where

   ``function_result`` is a function Result ``attribute_reference``.

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 6.1.5 Syntax

.. centered:: **Legality Rules**

#. Every ``input`` of a ``dependency_relation`` of a Depends
   aspect shall denote an entire object, a type, a subtype, or a state
   abstraction.

#. An ``input`` of a ``dependency_relation`` of a Depends
   aspect shall not denote a manifest constant, type, or subtype.

#. An ``input`` or ``output`` of a ``dependency_relation`` of a Depends
   aspect shall not denote a state abstraction whose refinement
   is visible [(a state abstraction cannot be named within its enclosing
   package's body other than in its refinement)].

#. Every non-function_result ``output`` of a ``dependency_relation`` of a
   Depends aspect shall denote an entire object or a state abstraction.

#. The rule that an ``input`` or ``output`` of a ``dependency_relation``
   shall not denote a function or a function call [(which is already
   implied by the preceding rules)] is a name resolution rule.
   [In particular, an ``input`` or ``output`` can unambiguously denote a
   state abstraction even if a function having the same fully qualified
   name is also present].

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Must be a state abstraction/whole object or formal parameter

#. An ``input`` must have a mode of **in** or **in out**
   and an ``output`` must have an mode of **in out** or
   **out**.  [Note: As a consequence an entity which is both an
   ``input`` and an ``output`` shall have a mode of **in out**.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR input must be of mode in or in out and output must be of mode out or in out

#. For the purposes of determining the legality of a Result
   ``attribute_reference``, a ``dependency_relation`` is considered to be
   a postcondition of the function to which the enclosing
   ``aspect_specification`` applies.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. There can be at most one ``output_list`` which is a **null** symbol
   and if it exists it must be the ``output_list`` of the last
   ``dependency_clause`` in the ``dependency_relation``.  An
   ``input`` which is in an ``input_list`` of a **null** ``output_list`` may
   not appear in another ``input_list`` of the same
   ``dependency_relation``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR null restrictions in Depends aspect

#. The entity denoted by an ``output`` in an ``output_list`` shall
   not be denoted by any other ``output`` in that ``output_list`` or any other
   ``output_list``.   

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Unique output entities

#. The entity denoted by an ``input`` in an ``input_list`` shall
   not be denoted by any other ``input`` in that ``input_list``.     

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Unique input entities

#. Every ``output`` of the subprogram shall appear in exactly one
   ``output_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Each output appears exactly once
   
#. Every ``input`` of the subprogram shall appear in at least one
   ``input_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 6.1.5 LR Each input shall appear at least once
      
#. A ``null_dependency_clause`` shall not have an ``input_list`` of **null**.

.. centered:: **Static Semantics**

#. The grammar terms ``input`` and ``output`` have the meaning given to input
   and output given in :ref:`subprogram-declarations`.
   
#. A ``dependency_clause`` has the meaning that the final value of every 
   ``output`` in the ``output_list`` is dependent on the initial value of every 
   ``input`` in the ``input_list``.
   
#. A ``dependency_clause`` with a "+" symbol in the syntax ``output_list`` =>+
   ``input_list`` means that each ``output`` in the ``output_list`` has a
   *self-dependency*, that is, it is dependent on itself. 
   [The text (A, B, C) =>+ Z is shorthand for 
   (A => (A, Z), B => (B, Z), C => (C, Z)).]
   
#. A ``dependency_clause`` of the form A =>+ A has the same meaning as A => A.

#. A ``dependency_clause`` with a **null** ``input_list`` means that the final
   value of each ``output`` in the ``output_list`` does not depend on any
   ``input``, other than itself, if the ``output_list`` =>+ **null**
   self-dependency syntax is used.

#. A ``null_dpendency_clause`` represents a *sink* for each
   ``input`` in the ``input_list``.  The ``inputs`` in the ``input_list`` have
   no discernible effect from an information flow analysis viewpoint.
   [The purpose of a ``null_dependency_clause`` is to facilitate the abstraction 
   and calling of subprograms whose implementation is not in |SPARK|.]

#. A Depends aspect of a subprogram with a **null** ``dependency_relation``
   indicates that the subprogram has no ``inputs`` or ``outputs``.  
   [From an information flow analysis viewpoint it is a 
   null operation (a no-op).]
   
#. A function without an explicit Depends aspect specification
   is assumed to have the ``dependency_relation`` 
   that its result is dependent on all of its inputs.  
   [Generally an explicit Depends aspect is not required for functions.]

#. A subprogram which has an explicit Depends aspect specification
   and lacks an explicit Global specification is assumed to have
   the [unique] Global aspect specification that is consistent with the
   subprogram's Depends aspect. [An explicit Global aspect specification
   is not required in this case.]

.. todo::
   Add rules relating to volatile state.
   To be completed in the Milestone 3 version of this document.

.. For purposes of flow analysis, a read of a volatile object is
   always considered to include a self-dependent update
   of the object. [This implies that a ``global_item`` with ``mode_selector``
   Input must not denote a volatile object (this rule is enforced during
   flow analysis). This in turn implies that a function cannot read a
   volatile object declared global to the function. All of this is consistent
   with Ada's rule that a read of a volatile object is an external effect
   (see Ada LRM C.6(20)).]

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Depends aspect
as it is used purely for static analysis purposes and is not executed.

.. centered:: **Verification Rules**

There are no verification rules associated with a Depends aspect of a subprogram
declaration.  The rules given in the Subprogram Bodies section under Depends 
aspects are checked when a subprogram body is a analyzed.

.. todo::
    Consider whether to capture the rules from SPARK 2005 about flow=auto mode in this document
    or whether it is purely a tool issue
    (in SPARK 2005, in flow=auto mode if a subprogram is missing a dependency relation
    then the flow analysis
    assumes all outputs of the subprogram are derived from all of its inputs).

.. centered:: **Examples**

.. code-block:: ada

   procedure P (X, Y, Z in : Integer; Result : out Boolean)
   with Depends => (Result => (X, Y, Z));
   -- The final value of Result depends on the initial values of X, Y and Z

   procedure Q (X, Y, Z in : Integer; A, B, C, D, E : out Integer)
   with Depends => ((A, B) => (X, Y),
                     C     => (X, Z),
                     D     => Y,
                     E     => null);
   -- The final values of A and B depend on the initial values of X and Y.
   -- The final value of C depends on the initial values of X and Z.
   -- The final value of D depends on the initial value of Y.
   -- The final value of E does not depend on any input value.

   procedure R (X, Y, Z : in Integer; A, B, C, D : in out Integer)
   with Depends => ((A, B) =>+ (A, X, Y),
                     C     =>+ Z,
                     D     =>+ null);
   -- The "+" sign attached to the arrow indicates self-dependency, that is
   -- the final value of A depends on the initial value of A as well as the
   -- initial values of X and Y.
   -- Similarly, the final value of B depends on the initial value of B
   -- as well as the initial values of A, X and Y.
   -- The final value of C depends on the initial value of C and Z.
   -- The final value of D depends only on the initial value of D.

   procedure S
   with Global  => (Input  => (X, Y, Z),
                    In_Out => (A, B, C, D)),
        Depends => ((A, B) =>+ (A, X, Y, Z),
                     C     =>+ Y,
                     D     =>+ null);
   -- Here globals are used rather than parameters and global items may appear
   -- in the Depends aspect as well as formal parameters.

   function F (X, Y : Integer) return Integer
   with Global  => G,
        Depends => (F'Result => (G, X),
                    null     => Y);
   -- Depends aspects are only needed for special cases like here where the
   -- parameter Y has no discernible effect on the result of the function.

   
Ghost Functions
~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** It shall be possible to specify functions which are used
     for testing and verification only.  Their presence should have no effect on
     the functionality of program execution which terminates normally 
     (without exception).

     **Rationale:**   In principle such functions could be removed from the
     code (possibly automatically by the compiler) on completion of testing 
     and verification and have no effect on the functionality of the program.

   * **Requirement:** It shall be possible to specify functions which are used
     for formal verification only which have no implementation.

     **Rationale:** A function used for formal verification purposes may be
     difficult (or impossible) to specify or implement in |SPARK|. A function
     without an implementation will be defined, for proof purposes, in an 
     external proof tool.

#. Constraints:

   * In order to be removed they can only be applied in places where it can be
     ascertained that they will not be called during normal execution of the
     program (that is with test and verification constructs disabled).
    
   * A function without an implementation cannot be called during execution of
     a program.

#. Consistency:

   Not applicable.

#. Semantics: 

   Not applicable.

#. General requirements:

    * See also section :ref:`ghost_entities`.


Language definition
^^^^^^^^^^^^^^^^^^^

Ghost entities are intended for use in discharging proof obligations and
in making it easier to express assertions about a program.
The essential property of ghost entities is that they have no
effect on the dynamic behavior of a valid SPARK program. More specifically,
if one were to take a valid SPARK program and remove all
ghost entity declarations from it and all assertions containing
references to those entities, then the resulting program might
no longer be a valid SPARK program (e.g., it might no longer
be possible to discharge all the program's proof obligations)
but its dynamic semantics (when viewed as an Ada program) should
be unaffected by this transformation.

.. note::
   (SB) Now that this section is about ghost entities in general, not
   just ghost functions, should it be moved to elsewhere in the manual?

.. centered:: **Static Semantics**

|SPARK| defines the convention_identifier Ghost.
An entity (e.g., a subprogram or an object) whose Convention aspect
is specified to have the value Ghost is said to be a ghost
entity (e.g., a ghost function or a ghost variable).

The Convention aspect of an entity declared inside of a ghost entity (e.g.,
within the body of a ghost function) is defined to be Ghost.
The Link_Name aspect of an imported ghost entity is defined
to be a name that cannot be resolved in the external environment.

.. centered:: **Legality Rules**

A ghost entity shall only be referenced:

- from within an assertion expression; or
- within or as part of the declaration or completion of a
  ghost entity (e.g., from within the body of a ghost function); or
- within a statement which does not contain (and is not itself) either an
  assignment statement targeting a non-ghost variable or
  a procedure call which passes a non-ghost variable as an
  out or in out mode actual parameter.

Within a ghost procedure, the view of any non-ghost variable is
a constant view. Within a ghost procedure, a volatile non-global
object shall not be read.
TBD: In a ghost procedure we don't want to allow assignments to non-ghosts
either via assignment statements or procedure calls. Is this rule
the best way to accomplish this?

A ghost entity shall not be referenced from
within the expression of a predicate specification of a non-ghost
subtype [because such predicates participate in determining
the outcome of a membership test].

All subcomponents of a ghost object shall be initialized by the
elaboration of the declaration of the object.
TBD: Make worst-case assumptions about private types for this rule,
or blast through privacy?

A ghost instantiation shall not be an instantation of a non-ghost
generic package.
TBD: Just being conservative here until we have more precise rules
about the side effects of elaborating an instance of a generic package.
We need the general rule that the elaboration of a
ghost declaration of any kind cannot modify non-ghost state.

The Link_Name or External_Name aspects of an imported ghost
entity shall not be specified. A Convention aspect specification
for an entity declared inside of a ghost entity shall be confirming
[(in other words, the specified Convention shall be Ghost)].

TBD: disallow a ghost tagged type because just its existence (even if
it is never referenced) changes the behavior of Ada.Tags operations?
Overriding is not a problem because Convention participates in
conformance checks (so ghost can't override non-ghost and vice versa).

TBD: Volatile ghosts seem useless, but do we need to prohibit them?
No reason to mention them one way or the other as far as I can see.

TBD: We are ignoring interactions between ghostliness and freezing.
Adding a ghost variable, for example, could change the freezing point
of a non-ghost type. It appears that this is ok; that is, this does
not violate the ghosts-have-no-effect-on-program-behavior rule.

TBD: Can a ghost variable be a constituent of a non-ghost state
abstraction, or would this somehow allow unwanted dependencies?
If not, then we presumably need to allow ghost state abstractions
or else it would illegal for a library level package body to
declare a ghost variable.

TBD: Do we want an implicit Ghost convention for an entity declared
within a statement whose execution depends on a ghost value?

.. code-block:: ada

  if My_Ghost_Counter > 0 then
    declare
      X : Integer; -- implicitly Ghost?

.. centered:: **Dynamic Semantics**

The effects of specifying a convention of Ghost
on the runtime representation, calling conventions, and other such
dynamic properties of an entity are the same as if a convention of
Ada had been specified.

[If it is intended that a ghost entity should not have any runtime
representation (e.g., if the entity is used only in discharging proof
obligations and is not referenced (directly or indirectly) in any
enabled (e.g., via an Assertion_Policy pragma) assertions),
then the Import aspect of the entity may be specified to be True.]

.. centered:: **Verification Rules**

A non-ghost output shall not depend on a ghost input.
TBD: Is this rule implied by other rules?

A ghost entity shall not be referenced

- within a call to a procedure which has a non-ghost output; or

- within a control flow expression (e.g., the condition of an
  if statement, the selecting expression of a case statement, the
  bounds of a for loop) of a compound statement which contains
  such a procedure call. [The case of an non-ghost-updating
  assignment statement is is handled by a legality rule; this rule is
  needed to prevent a call to a procedure which updates a
  non-ghost via an up-level reference, as opposed to updating a parameter.]

TBD: Is there a better way to express this rule? We want to say that
an update of a non-ghost shall not have a control flow dependency
on a ghost. Can we just say that?

A ghost procedure shall not have a non-ghost output.

   .. centered:: **Examples**

.. code-block:: ada

   function A_Ghost_Expr_Function (Lo, Hi : Natural) return Natural
      is (if Lo > Integer'Last - Hi then Lo else ((Lo + Hi) / 2))
   with
      Pre  => Lo <= Hi,
      Post => A_Ghost_Function'Result in Lo .. Hi,
      Convention => Ghost;

   function A_Ghost_Function (Lo, Hi : Natural) return Natural
   with
      Pre  => Lo <= Hi,
      Post => A_Ghost_Function'Result in Lo .. Hi,
      Convention => Ghost;
   -- The body of the function is declared elsewhere.

   function A_Nonexecutable_Ghost_Function (Lo, Hi : Natural) return Natural
   with
      Pre  => Lo <= Hi,
      Post => A_Ghost_Function'Result in Lo .. Hi,
      Convention => Ghost,
      Import;
   -- The body of the function is not declared elsewhere.


Formal Parameter Modes
----------------------

No extensions or restrictions.

.. todo::
   The modes of a subprogram in Ada are not as strict as S2005 and there
   is a difference in interpretation of the modes as viewed by flow analysis.
   For instance in Ada a formal parameter of mode out of a composite type need
   only be partially updated, but in flow analysis this would have mode in out.
   Similarly an Ada formal parameter may have mode in out but not be an input.
   In flow analysis it would be regarded as an input and give arise to 
   flow errors.
   Perhaps we need an aspect to describe the strict view of a parameter
   if it is different to the specified Ada mode of the formal parameter?
   To be completed in the Milestone 3 version of this document.


Subprogram Bodies
-----------------


Conformance Rules
~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Inline Expansion of Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Global Aspects
~~~~~~~~~~~~~~

THe Global aspect may only be specified for the initial declaration of a
subprogram (which may be either a body or a body stub).
The implementation of a subprogram body must be consistent with the
subprogram's Global Aspect.

Note that a Refined Global aspect may be applied to a subprogram body when using state
abstraction; see section :ref:`refined-global-aspect` for further details.

.. centered:: **Syntax**

No extra syntax is associated with Global aspects on 
subprogram bodies.

.. centered:: **Legality Rules**

No extra legality rules are associated with Global aspects on 
subprogram bodies.

.. centered:: **Static Semantics**

No extra static semantics are associated with Global aspects on 
subprogram bodies.

.. centered:: **Dynamic Semantics**

No extra dynamic semantics are associated with Global aspects on 
subprogram bodies.

.. centered:: **Verification Rules**

#. A``global_item`` shall occur in a Global aspect of a 
   subprogram if and only if it denotes an entity that is referenced by the 
   subprogram.
   
#. Each entity denoted by a ``global_item`` in a Global aspect of a subprogram 
   that is an input or output of the subprogram shall satisfy the following mode
   specification rules 
   [which are checked during analysis of the subprogram body]:

   * a ``global_item`` that denotes an input but not an output is mode **in** 
     and has a ``mode_selector`` of Input; 
   
   * a ``global_item`` that denotes an output but not an input is always fully 
     initialized on every call of the subprogram, is mode **out** and has a 
     ``mode_selector`` of Output;
     
   * otherwise the ``global_item`` denotes both an input and an output, is
     mode **in out** and has a ``mode_selector`` of In_Out.

#. An entity that is denoted by a ``global_item`` which is referenced by a 
   subprogram but is neither an input nor an output but is only referenced
   directly, or indirectly in assertion expressions has a ``mode_selector`` of 
   Proof_In.

.. todo::
    Consider how implicitly generated proof obligations associated with runtime checks
    should be viewed in relation to Proof_In.
    To be addressed in the Milestone 4 version of this document.

Depends Aspects
~~~~~~~~~~~~~~~

If a subprogram does not have a separate declaration then the Depends 
aspect is applied to the declaration of its its body or body stub.
The implementation of a subprogram body must be consistent with its 
Depends Aspect.  

Note that a Refined Depends aspect may be applied to a subprogram body when using state
abstraction; see section :ref:`refined-depends-aspect` for further details.

.. centered:: **Syntax**

No extra syntax is associated with Depends aspects on 
subprogram bodies.

.. centered:: **Legality Rules**

No extra legality rules are associated with Depends aspects on 
subprogram bodies.

.. centered:: **Static Semantics**

No extra static semantics are associated with Depends aspects on 
subprogram bodies.

.. centered:: **Dynamic Semantics**

No extra dynamic semantics are associated with Depends aspects on 
subprogram bodies

.. centered:: **Verification Rules**

#. Each ``output`` given in the Depends aspect must be an ``output`` in
   the implementation of the subprogram body and the ``output`` must depend on 
   all, but only, the ``inputs`` given in the ``input_list`` associated with the 
   ``output``.
   
#. Each ``output`` of the implementation of the subprogram body is present as 
   an output in the Depends aspect.
   
#. Each ``input`` of the Depends aspect is an ``input`` of the implementation of 
   the subprogram body.


Subprogram Calls
----------------

A call is in |SPARK| only if it resolves statically to a subprogram whose
declaration view is in |SPARK| (whether the call is dispatching or not).

Parameter Associations
~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Anti-Aliasing
~~~~~~~~~~~~~

An alias is a name which refers to the same object as another name.
The presence of aliasing is inconsistent with the underlying flow
analysis and proof models used by the tools which assume that
different names represent different entities.  In general, it is not
possible or is difficult to deduce that two names refer to the same
object and problems arise when one of the names is used to update the
object.

A common place for aliasing to be introduced is through the actual
parameters and between actual parameters and
global variables in a procedure call.  Extra verification rules are
given that avoid the possibility of aliasing through actual
parameters and global variables.  A function is not allowed to have
side-effects and cannot update an actual parameter or global
variable.  Therefore, function calls cannot introduce aliasing and
are excluded from the anti-aliasing rules given below for procedure
calls.

High-Level Requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * Not applicable.

#. Constraints:

   * **Requirement:** An entity that may be updated on a call to a subprogram
     may not be referred to by distinct names within that subprogram.

     **Rationale:** Flow analysis specifications are presented and analyzed in
     terms of names rather than the entities to which those names refer.

#. Semantics: 

   * Not applicable.

#. Consistency:

    * Not applicable.

#. General requirements:

    * Not applicable.


Language Definition
^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

No extra syntax is associated with anti-aliasing.

.. centered:: **Legality Rules**

No extra legality rules are associated with anti-aliasing.

.. centered:: **Static Semantics**

No extra static semantics are associated with anti-aliasing.

.. centered:: **Dynamic Semantics**

No extra dynamic semantics are associated with anti-aliasing.

   .. centered:: **Verification Rules**

#. In |SPARK|, a procedure call shall not pass actual parameters 
   which denote objects with overlapping locations, when at least one of 
   the corresponding formal parameters is of mode **out** or **in out**,
   unless the other corresponding formal parameter is of mode **in**
   and is of a by-copy type. 
   
#. In |SPARK|, a procedure call shall not pass an actual parameter, whose
   corresponding formal parameter is mode **out** or **in out**,
   that denotes an object which overlaps with any ``global_item`` referenced 
   by the subprogram.
   
#. In |SPARK|, a procedure call shall not pass an actual parameter which
   denotes an object which overlaps a ``global_item`` of mode 
   **out** or **in out** of the subprogram, unless the corresponding formal
   parameter is of mode **in** and by-copy.

Return Statements
-----------------

No extensions or restrictions.

Overloading of Operators
------------------------

No extensions or restrictions.

Null Procedures
---------------

No extensions or restrictions.


Expression Functions
--------------------

Contract_Cases, Global and Depends aspects may be applied to an expression
function as for any other function declaration if it does not have a separate
declaration.  If it has a separate declaration then the aspects are applied to
that.  It may have refined aspects applied (see :ref:`refinement-rationale`).
