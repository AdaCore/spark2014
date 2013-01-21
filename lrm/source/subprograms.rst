Subprograms
===========

Subprogram Declaration
----------------------

We distinguish the *declaration view* introduced by a ``subprogram_declaration``
from the *implementation view* introduced by a ``subprogram_body`` or an
``expression_function_declaration``. For subprograms that are not declared by
a ``subprogram_declaration``, the ``subprogram_body`` or
``expression_function_declaration`` also introduces a declaration view which
may be in |SPARK| even if the implementation view is not.

Rules are imposed in |SPARK| to ensure that the execution of a function
call does not modify any variables declared outside of the function.
It follows as a consequence of these rules that the evaluation
of any [SPARK] expression is side-effect free.

We also introduce the notion of a *global item*, which is a global variable or
a state abstraction (see :ref:`abstract-state`). Global items are presented
in Global aspects (see :ref:`global-aspect`).

.. centered:: **Extended Legality Rules**

#. A function declaration shall not have a ``parameter_specification``
   with a mode of **out** or **in out**. This rule also applies to
   a subprogram_body for a function for which no explicit specification
   is given.

.. centered:: **Static Semantics**

#. The *final* value of a global item or parameter of a subprogram is its 
   value immediately following the successful call of the subprogram.

#. The *initial* value of a global item or parameter of a subprogram is its 
   value at the call of the subprogram.
   
#. An *output* of a subprogram is a global item or parameter whose final
   value may be updated by a call to the subprogram.  The result of a function
   is also an output.
   
#. An *input* of a subprogram is a global item or parameter whose initial
   value may be used in determining the final value of an output of the 
   subprogram.


.. todo::
   In the future we may be able to permit access and aliased formal parameter specs. Target: rel2+

.. todo::
   What do we do regarding null exclusion parameters? Target: D2

.. todo::
   What do we do regarding function access results and function null exclusion results? Target: D2


Preconditions and Postconditions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As indicated by the ``aspect_specification`` being part of a
``subprogram_declaration``, a subprogram is in |SPARK| only if its specific
contract expressions (introduced by Pre and Post) and class-wide
contract expressions (introduced by Pre'Class and Post'Class), if any,
are in |SPARK|.

.. centered:: **Verification Rules**

#. Verification conditions are generated from the program text to
   demonstrate that the implementation of the body of the subprogram
   satisfies the post condition provided the precondition is True and
   the subprogram completes normally.

.. note:: (TJJ 29/11/12) Do we need this verification rule?  If we do
    it needs to be more precise I think.

.. todo:: Think about Pre'Class and Post'Class. Target: D2.

Subprogram Contracts
~~~~~~~~~~~~~~~~~~~~

|SPARK| provides extra aspects, the Global and Depends
aspects to strengthen a subprogram declaration so that constructive,
modular program analysis may be performed.  With the extra aspects the
body of a subprogram does not have to be implemented in order for
analysis and proof of callers of the subprogram.

A Contract_Cases aspect is also provided which provides a convenient
way of formally specifying the required functionality of a subprogram.


.. centered:: **Legality Rules**

#. The Global, Depends and Contract_Cases aspects may be
   specified for a subprogram with an ``aspect_specification``.  More
   specifically, these aspects are allowed in the same
   contexts as a Pre or Post aspect.

Contract Cases 
~~~~~~~~~~~~~~

The Contract_Cases aspect provides a concise way to specify mutually
independent cases guarded by ``conditions`` using the initial value of
**in** or **in out** formal parameters or global variables.  Each
``contract_case`` specifies the final value of mode **out** or **in
out** formal parameters or global variables.  The final
``contract_case`` may be the keyword **others** which means that, in a
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
      Pre  => General_Precondition
                and then Exactly_One_Of(A1,A2...An),
      Post => General_Postcondition
                and then (if A1'Old then B1)
                and then (if A2'Old then B2)
                and then ...
                and then (if An'Old then Bn);


where

  A1 .. An are Boolean expressions involving the initial values of
  formal parameters and global variables and

  B1 .. Bn are Boolean expressions that may also use the final values of
  formal parameters, global variables and results.

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

#. Each ``condition`` in a Contract_Cases aspect has to proven to
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

.. _global-aspect:

Global Aspect
~~~~~~~~~~~~~

A Global aspect of a subprogram, if present, lists the global items whose values
are used or affected by a call of the subprogram.

The Global aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Global and the ``aspect_definition`` must
follow the grammar of ``global_specification``

.. centered:: **Syntax**

::

   global_specification        ::= (moded_global_list {, moded_global_list})
                                 | global_list
                                 | null
   moded_global_list           ::= mode_selector => global_list
   global_list                 ::= global_item
                                 | (global_item {, global_item})
   mode_selector               ::= Input | Output | In_Out | Contract_In
   global_item                 ::= name

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 6.1.4 Syntax

.. centered:: **Legality Rules**

#. A ``global_item`` of a subprogram shall be a stand alone variable object 
   [that is, it is not part of a larger object] or it shall be a state abstraction.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR global_item shall be stand alone variable or state abstraction

#. Each ``mode_selector`` shall occur at most once in a single
   Global aspect.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR Each mode_selector shall occur at most once in a single Global aspect

#. A function subprogram may not have a ``mode_selector`` of
   ``Output`` or ``In_Out`` in its Global aspect.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR Functions cannot have Output or In_Out as mode_selector

#. ``global_items`` in the same Global aspect shall denote distinct entities.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR global_items shall denote distinct entities

#. A global item occurring in a Global aspect of a subprogram aspect
   specification shall not have the same ``defining_identifier`` as a formal
   parameter of the subprogram.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR A global_item cannot have the same defining_identifier as a formal parameter

#. A global item  of mode **in out** or **out** shall not be a Volatile Input
   state abstraction (see :ref:`abstract-state-aspect`).

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR A global_item of mode in out or out cannot be a Volatile Input state abstraction

#. A global item of mode **in** or **in out** shall not be a Volatile Output
   state abstraction.

   .. ifconfig:: Display_Trace_Units
   
      :Trace Unit: 6.1.4 LR A global_item of mode in out or in cannot be a Volatile Output state abstraction


.. centered:: **Static Semantics**

#. A ``global_specification`` that is a ``global_list`` is considered to be a
   ``moded_global_list`` with the ``mode_selector`` Input.

#. A ``global_item`` is *referenced* by a subprogram if:

   * It is an input or an output of the subprogram, or;

   * It [its initial value] is used to determine the value of an assertion
     expression within the subprogram, or;

   * It [its initial value] is used to determine the value of an assertion
     expression within another subprogram that is called either directly or
     indirectly by this subprogram.

#. A subprogram with a Global aspect that has a ``global_specification``
   of **null** shall not reference any global items.
  
#. A ``global_item`` shall occur in a Global aspect of a subprogram if and
   only if it is referenced by the subprogram.
   
#. Each ``global_item`` in a Global aspect of a subprogram that is an input
   or output of the subprogram shall satisfy the following mode
   specification rules 
   [which are checked during analysis of the subprogram body]:

   * a ``global_item`` that is an input but not an output is mode **in** and 
     has a ``mode_selector`` of Input; 
   
   * a ``global_item`` that is an output but not an input is always fully initialized on
     every call of the subprogram, is mode **out** and has a ``mode_selector`` 
     of Output;
     
   * otherwise the ``global_item`` is both an input and an output, is
     mode **in out** and has a ``mode_selector`` of In_Out.

#. A ``global_item`` that is referenced by a subprogram but is neither an
   input nor an output of that subprogram [that is, it is only used to determine
   the value of an assertion expression] has a ``mode_selector`` of Contract_In.

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Global.

.. centered:: **Verification Rules**

#. A Global aspect is verified against the ``global_specification``
   rules given in the static semantics.

.. centered:: **Examples**

.. code-block:: ada

   with Global => null; -- Indicates that the subprogram does not read or update
                        -- any global items.
   with Global => V;    -- Indicates that V may be read by the subprogram.
   with Global => (X, Y, Z);  -- X, Y and Z may be read by the subprogram.
   with Global => (Input        => V); -- Indicates that V may be read by the subprogram.
   with Global => (Input        => (X, Y, Z)); -- X, Y and Z may be read by the subprogram.
   with Global => (Output       => (A, B, C)); -- A, B and C will be fully initialized
                                               -- by the subprogram.
   with Global => (Input        => (X, Y, Z),
                   Output       => (A, B, C),
                   In_Out       => (P, Q, R),
                   Contract_In  => (T, U));
                  -- A global aspect with all types of global specification

.. _depends_aspect:

Depends Aspects
~~~~~~~~~~~~~~~

A Depends aspect defines a *dependency relation* for a
subprogram which may be given in the ``aspect_specification`` of the
subprogram.  The dependency relation is used in information flow
analysis. Depends aspects are optional and are simple specifications.

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

The functional behaviour of a subprogram is not specified by the Depends
aspect but, unlike a postcondition, the Depends aspect, if it is given, has
to be complete in the sense that every input and output of the subprogram must
appear in the Depends aspect.

The Depends aspect is introduced by an ``aspect_specification`` where
the ``aspect_mark`` is Depends and the ``aspect_definition`` must follow
the grammar of ``dependency_relation`` given below.


.. centered:: **Syntax**

::

   dependency_relation       ::= null
                            | (dependency_clause {, dependency_clause})
   dependency_clause         ::= output_list =>[+] input_list
   output_list            ::= output
                            | (output {, output})
                            | null
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

#. Every ``input`` and ``output`` of a ``dependency_relation`` of a Depends
   aspect of a subprogram is a state abstraction, a whole object (not part of 
   a containing object) or a formal parameter of the subprogram.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. An ``input`` must have a mode of **in** or **in out**
   and an ``output`` must have an mode of **in out** or
   **out**.  [Note: As a consequence an entity which is both an
   ``input`` and an ``output`` shall have a mode of **in out**.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. For the purposes of determining the legality of a Result
   ``attribute_reference``, a ``dependency_relation`` is considered to be
   a postcondition of the function, if any, to which the enclosing
   ``aspect_specification`` applies.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. There can be at most one ``output_list`` which is a **null** symbol
   and if it exists it must be the ``output_list`` of the last
   ``dependency_clause`` in the ``dependency_relation``.  An
   ``input`` which is in an ``input_list`` of a **null** export may
   not appear in another ``input_list`` of the same
   ``dependency_relation``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The object denoted by a given ``output`` in an ``output_list`` shall
   not be denoted by any other ``output`` in that ``output_list``.   

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. The object denoted by a given ``input`` in an ``input_list`` shall
   not be denoted by any other ``input`` in that ``input_list``.     

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

#. Every ``output`` of the subprogram shall appear in exactly one
   ``output_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD
   
#. Every ``input`` of the subprogram shall appear in at least one
   ``input_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: TBD

.. centered:: **Static Semantics**

#. The grammar terms ``input`` and ``output`` have the meaning given to input
   and output given in :ref:`global-aspect`.
   
#. A Depends aspect of a subprogram with a **null** ``dependency_relation``
   indicates that the subprogram has no ``inputs`` or ``outputs``.  
   [From an information flow analysis viewpoint it is a 
   null operation (a no-op).]
   
#. A ``dependency_clause`` has the meaning that the final value of every 
   ``output`` in the ``output_list`` is dependent on the initial value of every 
   ``input`` in the ``input_list``.
   
#. A ``dependency_clause`` with a "+" symbol in the syntax ``output_list`` =>+
   ``input_list`` means that each ``output`` in the ``output_list`` has a
   *self-dependency*, that is, it is dependent on itself. 
   [The text (A, B, C) =>+ Z is shorthand for 
   (A => (A, Z), B => (B, Z), C => (C, Z)).]

#. A ``dependency_clause`` with a **null** ``input_list`` means that the final
   value of each ``output`` in the ``output_list`` does not depend on any
   ``input``, other than itself, if the ``output_list`` =>+ **null**
   self-dependency syntax is used.

#. A an ``output_list`` that is **null** represents a *sink* for each
   ``input`` in the ``input_list``.  The ``inputs`` in the ``input_list`` have
   no discernible effect from an information flow analysis viewpoint.
   [The purpose of a **null** ``output_list`` is to facilitate the abstraction 
   and calling of subprograms whose implementation is not in |SPARK|.]

#. A function which does not have an explicit Depends aspect
   is assumed to have the ``dependency_relation`` 
   that its result is dependent on all of its inputs.  
   [Generally a Depends aspect is not required for functions.]
   
.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with a Depends aspect
as it is used purely for static analysis purposes and is not executed.


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


Proof Functions
~~~~~~~~~~~~~~~

.. todo:: TN LA24-011 is open for someone to propose a strawman design.
   Target: D2.


Formal Parameter Modes
----------------------

No extensions or restrictions.

Subprogram Bodies
-----------------


Conformance Rules
~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Inline Expansion of Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Mode Refinement
~~~~~~~~~~~~~~~

If a subprogram has a mode refinement (in a ``global_aspect`` or a
``refined_global_aspect``) then the
implementation of its body must comply with the refined modes
specified for the ``moded_items``.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. The initial value of a ``moded_item`` (including a *formal
   parameter* if the restriction ``Strict_Modes`` is in force) which
   is of mode which has an effective mode of **in** or **in out** must
   be used in determining the final value of at least one ``export``
   of the subprogram.
#. If a ``moded_item`` (including a *formal parameter* if the
   restriction ``Strict_Modes`` is in force) is of mode **in out** it
   must be updated directly or indirectly on at least one executable
   path through the subprogram body.
#. If a ``moded_item`` (including a *formal parameter* if the
   restriction ``Strict_Modes`` is in force) is of mode **out** then
   it must be updated either directly or indirectly on every
   executable path through the subprogram body.
#. If a ``moded_item``, appears in the ``mode_refinement`` of a
   subprogram with a mode of **in**, then it may only appear as a
   ``moded_item`` of mode **in** in any ``mode_refinement`` nested
   within the subprogram.

.. centered:: *Checked by Proof*

#. If a subcomponent name appears in a ``mode_specification`` with a
   ``mode_selector`` of ``Output`` or ``In_Out`` then just that
   subcomponent is considered to be updated and the other
   subcomponents of the object are preserved (unchanged).  If more
   than one subcomponent of the same object appears in such a
   ``mode_specification`` then all the mentioned subcomponents are
   considered to be updated and remaining subcomponents of the object
   preserved.
#. If a subcomponent name appears in a ``mode_specification`` with a
   ``mode_selector`` of ``Input`` or ``In_Out`` then the initial value
   of just that subcomponent is considered to be read and used in
   determining the final value of at least one ``export``. If more than
   one subcomponent of the same object appears in such a
   ``mode_specification`` then the rule applies to all mentioned
   subcomponents.

.. todo:: Conditional mode specifications which have to be checked by proof. Target: rel2+.

Global Aspects
~~~~~~~~~~~~~~

If a subprogram does not have a separate declaration its body or body
stub may have a ``global_aspect`` in its aspect specification where
the same rules as for a ``global_aspect`` in a subprogram declaration
apply.  When a subprogram has a ``global_aspect`` either in its
declaration or its body or body stub the rules and semantics given
below should be satisfied by the implementation of its body.

If the subprogram has a ``refined_global_aspect`` (see
:ref:`refined-global-aspect`), this has to be checked for consistency
with the ``global_aspect`` and influences the rules for checking the
implementation of its body as described below.

.. centered:: **Legality Rules**

#. A subprogram body or body stub may only have a ``global_aspect`` if
   it does not have a separate declaration.
#. A subprogram, shall not declare, immediately within its body, an
   entity of the same name as a ``moded_item`` or the name of the
   object of which the ``moded_item`` is a subcomponent, appearing in
   the ``global_aspect`` of the subprogram.  If the subprogram has a
   ``refined_global_aspect`` then the rule applies to ``moded_items``
   from both aspects.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. A non-*local variable* of a subprogram which is not a formal
   parameter or listed as a ``moded_item`` in the ``global_aspect``
   shall not be read or updated directly or indirectly within the body
   of the subprogram unless it appears as a ``moded_item`` in
   ``refined_global_aspect`` of the subprogram.
#. If a subprogram does not have a ``global_aspect`` then an implicit
   one is synthesised from implementation of the body (if it exists).


Depends Aspects
~~~~~~~~~~~~~~~

If a subprogram does not have a separate declaration its body or body
stub may have a Depends aspect in its aspect specification
where the same rules as for a Depends aspect in a subprogram
declaration apply.  When a subprogram has a Depends aspect
either in its declaration or its body or body stub the rules and
semantics given below should be satisfied by the implementation of its
body.

If the subprogram has a Refined_Depends aspect (see
:ref:`refined-depends-aspect`), this has to be checked for consistency
with the Depends aspect and influences the rules for checking the
implementation of its body as described below.


.. centered:: **Legality Rules**

#. A subprogram body or body stub may only have a
   Depends aspect if it does not have a separate declaration.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. A dependency relation D' is synthesised from the body of a
   subprogram P (if it exists). if P has a Depends aspect and:

   * has a Refined_Depends aspect then D' is compared with the
     Refined_Depends aspect any differences reported; or
   * has a Depends aspect but not a
     Refined_Depends aspect when one is required due to state
     refinement, then D' is taken to be the
     Refined_Depends aspect.  Using the
     ``refined_state_aspect`` the consistency between D' and the
     Depends aspect of P is checked and any inconsistencies,
     reported using the rules given in
     :ref:`refined-depends-aspect` ; or
   * has a Depends aspect and does not require a
     Refined_Depends aspect, then D' is compared directly with
     the Depends aspect of P and any differences reported; or
   * does not have a Depends aspect an implicit
     Depends aspect is synthesised from D'.

#. A function that does not have an explicit Depends aspect is
   assumed to have a dependency relation that its result is dependent
   on all of its imports and this dependency relation is compared with
   the implicit one determined from the body of the function.


.. centered:: *Checked by Proof*

.. todo:: conditional dependencies and subcomponents. Target: rel2+.


Subprogram Calls
----------------

A call is in |SPARK| only if it resolves statically to a subprogram whose
declaration view is in |SPARK| (whether the call is dispatching or not).

Parameter Associations
~~~~~~~~~~~~~~~~~~~~~~



Abstract and Refined Views
^^^^^^^^^^^^^^^^^^^^^^^^^^

There are two possible views of a subprogram P declared in the visible
part of a package.  An abstract view and a refined view.  The abstract
view is that seen by the client of the package.  The refined view is
seen within the body of the package and its private descendants.


Global Aspects
^^^^^^^^^^^^^^

Every subprogram is considered to have a ``global_aspect`` whether it
is explicit or synthesized and implicit.  A subprogram declared in the
visible part of a package may also have a ``refined_global_aspect``,
again this may be explicit or synthesized.  Which of these two aspects
is used depends on where the subprogram is called.  If it is called
from within the package or its private dependents and the subprogram
has a ``refined_global_aspect`` then this is used.  In all other calls
the ``global_aspect`` is used.

Anti-Aliasing
~~~~~~~~~~~~~

An alias is a name which refers to the same object as another name.
The presence of aliasing is inconsistent with the underlying flow
analysis and proof models used by the tools which assume that
different names represent different entities.  In general, it is not
possible or is difficult to deduce that two names refer to the same
object and problems arise when one of the names is used to update the
object.

A common place for aliasing to be introduced is through the *actual
parameters* (see Ada RM 6.4.1) and between *actual parameters* and
*global variables* in a procedure call.  Extra semantic rules are
given that avoid the possibility of aliasing through *actual
parameters* and *global variables*.  A function is not allowed to have
side-effects and cannot update an *actual parameter* or *global
variable*.  Therefore, function calls cannot introduce aliasing and
are excluded from the anti-aliasing rules given below for procedure
calls.

.. todo:: Relax rules for aliasing based on the following paragraph.
   RCC comment: I am happy that these rules are OK given the definition
   of "overlapping" below. Assign to SB, TJJ and/or YM
   to agree this is all OK. Target: D2.

In |SPARK|, it is not allowed in a call to pass as parameters references to
overlapping locations, when at least one of the parameters is of mode ``out``
or ``in out``, unless the other parameter is of mode ``in`` and
by-copy. Likewise, it is not allowed in a call to pass as ``out`` or ``in out``
parameter a reference to some location which overlaps with any global parameter
of the subprogram. Finally, it is not allowed in a call to pass as ``in`` or
``in out`` parameter a reference to some location which overlaps with a global
parameter of mode ``out`` or ``in out`` of the subprogram, unless the parameter
is of mode ``in`` and by-copy.

The ``moded_items`` which are *global* to a procedure have to be
determined.  These may be obtained from an explicit ``global_aspect``
or Depends aspect of the procedure, if either or both of these
are present. If neither of these are present then an implicit global
aspect is used which is deduced by analysis of the bodies of the called
subprogram and the subprograms it calls.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow-Analysis*

#. If a procedure declaration does not have a ``global_aspect`` but
   has a Depends aspect, an implicit ``global_aspect`` will be
   computed from the Depends aspect.
#. If a procedure does not have a global or depends
   aspect, an implicit ``global_aspect`` will be computed using whole
   program analysis.
#. In a call to a procedure P:

   #. If P is declared in package Q with an explicit ``global_aspect``
      and the body of P has a ``refined_global_aspect``
      (see :ref:`refined-global-aspect`) then in applying the anti-aliasing rules to
      calls of P within the body of Q the ``refined_global_aspect`` of
      the body or body stub of P should be used.
   #. In all other cases the ``global_aspect`` from declaration or
      body of P, if P does not have a separate declaration, shall be
      used.  The ``global_aspect`` may be implicit.

#. If a *variable* V named in the ``global_aspect`` of a procedure P
   is of mode **out** or **in out**, then neither V nor any of its
   subcomponents can occur as an *actual parameter* of P.
#. If a *variable* V occurs in the ``global_aspect`` of a procedure P,
   then neither V nor any of its subcomponents can occur as an *actual
   parameter* of P where the corresponding *formal parameter* is of
   mode **out** or **in out**.
#. If an *entire variable* V or a subcomponent of V occurs as an
   *actual parameter* in a procedure call statement, and the
   corresponding *formal parameter* is of mode **out** or **in out**,
   then neither V nor an overlapping subcomponent of V can occur as
   another *actual parameter* in that statement. Two components are
   considered to be overlapping if they are elements of the same array
   with the same index, or slices of the same array with common
   indices (these two cases require the use of proof techniques), or
   are the same component of a record (for example V.F and V.F)
   including subcomponents of the component (for example V.F and
   V.F.P).
#. Where one of these rules prohibits the occurrence of a *variable* V
   or any of its subcomponents as an actual parameter, the following
   constructs are also prohibited in this context:

    #. a type conversion whose operand is a prohibited construct;
    #. a qualified expression whose operand is a prohibited construct;
    #. a prohibited construct enclosed in parentheses.

.. centered:: *Checked by Proof*

#. The requirement that no two array elements overlap and that there
   are no overlapping elements between array slices or between array
   slices and individual elements.

.. centered:: **Dynamic Semantics**

The extended static semantics are checked using static analyses, no
extra dynamic checks are required.

Dependency Relations
~~~~~~~~~~~~~~~~~~~~

Every subprogram has a dependency relation, explicitly given in a
Depends aspect, implicitly synthesized from the subprogram code
or conservatively assumed from the *formal parameters* and *global
variables* of the subprogram.  If the subprogram is declared in the
visible part of package it may also have a
Refined_Depends aspect, again explicitly given or synthesised.

The dependency relation of a subprogram is used to determine the effect
of a call to a subprogram in terms of the flows of information through
the subprogram.

#. A subprogram P declared in the visible part of a package, called
   within the body or private descendants of the package and P
   requires a Refined_Depends aspect because of
   state_refinement, the following will be used as the dependency
   relation of P:

   * the ``dependency_relation`` from the explicit
     Refined_Depends aspect if one is present;
   * for a function which does not have an explicit
     Depends aspect, the assumed dependency relation is that
     its result is dependent on all of its imports;
   * for a procedure which does not have an explicit
     Refined_Depends aspect but the subprogram
     has a proper body, the implicit dependency relation synthesized
     from the subprogram code will be used.
   * for a procedure which has neither a Refined_Depends aspect
     nor a proper body the conservative dependency relation that is
     used is that every ``export`` is dependent on every ``import``.

#. A call to a subprogram P from a client of the package containing
   the declaration of P or for a call to a subprogram which does not
   require a Refined_Depends aspect, the following will be used
   as the dependency relation :

   * the ``dependency_relation`` from an explicit Depends aspect if one is present;
   * for a function which does not have an explicit
     Depends aspect, the assumed dependency relation is that
     its result is dependent on all of its imports;
   * for a procedure which does not have an explicit
     Depends aspect but the subprogram has a proper body, the
     implicit dependency relation synthesized from the subprogram code
     will be used.
   * for a procedure which has neither a Depends aspect nor a
     proper body the conservative dependency relation that is used is
     that every ``export`` is dependent on every ``import``.

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

No extensions or restrictions.




