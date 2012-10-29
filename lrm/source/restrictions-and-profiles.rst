Restrictions and Profiles
=========================

A list of restrictions by section and their effect:


2.1 Character Set

#. ``No_Wide_Characters``

   This GNAT-defined restriction may be applied to restrict the use of
   Wide and Wide_Wide character and string types in |SPARK|.

6.1 Subprogram Declarations

#. ``No_Default_Subprogram_Parameters``

   Prohibits the use of default subprogram parameters, that is, a
   ``parameter_specification`` cannot have a ``default_expression``.


6.1.4 Mode Refinement

#. ``Moded_Variables_Are_Entire``

   Asserts that a ``moded_item`` cannot be a subcomponent name.

#. ``No_Conditional_Modes``

   Prohibits the use of a ``conditional_mode`` in a
   ``mode_specification``.

#. ``No_Default_Modes_On_Procedures``

   A style restriction that disallows a ``default_mode_specification``
   within a procedure ``mode_refinement``. An explicit ``Input =>``
   must be given.  A function ``mode_refinement`` may have a
   ``default_mode_specification``.


6.1.5 Global Aspects

#. ``Global_Aspects_Required``

   Enforces the use of a ``global_aspect`` on every subprogram which
   accesses a *global* variable.  When this restriction is in force a
   subprogram which does not have an explicit ``global_aspect`` is
   considered to have a have have one of ``Global =>`` **null**.

#. ``Global_Aspects_On_Procedure_Declarations``

   A less stringent restriction which requires a ``global_aspect`` on
   all procedure declarations that access a *global* variable.  A
   ``global_aspect`` is optional on a subprogram body that does not
   have a separate declaration.  An implicit global aspect is calculated
   from the body of each subprogram body which does not have an
   explicit ``global_aspect``.

6.1.6 Param Aspects

#. ``No_Param_Aspects``

   Excludes the use of ``param_aspects``.

6.1.7 Dependency Aspects

#. ``Procedures_Require_Dependency_Aspects``

   Mandates that all procedures must have a ``dependency_aspect``.
   Functions may have a ``dependency_aspect`` but they are not
   required.

#. ``Procedure_Declarations_Require_Dependency_Aspects``

   A less stringent restriction which only requires a
   ``dependency_aspect`` to be applied to a procedure declaration. A
   ``dependency_aspect`` is optional on a subprogram body that does
   not have a separate declaration.  An implicit dependency aspect is
   calculated from the body of each subprogram body which does not
   have an explicit ``dependency_aspect``.

#. ``No_Conditional_Dependencies``

   Prohibits the use of a ``conditional_dependency`` in any
   ``dependency_relation``.

#. ``Dependencies_Are_Entire``

   Prohibits the use of subcomponents in ``dependency_relations``.

6.2 Formal Parameter Modes

#. ``Strict_Modes``

   * A *formal parameter* (see Ada LRM 6.1) of a subprogram of mode
     **in** or **in out** (an ``import``) must be read on at least one
     execution path through the body of the subprogram and its initial
     value used in determining the value of at least one of ``export``
     or the special **null** export symbol.
   * A *formal parameter* of a subprogram of mode **in out** must be
     updated directly or indirectly on at least one executable path
     within the subprogram body.
   * A *formal parameter* of a subprogram of mode **out** must be
     updated directly or indirectly on every executable path through
     the subprogram body.

   This restriction has to be checked by flow analysis.

6.3 Subprogram Bodies

#. ``End_Designators_Required``

   Mandates that the final end of every subprogram body, package
   declaration and package body has a designator which repeats the
   defining designator of the unit.

.. note:: RCC. Is End_Designators_Required really ever going to be used? It was only
   required in S95 to facilitate the implementation of the hide
   anno really. This feels more like a rule for GNATCheck that
   users might choose to emply, but I don't think it makes
   any difference to verifiability, so no business of |SPARK|?

6.3.2 Global Aspects

#. ``No_Scope_Holes``

   A subprogram, P, shall not declare an entity of the same name as a
   ``moded_item`` or the name of the object of which the
   ``moded_item`` is a subcomponent in its ``global_aspect`` within a
   ``loop_statement`` or ``block_statement`` whose nearest enclosing
   program unit is P.

.. note:: RCC. Is No_Scope_Holes really necessary for proof or any other form
   of verification? 

6.4.2 Anti-Aliasing

#. ``Array_Elements_Assumed_To_Overlap``

   Enforces the assumption that array elements are always considered
   to be overlapping and so, for example, V.A(I).P and V.A(J).Q are
   considered as overlapping.  This restriction can be enforced simply
   whereas the more general rule that array subcomponents are only
   considered to be overlapping when they have common indices requires
   formal proof in general.

.. note:: RCC. Strongly agree that we need this for rel1, since it gets
   us back to the simple aliasing rules of S95, without having to resort
   to proof.

7.1 Packages

#. ``End_Designators_Required``

   See the same restriction in section 6.3. 


7.1.2 Abstract State Aspect

#. ``Package_Aspects_Required`` 

   Applies to an entire package including any embedded packages and
   its private child packages and enforces the restriction that a
   package which has hidden state must have an
   ``abstract_state_aspect``.

   If any of the state components of a package, including *variables*
   declared in its visible part are initialized during the elaboration
   of the package, then the initializes state components must appear
   in an ``initializes_aspect``.

#. ``No In_Out Volatile Variables`` 

   Applies to an entire package including any embedded packages and
   its private child packages and enforces the restriction that a
   ``mode_selector`` of In_Out may not appear in an
   ``abstract_state_aspect`` or a ``refined_state_aspect``.

7.1.3 Initializes Aspect
 
#. ``Package_Aspects_Required``

   See the same restriction in section 7.1.2. 

#. ``Package_Elaboration_Initializes_Local_State_Only``

   Applies to an entire package including any embedded packages and
   its private child packages and enforces the restriction that the
   package may only initialize state declared locally to the package
   during its elaboration.  That is, only the *variables* declared
   immediately within the package.

#. ``Package_Elaboration_Initializes_Local_And_Parent_State_Only``

   A package may only initialize a *variable* declared *locally* to
   the package, a visible *variable* of its parent or indirectly a
   ``state_name`` of its parent.

#. ``Package_Elaboration_Order_Independence``

   Enforces the rule the elaboration of a package Q may only
   initialize a *variable* using a *static expression* or using
   subprograms and *variables local* to Q.  Ultimately all the
   initialization values must be derived from *static expressions*.  If
   this restriction is in force then the predicate of an
   ``initial_condition_aspect`` of a package may only refer to state
   initialized by Q.

7.1.4 Initial Condition Aspect
 
#. ``Initialize_Package_Local_State_Only``

   See the same restriction in section 7.1.3. 


#. ``Package_Elaboration_Order_Independence``

   See the same restriction in section 7.1.3. 

7.2.2 Refined State Aspect

#. ``Null_State_Refinement_Prohibited``

   The ``abstract_state_name`` **null** cannot be used in a
   ``state_refinement_aspect``.

#.  ``Strict_Volatile_State_Refinement``

    A ``constituent`` of a Volatile ``abstract_state_name`` must be
    Volatile and be of the same mode.



END OF FILE
