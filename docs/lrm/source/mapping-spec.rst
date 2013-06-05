.. _mapping-spec-label:

SPARK 2005 to |SPARK| Mapping Specification
===========================================

This appendix defines the mapping between SPARK 2005 and |SPARK|.
It is intended as both a completeness check for the |SPARK| language
design, and as a guide for projects upgrading from SPARK 2005 to |SPARK|.

Subprogram patterns
-------------------

.. _ms-global_derives-label:

Global and Derives
~~~~~~~~~~~~~~~~~~

This example demonstrates how global variables can be accessed through
procedures/functions and presents how the SPARK 2005 `derives` annotation maps
over to `depends` in |SPARK|. The example consists of one procedure (`Swap`) and
one function (`Add`). `Swap` accesses two global variables and swaps their contents
while `Add` returns their sum.

Specification in SPARK 2005:

   .. literalinclude:: ../code/global_derives/05/swap_add_05.ads
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/global_derives/14/swap_add_14.ads
      :language: ada
      :linenos:

.. _ms-pre_post_return-label:

Pre/Post/Return contracts
~~~~~~~~~~~~~~~~~~~~~~~~~

This example demonstrates how the `Pre`/`Post`/`Return` contracts are restructured
and how they map from SPARK 2005 to |SPARK|. Procedure `Swap` and function
`Add` perform the same task as in the previous example, but they have been
augmented by post annotations. Two additional functions (`Max` and `Divide`)
and one additional procedure (`Swap_Array_Elements`) have also been included
in this example in order to demonstrate further features. `Max` returns the
maximum of the two globals. `Divide` returns the division of the two globals
after having ensured that the divisor is not equal to zero. The `Swap_Array_Elements`
procedure swaps the contents of two elements of an array. For the same reasons
as in the previous example, the bodies are not included.

Specification in SPARK 2005:

   .. literalinclude:: ../code/pre_post_return/05/swap_add_max_05.ads
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/pre_post_return/14/swap_add_max_14.ads
      :language: ada
      :linenos:

.. _ms-attributes_of_unconstrained_out_parameter_in_precondition-label:

Attributes of unconstrained out parameter in precondition
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following example illustrates the fact that the attributes of an unconstrained
formal array parameter of mode "out" are permitted to appear in a precondition.
The flow analyser also needs to be smart about this, since it knows the X'First and
X'Last are well-defined in the body, even though the content of X is not.

Specification in SPARK 2005:

   .. literalinclude:: ../code/attributes_of_unconstrained_out_parameter_in_precondition/05/p.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/attributes_of_unconstrained_out_parameter_in_precondition/05/p.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/attributes_of_unconstrained_out_parameter_in_precondition/14/p.ads
      :language: ada
      :linenos:

.. todo::
   Depending on the outcome of M423-014, either pragma Annotate or pragma Warning
   will be utilized to accept warnings/errors in |SPARK|.
   To be completed in the Milestone 4 version of this document.

Body in |SPARK|:

   .. literalinclude:: ../code/attributes_of_unconstrained_out_parameter_in_precondition/14/p.adb
      :language: ada
      :linenos:

.. _ms-nesting_refinement-label:

Nesting of subprograms, including more refinement
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This example demonstrates how procedures and functions can be nested within
other procedures and functions. Furthermore, it illustrates how global variables
refinement can be performed.

Specification in SPARK 2005:

   .. literalinclude:: ../code/nesting_refinement/05/nesting_refinement_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/nesting_refinement/05/nesting_refinement_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/nesting_refinement/14/nesting_refinement_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/nesting_refinement/14/nesting_refinement_14.adb
      :language: ada
      :linenos:

Package patterns
----------------

Abstract Data Types (ADTs)
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _ms-adt_visible-label:

Visible type
^^^^^^^^^^^^

The following example adds no mapping information. The SPARK 2005 and |SPARK| versions
of the code are identical. Only the specification of the SPARK 2005 code will be presented.
The reason why this code is being provided is to allow for a comparison between a package that
is purely public and an equivalent one that also has private elements.

Specification in SPARK 2005:

   .. literalinclude:: ../code/adt_visible/05/stacks_05.ads
      :language: ada
      :linenos:

.. _ms-adt_private-label:

Private type
^^^^^^^^^^^^

Similarly to the previous example, this one does not contain any annotations either. Due
to this, the SPARK 2005 and |SPARK| versions are exactly the same. Only the specification of
the 2005 version shall be presented.

Specification in SPARK 2005:

   .. literalinclude:: ../code/adt_private/05/stacks_05.ads
      :language: ada
      :linenos:

.. _ms-adt_private_refinement-label:

Private type with refined pre/post contracts in the body
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example demonstrates how `pre` and `post` conditions, that lie in the specification
of a package, can be refined in the package's body. Contracts that need not be refined, do
not have to be repeated in the body of a package. In this particular example, the body of
the SPARK 2005 might seem to be needlessly repeating contracts. However, this is not true
since the contracts that are being repeated are indirectly being refined through the
refinement of the `Is_Empty` and `Is_Full` functions.

Specification in SPARK 2005:

   .. literalinclude:: ../code/adt_private_refinement/05/stacks_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/adt_private_refinement/05/stacks_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/adt_private_refinement/14/stacks_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/adt_private_refinement/14/stacks_14.adb
      :language: ada
      :linenos:

.. _ms-adt_public_child_non_tagged_parent-label:

Public child extends non-tagged parent ADT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example covers the main differences between a child package
and an arbitrary package, namely:

* The private part of a child package can access the private part of its parent.
* The body of a child package can access the private part of its parent.
* The child does not need a with clause for its parent.

A private type and private constant are declared in the parent. The former is accessed
in the body of the child, while the latter is accessed in the private part of the child.

Specifications of both parent and child in SPARK 2005:

   .. literalinclude:: ../code/adt_public_child_non_tagged_parent/05/pairs_05.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/adt_public_child_non_tagged_parent/05/pairs_05_additional_05.ads
      :language: ada
      :linenos:

Bodies of both parent and child in SPARK 2005:

   .. literalinclude:: ../code/adt_public_child_non_tagged_parent/05/pairs_05.adb
      :language: ada
      :linenos:

   .. literalinclude:: ../code/adt_public_child_non_tagged_parent/05/pairs_05_additional_05.adb
      :language: ada
      :linenos:

Specifications of both parent and child in |SPARK|:

   .. literalinclude:: ../code/adt_public_child_non_tagged_parent/14/pairs_14.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/adt_public_child_non_tagged_parent/14/pairs_14_additional_14.ads
      :language: ada
      :linenos:

Bodies of both parent and child in |SPARK|:

As per SPARK 2005.

.. _ms-adt_tagged_type-label:

Tagged type in root ADT package
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example illustrates the use of a tagged type in an ADT package.

Specification in SPARK 2005:

   .. literalinclude:: ../code/adt_tagged_type/05/stacks_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

N/A

Specification in |SPARK|:

   .. literalinclude:: ../code/adt_tagged_type/14/stacks_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

N/A

.. _ms-adt_tagged_type_extension-label:

Extension of tagged type in child package ADT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example illustrates the extension of a tagged type in a child package.

Specification in SPARK 2005:

   .. literalinclude:: ../code/adt_tagged_type_extension/05/stacks_05_monitored_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/adt_tagged_type_extension/05/stacks_05_monitored_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/adt_tagged_type_extension/14/stacks_14_monitored_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

As per SPARK 2005.

.. _ms-adt_private_public_child_visibility-label:

Private/Public child visibility
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example demonstrates visibility rules that apply between public children,
private children and their parent in SPARK 2005. More specifically, it shows that:

* Private children are able to see their private siblings but not their public siblings.
* Public children are able to see their public siblings but not their private siblings.
* All children have access to their parent but the parent can only access private children.

Applying the SPARK tools on the following files will produce certain errors. This was
intentionally done in order to illustrate both legal and illegal access attempts.

|SPARK| shares Ada2012's visibility rules. No restrictions have been applied
in terms of visibility and thus no |SPARK| code is provided in this section.

Specification of parent in SPARK 2005:

   .. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05.ads
      :language: ada
      :linenos:

Specification of private child A in SPARK 2005:

   .. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05_private_child_a_05.ads
      :language: ada
      :linenos:

Specification of private child B in SPARK 2005:

   .. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05_private_child_b_05.ads
      :language: ada
      :linenos:

Specification of public child A in SPARK 2005:

   .. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05_public_child_a_05.ads
      :language: ada
      :linenos:

Specification of public child B in SPARK 2005:

   .. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05_public_child_b_05.ads
      :language: ada
      :linenos:

Body of parent in SPARK 2005:

   .. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05.adb
      :language: ada
      :linenos:

Body of public child A in SPARK 2005:

   .. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05_public_child_a_05.adb
      :language: ada
      :linenos:

Abstract State Machines (ASMs)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Visible, concrete state
^^^^^^^^^^^^^^^^^^^^^^^

.. _ms-asm_visible_concrete_initialized_by_declaration-label:

Initialized by declaration
++++++++++++++++++++++++++

The example that follows presents a way of initializing a concrete state (a state that
cannot be refined) at the point of the declaration of the variables that compose it.
This can only be done in SPARK 2005. In |SPARK| state abstractions cannot share names
with variables and concequently cannot be implicitly refined.

Specification in SPARK 2005:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_declaration/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_declaration/05/stack_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_declaration/14/stack_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_declaration/14/stack_14.adb
      :language: ada
      :linenos:

.. _ms-asm_visible_concrete_initialized_by_elaboration-label:

Initialized by elaboration
++++++++++++++++++++++++++

The following example presents how a package's concrete state can be initialized at
the statements section of the body. The specifications of both SPARK 2005 and |SPARK|
are not presented since they are identical to the specifications of the previous example.

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_elaboration/05/stack_05.adb
      :language: ada
      :linenos:

Body in |SPARK|:

As per SPARK 2005.

.. _ms-asm_private_concrete-label:

Private, concrete state
^^^^^^^^^^^^^^^^^^^^^^^

The following example demonstrates how variables, that need to be hidden from the users
of a package, can be placed on the package's private section. The SPARK 2005 body has
not been included since it does not contain any annotations.

Specification in SPARK 2005:

   .. literalinclude:: ../code/asm_private_concrete/05/stack_05.ads
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/asm_private_concrete/14/stack_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/asm_private_concrete/14/stack_14.adb
      :language: ada
      :linenos:

Private, abstract state, refining onto concrete states in body
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. _ms-asm_private_abstract_bodyref_procedureinit-label:

Initialized by procedure call
+++++++++++++++++++++++++++++

In this example, the abstract state declared at the specification is refined at the body.
Procedure `Init` can be invoked by users of the package, in order to initialize the state.

Specification in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_procedureinit/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_procedureinit/05/stack_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_procedureinit/14/stack_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_procedureinit/14/stack_14.adb
      :language: ada
      :linenos:

.. _ms-asm_private_abstract_bodyref_elaborationinit-label:

Initialized by elaboration of declaration
+++++++++++++++++++++++++++++++++++++++++

The example that follows introduces an abstract state at the specification and refines it
at the body. The constituents of the abstract state are initialized at declaration.

Specification in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_elaborationinit/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_elaborationinit/05/stack_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_elaborationinit/14/stack_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_elaborationinit/14/stack_14.adb
      :language: ada
      :linenos:

.. _ms-asm_private_abstract_bodyref_statementinit-label:

Initialized by package body statements
++++++++++++++++++++++++++++++++++++++

This example introduces an abstract state at the specification and refines it at the body.
The constituents of the abstract state are initialized at the statements part of the body.
The specifications of the SPARK 2005 and |SPARK| versions of the code are as in the previous
example and have thus not been included.

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_statementinit/05/stack_05.adb
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_statementinit/14/stack_14.adb
      :language: ada
      :linenos:

.. _ms-asm_private_abstract_bodyref_mixedinit-label:

Initialized by mixture of declaration and statements
++++++++++++++++++++++++++++++++++++++++++++++++++++

This example introduces an abstract state at the specification and refines it at the body.
Some of the constituents of the abstract state are initialized during their declaration and
the rest at the statements part of the body.

Specification in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_mixedinit/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_mixedinit/05/stack_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_mixedinit/14/stack_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_mixedinit/14/stack_14.adb
      :language: ada
      :linenos:


.. _ms-asm_initial_condition-label:

Initial condition
^^^^^^^^^^^^^^^^^

This example introduces a new |SPARK| feature that did not exist in SPARK 2005.
On top of declaring an abstract state and promising to initialize it, we also illustrate
certain conditions that will be valid after initialization. The body is not being provided
since it does not add any further insight.

Specification in |SPARK|:

   .. literalinclude:: ../code/asm_initial_condition/14/stack_14.ads
      :language: ada
      :linenos:


.. _ms-asm_abstract_state_refined_in_private_child-label:

Private, abstract state, refining onto concrete state of private child
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example shows a parent package Power that contains a State own
variable. This own variable is refined onto concrete state contained within the
two private children Source_A and Source_B.


Specification of Parent in SPARK 2005:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/05/power_05.ads
      :language: ada
      :linenos:

Body of Parent in SPARK 2005:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/05/power_05.adb
      :language: ada
      :linenos:

Specifications of Private Children in SPARK 2005:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/05/power_05_source_a_05.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/05/power_05_source_b_05.ads
      :language: ada
      :linenos:

Bodies of Private Children in SPARK 2005:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/05/power_05_source_a_05.adb
      :language: ada
      :linenos:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/05/power_05_source_b_05.adb
      :language: ada
      :linenos:

Specification of Parent in |SPARK|:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/14/power_14.ads
      :language: ada
      :linenos:

Body of Parent in |SPARK|:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/14/power_14.adb
      :language: ada
      :linenos:

Specifications of Private Children in |SPARK|:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/14/power_14_source_a_14.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/14/power_14_source_b_14.ads
      :language: ada
      :linenos:

Bodies of Private Children in |SPARK|:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/14/power_14_source_a_14.adb
      :language: ada
      :linenos:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_private_child/14/power_14_source_b_14.adb
      :language: ada
      :linenos:

.. _ms-asm_abstract_state_refined_in_embedded_package-label:

Private, abstract state, refining onto concrete state of embedded package
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example is based around the packages from section `Private, abstract state,
refining onto concrete state of private child`_, with the private child packages
converted into embedded packages.

Specification in SPARK 2005:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/05/power_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/05/power_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/14/power_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/14/power_14.adb
      :language: ada
      :linenos:

.. _ms-asm_abstract_state_refined_in_embedded_and_private_child-label:

Private, abstract state, refining onto mixture of the above
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example is based around the packages from sections `Private, abstract state,
refining onto concrete state of private child`_
and `Private, abstract state, refining onto concrete state of embedded package`_.
Source_A is an embedded package, while Source_B is a private child. In order to
avoid repetition, the code of this example is not being presented.

External Variables
~~~~~~~~~~~~~~~~~~

.. _ms-external_variables_input_output-label:

Basic Input and Output Device Drivers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example shows a main program - Copy - that reads all available data
from a given input port, stores it internally during the reading process in a stack
and then outputs all the data read to an output port. The specification of the
stack package are not being presented since they are identical to previous examples.

Specification of main program in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_output/05/copy_05.adb
      :language: ada
      :linenos:

Specification of input port in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_output/05/input_port_05.ads
      :language: ada
      :linenos:

Body of input port in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_output/05/input_port_05.adb
      :language: ada
      :linenos:

Specification of output port in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_output/05/output_port_05.ads
      :language: ada
      :linenos:

Body of output port in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_output/05/output_port_05.adb
      :language: ada
      :linenos:

Specification of main program in |SPARK|:
   .. literalinclude:: ../code/external_variables_input_output/14/copy_14.adb
      :language: ada
      :linenos:

Specification of input port in |SPARK|:

   .. literalinclude:: ../code/external_variables_input_output/14/input_port_14.ads
      :language: ada
      :linenos:

Specification of output port in |SPARK|:

   .. literalinclude:: ../code/external_variables_input_output/14/output_port_14.ads
      :language: ada
      :linenos:

Body of input port in |SPARK|:

This is as per SPARK 2005, but uses aspects instead of representation clauses and pragmas.

   .. literalinclude:: ../code/external_variables_input_output/14/input_port_14.adb
      :language: ada
      :linenos:

Body of output port in |SPARK|:

This is as per SPARK 2005, but uses aspects instead of representation clauses and pragmas.

   .. literalinclude:: ../code/external_variables_input_output/14/output_port_14.adb
      :language: ada
      :linenos:

.. _ms-external_variables_input_append_tail-label:

Input driver using \'Append and \'Tail contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example uses the Input_Port package from section `Basic Input and Output Device Drivers`_
and adds a contract using the 'Tail attribute. The example also use the Always_Valid attribute
in order to allow proof to succeed (otherwise, there is no guarantee in the proof context
that the value read from the port is of the correct type).

.. todo::
   There will not be an equivalent of \'Append and \'Tail in |SPARK|. However, we will be
   able to achieve the same functionality using generics. To be completed in the Milestone 4
   version of this document.

Specification in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_append_tail/05/input_port_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_append_tail/05/input_port_05.adb
      :language: ada
      :linenos:

.. _ms-external_variables_output_append_tail-label:

Output driver using \'Append and \'Tail contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example uses the Output package from section `Basic Input and Output Device Drivers`_
and adds a contract using the 'Append attribute.

.. todo::
   There will not be an equivalent of \'Append and \'Tail in |SPARK|. However, we will be
   able to achieve the same functionality using generics. To be completed in the Milestone 4
   version of this document.

Specification in SPARK 2005:

   .. literalinclude:: ../code/external_variables_output_append_tail/05/output_port_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/external_variables_output_append_tail/05/output_port_05.adb
      :language: ada
      :linenos:

.. _ms-external_variables_refinement_voting_input_switch-label:

Refinement of external state - voting input switch
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example presents an abstract view of the reading of 3 individual
switches and the voting performed on the values read.

Abstract Switch specification in SPARK 2005:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/05/switch.ads
      :language: ada
      :linenos:

Component Switch specifications in SPARK 2005:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/05/switch-val1.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/05/switch-val2.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/05/switch-val3.ads
      :language: ada
      :linenos:

Switch body in SPARK 2005:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/05/switch.adb
      :language: ada
      :linenos:

Abstract Switch specification in |SPARK|:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/14/switch.ads
      :language: ada
      :linenos:

Component Switch specifications in |SPARK|:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/14/switch-val1.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/14/switch-val2.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/14/switch-val3.ads
      :language: ada
      :linenos:

Switch body in |SPARK|:

   .. literalinclude:: ../code/external_variables_refinement_voting_input_switch/14/switch.adb
      :language: ada
      :linenos:

.. _ms-external_variables_complex_io_device-label:

Complex I/O Device
^^^^^^^^^^^^^^^^^^

The following example illustrates a more complex I/O device: the device is fundamentally
an output device but an acknowledgement has to be read from it. In addition, a local register
stores the last value written to avoid writes that would just re-send the same value.
The own variable is then refined into a normal variable, an input external variable
ad an output external variable.

Specification in SPARK 2005:

   .. literalinclude:: ../code/external_variables_complex_io_device/05/device.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/external_variables_complex_io_device/05/device.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/external_variables_complex_io_device/14/device.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/external_variables_complex_io_device/14/device.adb
      :language: ada
      :linenos:

.. _ms-external_variables_increasing_values_in_input_stream-label:

Increasing values in input stream
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example illustrates an input port from which values are
read. According to its postcondition, procedure Increases checks whether
the first values read from the sequence are in ascending order. This example
shows that postconditions can refer to multiple individual elements of the
input stream.

.. todo::
   There will not be an equivalent of \'Append and \'Tail in |SPARK|. However, we will be
   able to achieve the same functionality using generics. To be completed in the Milestone 4
   version of this document.

Specification in SPARK 2005:

   .. literalinclude:: ../code/external_variables_increasing_values_in_input_stream/05/inc.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/external_variables_increasing_values_in_input_stream/05/inc.adb
      :language: ada
      :linenos:


Package Inheritance
~~~~~~~~~~~~~~~~~~~

.. _ms-contracts_with_remote_state-label:

Contracts with remote state
^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example illustrates indirect access to the state of one package
by another via an intermediary. Raw_Data stores some data, which has preprocessing
performed on it by Processing and on which Calculate performs some further processing
(although the corresponding bodies are not given, Read_Calculated_Value in Calculate
calls through to Read_Processed_Data in Processing, which calls through to Read in Raw_Data).

Specifications in SPARK 2005:

   .. literalinclude:: ../code/contracts_with_remote_state/05/raw_data.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/contracts_with_remote_state/05/processing.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/contracts_with_remote_state/05/calculate.ads
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/contracts_with_remote_state/14/raw_data.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/contracts_with_remote_state/14/processing.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/contracts_with_remote_state/14/calculate.ads
      :language: ada
      :linenos:

.. _ms-package_nested_inside_package-label:

Package nested inside package
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

See section `Private, abstract state, refining onto concrete state of embedded package`_.

.. _ms-package_nested_inside_subprogram-label:

Package nested inside subprogram
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example is a modified version of that given in section
`Refinement of external state - voting input switch`_. It illustrates the
use of a package nested within a subprogram.

Abstract Switch specification in SPARK 2005:

   .. literalinclude:: ../code/package_nested_inside_subprogram/05/switch.ads
      :language: ada
      :linenos:

Component Switch specifications in SPARK 2005:

As in `Refinement of external state - voting input switch`_

Switch body in SPARK 2005:

   .. literalinclude:: ../code/package_nested_inside_subprogram/05/switch.adb
      :language: ada
      :linenos:

Abstract Switch specification in |SPARK|:

   .. literalinclude:: ../code/package_nested_inside_subprogram/14/switch.ads
      :language: ada
      :linenos:

Component Switch specification in |SPARK|:

As in `Refinement of external state - voting input switch`_

Switch body in |SPARK|:

   .. literalinclude:: ../code/package_nested_inside_subprogram/14/switch.adb
      :language: ada
      :linenos:


.. _ms-circular_dependence_and_elaboration_order-label:

Circular dependence and elaboration order
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example demonstrates how the Examiner locates and disallows circular dependence
and elaboration relations.

Specification of package P_05 in SPARK 2005:

   .. literalinclude:: ../code/circular_dependence_and_elaboration_order/05/p_05.ads
      :language: ada
      :linenos:

Specification of package Q_05 in SPARK 2005:

   .. literalinclude:: ../code/circular_dependence_and_elaboration_order/05/q_05.ads
      :language: ada
      :linenos:

Body of package P_05 in SPARK 2005:

   .. literalinclude:: ../code/circular_dependence_and_elaboration_order/05/p_05.adb
      :language: ada
      :linenos:

Body of package Q_05 in SPARK 2005:

   .. literalinclude:: ../code/circular_dependence_and_elaboration_order/05/q_05.adb
      :language: ada
      :linenos:

Specification of package P_14 in |SPARK|:

   .. literalinclude:: ../code/circular_dependence_and_elaboration_order/14/p_14.ads
      :language: ada
      :linenos:

Specification of package Q_14 in |SPARK|:

   .. literalinclude:: ../code/circular_dependence_and_elaboration_order/14/q_14.ads
      :language: ada
      :linenos:

Body of package P_14 in |SPARK|:

   .. literalinclude:: ../code/circular_dependence_and_elaboration_order/14/p_14.adb
      :language: ada
      :linenos:

Body of package Q_14 in |SPARK|:

   .. literalinclude:: ../code/circular_dependence_and_elaboration_order/14/q_14.adb
      :language: ada
      :linenos:

Bodies and Proof
----------------

Assert, Assume, Check contracts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _ms-assert_loop_contract-label:

Assert (in loop) contract
^^^^^^^^^^^^^^^^^^^^^^^^^

The following example demonstrates how the `assert` annotation can be used inside a loop.
At each run of the loop the list of existing hypotheses is cleared and the statements that
are within the `assert` annotation are added as the new hypotheses. The |SPARK| equivalent of
`assert`, while within a loop, is `pragma Loop_Invariant`.

Specification in SPARK 2005:

   .. literalinclude:: ../code/assert_loop_contract/05/assert_loop_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/assert_loop_contract/05/assert_loop_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/assert_loop_contract/14/assert_loop_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/assert_loop_contract/14/assert_loop_14.adb
      :language: ada
      :linenos:


.. _ms-assert_no_loop_contract-label:

Assert (no loop) contract
^^^^^^^^^^^^^^^^^^^^^^^^^

While not in a loop, the SPARK 2005 `assert` annotation maps to `pragma Assert_And_Cut`
in |SPARK|. These statements clear the list of hypotheses and add the statements that
are within them as the new hypotheses.

.. _ms-proof_assume_contract-label:

Assume contract
^^^^^^^^^^^^^^^

The following example illustrates use of an Assume annotation (in this case,
the Assume annotation is effectively being used to implement the Always_Valid
attribute).

Specification for Assume annotation in SPARK 2005:

   .. literalinclude:: ../code/proof_assume_contract/05/input_port.ads
      :language: ada
      :linenos:

Body for Assume annotation in SPARK 2005:

   .. literalinclude:: ../code/proof_assume_contract/05/input_port.adb
      :language: ada
      :linenos:

Specification for Assume annotation in |SPARK|:

   .. literalinclude:: ../code/proof_assume_contract/14/input_port.ads
      :language: ada
      :linenos:

Body for Assume annotation in |SPARK|:

   .. literalinclude:: ../code/proof_assume_contract/14/input_port.adb
      :language: ada
      :linenos:

.. _ms-check_contract-label:

Check contract
^^^^^^^^^^^^^^

The SPARK 2005 `check` annotation is replaced by `pragma assert` in |SPARK|. This
annotation adds a new hypothesis to the list of existing hypotheses. The code is
not presented but can be found under "code\\check_contract".

Assert used to control path explosion
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This example will be added in future, based on the Tutorial 5, Exercise 1 example from
the advanced SPARK course.

Other Contracts and Annotations
-------------------------------

Declare annotation
~~~~~~~~~~~~~~~~~~

.. todo:: The declare annotation SPARK is used to control the generation of proof
   rules for composite objects. It is not clear that this will be required in
   |SPARK|, so this section will be updated or removed in future.
   To be completed in the Milestone 4 version of this document.

Always_Valid assertion
~~~~~~~~~~~~~~~~~~~~~~

See section `Input driver using \'Append and \'Tail contracts`_ for use of an assertion involving
the Always_Valid attribute.

Rule declaration annotation
~~~~~~~~~~~~~~~~~~~~~~~~~~~

See section `Proof types and proof functions`_.

.. _ms-proof_types_and_proof_functions-label:

Proof types and proof functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following example gives pre- and postconditions on operations that act upon
the concrete representation of an abstract own variable. This means that proof functions
and proof types are needed to state those pre- and postconditions. In addition, it gives
an example of the use of a rule declaration annotation - in the body of procedure Initialize -
to introduce a rule related to the components of a constant record value.

.. todo::
   *Note that the* |SPARK| *version of the rule declaration annotation has not yet been
   defined [M520-006] - note that it might not even be needed, though this is to be determined -
   and so there is no equivalent included in the* |SPARK| *code.*
   To be completed in the Milestone 4 version of this document.

Specification in SPARK 2005:

   .. literalinclude:: ../code/other_proof_types_and_functions/05/stack.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/other_proof_types_and_functions/05/stack.adb
      :language: ada
      :linenos:

Specification in |SPARK|

   .. literalinclude:: ../code/other_proof_types_and_functions/14/stack.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/other_proof_types_and_functions/14/stack.adb
      :language: ada
      :linenos:

Main_Program annotation
~~~~~~~~~~~~~~~~~~~~~~~

See the main program annotation used in section `Basic Input and Output Device Drivers`_.

RavenSPARK patterns
~~~~~~~~~~~~~~~~~~~

The Ravenscar profile for tasking is not yet supported in |SPARK|.
Mapping examples will be added here in future.
