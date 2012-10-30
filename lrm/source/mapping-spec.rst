.. _mapping-spec-label:

SPARK2005 to |SPARK| Mapping Specification
==========================================

This document defines the mapping between SPARK2005 and |SPARK|.
It is intended as both a completeness check for the |SPARK| language
design, and as a guide for projects upgrading from SPARK2005 to |SPARK|.

Subprogram patterns
-------------------

.. _ms-global_derives-label:

Global and Derives
~~~~~~~~~~~~~~~~~~

This example demonstrates how global variables can be accessed through 
procedures and functions and presents how the `derives` annotation is structured. 
The example comprises of one procedure (`Swap`) and one function (`Add`). `Swap` 
accesses two global variables and swaps their contents while `Add` returns their 
sum. The bodies of both SPARK 2005 and |SPARK| are identical and add no further 
insight and will thus not be included.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/global_derives/05/swap_add_05.ads
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/global_derives/14/swap_add_14.ads
      :language: ada
      :linenos:

.. _ms-pre_post_return-label:

Pre/Post/Return contracts
~~~~~~~~~~~~~~~~~~~~~~~~~

This example demonstrates how the `Pre`/`Post`/`Return` contracts are structured 
and how they map from SPARK 2005 to |SPARK|. Procedure `Swap` and function 
`Add` perform the same task as in the previous example, but they have been 
augmented by post annotations. Two additional functions (`Max` and `Divide`) 
and one additional procedure (`Swap_Array_Elements`) have also been included 
in this example in order to demonstrate further features. `Max` returns the 
maximum of the two globals. `Divide` returns the division of the two globals 
after having ensured that the divisor is not equal to zero. The `Swap_Array_Elements` 
procedure swaps the contents of two elements of an array. For the same reasons
as in the previous example, the bodies are not included.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/pre_post_return/05/swap_add_max_05.ads
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/pre_post_return/14/swap_add_max_14.ads
      :language: ada
      :linenos:

.. _ms-nesting_refinement-label:

Nesting of subprograms, including more refinement
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This example demonstrates how procedures and functions can be nested within 
other procedures and functions. Furthermore, it illustrates how global variables 
refinement can be performed.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/nesting_refinement/05/nesting_refinement_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/nesting_refinement/05/nesting_refinement_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

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
of the code are identical. Thus, only the SPARK 2005 code will be presented. The reason 
why this code is being provided is to allow for a comparison between a package that is 
purely public and an equivalent one that also has private elements.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/adt_visible/05/stacks_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/adt_visible/05/stacks_05.adb
      :language: ada
      :linenos:

.. _ms-adt_private-label:

Private type
^^^^^^^^^^^^

Similarly to the previous example, this one does not contain any annotations either. Due 
to this, the SPARK 2005 and |SPARK| versions are exactly the same and hence only one of  
them shall be presented.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/adt_private/05/stacks_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/adt_private/05/stacks_05.adb
      :language: ada
      :linenos:

.. _ms-adt_private_refinement-label:

Private type with refined pre/post contracts in the body
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example demonstrates how `pre` and `post` conditions, that lie in the specifications 
of a package, can be refined in the package's body. In order to prove the absence of runtime 
errors, 3 user rules had to be introduced for the SPARK 2005 version. These rules are not 
presented here since they are not required in the |SPARK| version. Contracts that need not 
be refined, do not have to be repeated in the body of a package. In this particular example, 
the body of the SPARK 2005 might seem to be needlessly repeating contracts. However, this 
is not true since the contracts that are being repeated are indirectly being refined through 
the refinement of the `Is_Empty` and `Is_Full` functions.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/adt_private_refinement/05/stacks_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/adt_private_refinement/05/stacks_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

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

Specifications in |SPARK|:

   .. literalinclude:: ../code/adt_public_child_non_tagged_parent/14/pairs_14.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../code/adt_public_child_non_tagged_parent/14/pairs_14_additional_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

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

Specification in |SPARK|:

As per SPARK 2005.

Private/Public child visibility
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Public child and visibility of parent
+++++++++++++++++++++++++++++++++++++

See  section `Public child extends non-tagged parent ADT`_.


Private child and visibility of parent
++++++++++++++++++++++++++++++++++++++

TBD

Visibility of public siblings
+++++++++++++++++++++++++++++

TBD

Visibility of private siblings
++++++++++++++++++++++++++++++

TBD

Visibility to parent of private children
++++++++++++++++++++++++++++++++++++++++

TBD

General visibility of public child
++++++++++++++++++++++++++++++++++

The following example uses the child package defined in section
`Public child extends non-tagged parent ADT`_ to illustrate
use of that by another package.

Specification in SPARK 2005:

   .. literalinclude:: ../code/visibility_of_public_child/05/visibility_of_public_child_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/visibility_of_public_child/05/visibility_of_public_child_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

   .. literalinclude:: ../code/visibility_of_public_child/14/visibility_of_public_child_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

As per SPARK 2005.


Abstract State Machines (ASMs)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


Visible, concrete state
^^^^^^^^^^^^^^^^^^^^^^^

.. _ms-asm_visible_concrete_initialized_by_declaration-label:

Initialized by declaration
++++++++++++++++++++++++++

The example that follows presents a way of initializing a concrete state (a state that 
cannot be refined) at the point of the declaration of the variables that compose it. 
The body of the |SPARK| version of the code is not presented since it is an exact copy 
of the SPARK 2005 body.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_declaration/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_declaration/05/stack_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_declaration/14/stack_14.ads
      :language: ada
      :linenos:

.. _ms-asm_visible_concrete_initialized_by_elaboration-label:

Initialized by elaboration
++++++++++++++++++++++++++

The following example presents how a package's concrete state can be initialized at 
the statements section of the body. The |SPARK| version of the body is not presented 
since it is identical to the SPARK 2005 body.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_elaboration/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_elaboration/05/stack_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/asm_visible_concrete_initialized_by_elaboration/14/stack_14.ads
      :language: ada
      :linenos:

.. _ms-asm_private_concrete-label:

Private, concrete state
^^^^^^^^^^^^^^^^^^^^^^^

The following example demonstrates how variables, that need to be hidden from the users of 
a package, can be placed on the package's private section. The bodies of the packages have 
not been included since they contain no annotation.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/asm_private_concrete/05/stack_05.ads
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/asm_private_concrete/14/stack_14.ads
      :language: ada
      :linenos:

Private, abstract state, refining onto concrete states in body
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. _ms-asm_private_abstract_bodyref_procedureinit-label:

Initialized by procedure call
+++++++++++++++++++++++++++++

In this example, the abstract state declared at the specifications is refined at the body. 
Procedure `Init` can be invoked by users of the package, in order to initialize the state. 

Specifications in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_procedureinit/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_procedureinit/05/stack_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

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

The example that follows introduces an abstract state at the specifications and refines it 
at the body. The constituents of the abstract state are initialized at declaration.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_elaborationinit/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_elaborationinit/05/stack_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

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

This example introduces an abstract state at the specifications and refines it at the body. 
The constituents of the abstract state are initialized at the statements part of the body.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_statementinit/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_statementinit/05/stack_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_statementinit/14/stack_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_statementinit/14/stack_14.adb
      :language: ada
      :linenos:

.. _ms-asm_private_abstract_bodyref_mixedinit-label:

Initialized by mixture of declaration and statements
++++++++++++++++++++++++++++++++++++++++++++++++++++

This example introduces an abstract state at the specifications and refines it at the body. 
Some of the constituents of the abstract state are initialized during their declaration and 
the rest at the statements part of the body.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_mixedinit/05/stack_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_mixedinit/05/stack_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_mixedinit/14/stack_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/asm_private_abstract_bodyref_mixedinit/14/stack_14.adb
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

As per SPARK 2005

.. _ms-asm_abstract_state_refined_in_embedded_package-label:

Private, abstract state, refining onto concrete state of embedded package
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example is based around the packages from section `Private, abstract state,
refining onto concrete state of private child`_, with the private child packages
converted into embedded packages.

Specification in SPARK 2005

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/05/asm_abstract_state_refined_in_embedded_package_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/05/asm_abstract_state_refined_in_embedded_package_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/14/asm_abstract_state_refined_in_embedded_package_14.ads
      :language: ada
      :linenos:

Body in |SPARK|

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/14/asm_abstract_state_refined_in_embedded_package_14.adb
      :language: ada
      :linenos:

.. _ms-asm_abstract_state_refined_in_embedded_and_private_child-label:

Private, abstract state, refining onto mixture of the above
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example is based around the packages from sections `Private, abstract state,
refining onto concrete state of private child`_
and `Private, abstract state, refining onto concrete state of embedded package`_.
Source_A is an embedded package, while Source_B is a private child.

Specification of Parent in SPARK 2005

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_and_private_child/05/asm_abstract_state_refined_in_embedded_and_private_child_05.ads
      :language: ada
      :linenos:

Body of Parent in SPARK 2005

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_and_private_child/05/asm_abstract_state_refined_in_embedded_and_private_child_05.adb
      :language: ada
      :linenos:

Specification of Private Child in SPARK 2005:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_and_private_child/05/asm_abstract_state_refined_in_embedded_and_private_child-child_b_05.ads
      :language: ada
      :linenos:

Body of Private Child in SPARK 2005:

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_and_private_child/05/asm_abstract_state_refined_in_embedded_and_private_child-child_b_05.adb
      :language: ada
      :linenos:

Specification of Parent in |SPARK|

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_and_private_child/14/asm_abstract_state_refined_in_embedded_and_private_child_14.ads
      :language: ada
      :linenos:

Body of Parent in |SPARK|

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_and_private_child/14/asm_abstract_state_refined_in_embedded_and_private_child_14.adb
      :language: ada
      :linenos:

Specification of Private Child in |SPARK|

   .. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_and_private_child/14/asm_abstract_state_refined_in_embedded_and_private_child-child_b_14.ads
      :language: ada
      :linenos:

Body of Private Child in |SPARK|

As per SPARK 2005.


External Variables
~~~~~~~~~~~~~~~~~~

TBD

Basic Input and Output Device Drivers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example shows a main program - Copy - that reads all available data
from a given input port, stores it internally during the reading process in a stack
and then outputs all the data read to an output port.

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

Specification of Stack in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_output/05/stacks_05.ads
      :language: ada
      :linenos:


Specification of main program in |SPARK|:

TBD

Specification of input port in |SPARK|:

TBD

Specification of output port in |SPARK|:

TBD

Body of input port in |SPARK|:

TBD

Body of output port in |SPARK|:

TBD

Specification of Stack in |SPARK|:

TBD


Input driver using \'Append and \'Tail contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

*** Add the detail Flo wants in here. ***

This example uses the Input_Port package from section `Basic Input and Output Device Drivers`_
and adds a contract using the 'Tail attribute. The example also use the Always_Valid attribute
in order to allow proof to succeeed (otherwise, there is no guarantee in the proof context
that the value read from the port is of the correct type).

Specification in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_append_tail/05/input_port_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/external_variables_input_append_tail/05/input_port_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

TBD

Body in |SPARK|:

TBD

Output driver using \'Append and \'Tail contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example uses the Output package from section `Basic Input and Output Device Drivers`_
and adds a contract using the 'Append attribute.

Specification in SPARK 2005:

   .. literalinclude:: ../code/external_variables_output_append_tail/05/output_port_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/external_variables_output_append_tail/05/output_port_05.adb
      :language: ada
      :linenos:

Specification in |SPARK|:

TBD

Body in |SPARK|:

TBD


Refinement of external state - voting input switch
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Package Inheritance
~~~~~~~~~~~~~~~~~~~

TBD

Contracts with remote state
^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Package nested inside package
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

See section `Private, abstract state, refining onto concrete state of embedded package`_.

Package nested inside subprogram
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Circular dependence and elaboration order
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Bodies and Proof
----------------

TBD

Assert, Assume, Check contracts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

TBD

Assert used to control path explostion (ASPDV example)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

TBD

Other Contracts and Annotations
-------------------------------

TBD

Declare annotation
~~~~~~~~~~~~~~~~~~

TBD

Always_Valid assertion
~~~~~~~~~~~~~~~~~~~~~~

See section `Input driver using \'Append and \'Tail contracts`_ for use of an assertion involving
the Always_Valid attribute.

Rule declaration anno's
~~~~~~~~~~~~~~~~~~~~~~~

TBD

Proof types and proof functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following example gives pre- and post-conditions on operations that act upon
the concrete representation of an abstract own variable. This means that proof functions
and proof types are needed to state those pre- and post-conditions.

Specification in SPARK 2005

   .. literalinclude:: ../code/other_proof_types_and_functions/05/stack.ads
      :language: ada
      :linenos:

Body in SPARK 2005

   .. literalinclude:: ../code/other_proof_types_and_functions/05/stack.adb
      :language: ada
      :linenos:

Proof rule in SPARK 2005:

   .. literalinclude:: ../code/other_proof_types_and_functions/05/stack/push.rlu
      :language: ada
      :linenos:

Specification in |SPARK|

TBD

Body in |SPARK|

TBD

Proof rules in |SPARK|:

TBD

Main_Program annotation
~~~~~~~~~~~~~~~~~~~~~~~

See the main program annotation used in section `Basic Input and Output Device Drivers`_.

RavenSPARK patterns - (TBD, but check upward compatibility for the future)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

TBD

Other Examples
--------------

Stack example. Specifications in SPARK 2005:

   .. literalinclude:: ../code/the_stack/05/the_stack_05.ads
      :language: ada
      :linenos:

Stack example. Body in SPARK 2005:

   .. literalinclude:: ../code/the_stack/05/the_stack_05.adb
      :language: ada
      :linenos:

Stack example. Specifications in |SPARK|:

   .. literalinclude:: ../code/the_stack/14/the_stack_14.ads
      :language: ada
      :linenos:

Stack example. Body in |SPARK|:

   .. literalinclude:: ../code/the_stack/14/the_stack_14.adb
      :language: ada
      :linenos:

Stack example with conditions. Specifications in SPARK 2005:

   .. literalinclude:: ../code/the_stack_with_conditions/05/the_stack_with_conditions_05.ads
      :language: ada
      :linenos:

Stack example with conditions. Body in SPARK 2005:

   .. literalinclude:: ../code/the_stack_with_conditions/05/the_stack_with_conditions_05.adb
      :language: ada
      :linenos:

Stack example with conditions. Specifications in |SPARK|:

   .. literalinclude:: ../code/the_stack_with_conditions/14/the_stack_with_conditions_14.ads
      :language: ada
      :linenos:

Stack example with conditions. Body in |SPARK|:

   .. literalinclude:: ../code/the_stack_with_conditions/14/the_stack_with_conditions_14.adb
      :language: ada
      :linenos:

Stack example with more conditions. Specifications in SPARK 2005:

   .. literalinclude:: ../code/the_stack_with_more_conditions/05/the_stack_with_more_conditions_05.ads
      :language: ada
      :linenos:

Stack example with more conditions. Body in SPARK 2005:

   .. literalinclude:: ../code/the_stack_with_more_conditions/05/the_stack_with_more_conditions_05.adb
      :language: ada
      :linenos:

Stack example with more conditions. Specifications in |SPARK|:

   .. literalinclude:: ../code/the_stack_with_more_conditions/14/the_stack_with_more_conditions_14.ads
      :language: ada
      :linenos:

Stack example with more conditions. Body in |SPARK|:

   .. literalinclude:: ../code/the_stack_with_more_conditions/14/the_stack_with_more_conditions_14.adb
      :language: ada
      :linenos:
