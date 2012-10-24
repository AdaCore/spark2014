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

   .. literalinclude:: ../code/global_derives/05/global_derives_05.ads
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/global_derives/14/global_derives_14.ads
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

   .. literalinclude:: ../code/pre_post_return/05/pre_post_return_05.ads
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/pre_post_return/14/pre_post_return_14.ads
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

   .. literalinclude:: ../code/adt_visible/05/adt_visible_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/adt_visible/05/adt_visible_05.adb
      :language: ada
      :linenos:

.. _ms-adt_private-label:

Private type
^^^^^^^^^^^^

Similarly to the previous example, this one does not contain any annotations either. Due 
to this, the SPARK 2005 and |SPARK| versions are exactly the same and hence only one of  
them shall be presented.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/adt_private/05/adt_private_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/adt_private/05/adt_private_05.adb
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

   .. literalinclude:: ../code/adt_private_refinement/05/adt_private_refinement_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/adt_private_refinement/05/adt_private_refinement_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/adt_private_refinement/14/adt_private_refinement_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/adt_private_refinement/14/adt_private_refinement_14.adb
      :language: ada
      :linenos:

Public child extends non-tagged parent ADT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Tagged type in root ADT package
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Extension of tagged type in child package ADT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Private/Public child visibility
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Abstract State Machines (ASMs)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

TBD

Visible, concrete state
^^^^^^^^^^^^^^^^^^^^^^^

TBD

Initialized by declaration
++++++++++++++++++++++++++

TBD

Initialized by elaboration
++++++++++++++++++++++++++

TBD

Private, concrete state
^^^^^^^^^^^^^^^^^^^^^^^

TBD

Private, abstract state, refining onto concrete states in body
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Initialized by procedure call
+++++++++++++++++++++++++++++

TBD

Initialized by elab of declaration
++++++++++++++++++++++++++++++++++

TBD

Initialized by package body statements
++++++++++++++++++++++++++++++++++++++

TBD

Initialized by mixture of declaration and statements
++++++++++++++++++++++++++++++++++++++++++++++++++++

TBD

Private, abstract state, refining onto concrete state of private child
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Private, abstract state, refining onto concrete state of embedded package
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Private, abstract state, refining onto mixture of the above
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

External Variables
~~~~~~~~~~~~~~~~~~

TBD

Basic Input Device Driver
^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Basic Output Device Driver
^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Input driver using \'Append and \'Tail contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Output driver using \'Append and \'Tail
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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

TBD

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

TBD

Rule declaration anno's
~~~~~~~~~~~~~~~~~~~~~~~

TBD

Proof types
~~~~~~~~~~~

TBD

Proof functions
~~~~~~~~~~~~~~~

TBD

Main_Program annotation
~~~~~~~~~~~~~~~~~~~~~~~

TBD

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
