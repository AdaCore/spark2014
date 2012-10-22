.. _mapping-spec-label:

SPARK2005 to |SPARK| Mapping Specification
==========================================

This document defines the mapping between SPARK2005 and |SPARK|.
It is intended as both a completeness check for the |SPARK| language
design, and as a guide for projects upgrading from SPARK2005 to |SPARK|.

Subprogram patterns
-------------------

Global and Derives
~~~~~~~~~~~~~~~~~~

This example demonstrates how global variables can be accessed through 
procedures and functions and presents how the derives annotation is structured. 
The example comprises of one procedure (`Swap`) and one function (`Add`). `Swap` 
accesses two global variables and swaps their contents while `Add` returns their 
sum.


Specifications in SPARK 2005:

   .. literalinclude:: ../code/global_derives/05/global_derives_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/global_derives/05/global_derives_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/global_derives/14/global_derives_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/global_derives/14/global_derives_14.adb
      :language: ada
      :linenos:

Pre/Post/Return contracts
~~~~~~~~~~~~~~~~~~~~~~~~~

This example demonstrates how the Pre/Post/Return contracts are structured 
and how they map from SPARK 2005 to |SPARK|. Procedure `Swap` and function 
`add` perform the same task as in the previous example, but they have been 
augmented by post annotations. Two additional functions (`Max` and `Divide`) 
and one additional procedure (`Swap_Array_Elements`) have also been included 
in this example in order to demonstare further features. `Max` returns the 
maximum of the two globals. `Divide` returns the division of the two globals 
after having ensured that the divisor is not equal to zero. Notice that the 
result of the division is a real number while the global variables are 
integers. The `Swap_Array_Elements` procedure swaps the contents of two elements 
of an array.

Specifications in SPARK 2005:

   .. literalinclude:: ../code/pre_post_return/05/pre_post_return_05.ads
      :language: ada
      :linenos:

Body in SPARK 2005:

   .. literalinclude:: ../code/pre_post_return/05/pre_post_return_05.adb
      :language: ada
      :linenos:

Specifications in |SPARK|:

   .. literalinclude:: ../code/pre_post_return/14/pre_post_return_14.ads
      :language: ada
      :linenos:

Body in |SPARK|:

   .. literalinclude:: ../code/pre_post_return/14/pre_post_return_14.adb
      :language: ada
      :linenos:

Nesting of subprograms, including more refinement
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Procedures and functions can be nested within other procedures and functions. 
An example of such a case is illustrated in this subsection.

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

TBD

Abstract Data Types (ADTs)
~~~~~~~~~~~~~~~~~~~~~~~~~~

TBD

Visible type
^^^^^^^^^^^^

TBD

Private type
^^^^^^^^^^^^

TBD

Private type with refined pre/post contracts in the body
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

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