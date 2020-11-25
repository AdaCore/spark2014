SPARK 2005 to SPARK 2014 Mapping Specification
==============================================

This appendix defines the mapping between SPARK 2005 and |SPARK|.
It is intended as both a completeness check for the |SPARK| language
design, and as a guide for projects upgrading from SPARK 2005 to SPARK 2014.

SPARK 2005 Features and SPARK 2014 Alternatives
-----------------------------------------------

Nearly every SPARK 2005 feature has a SPARK 2014 equivalent or there is
an alternative way of providing the same feature in SPARK 2014.  The only
SPARK 2005 (not including RavenSPARK) features that do not have a direct
alternative are:

  * the 'Always_Valid attribute;

  * the ability to add pre and postconditions to an instantiation of a
    generic subprogram, e.g., Unchecked_Conversion; and

  * a precondition on the body of a subprogram refining the one on the
    specification - this is not usually required in SPARK 2014, it is
    normally replaced by the use of expression functions.

At the moment the first two features have to be accomplished using
pragma Assume.

The following subsections of this appendix demonstrate how many SPARK
2005 idioms map into SPARK 2014.  As a quick reference the table below
shows, for each SPARK 2005 annotation or SPARK 2005 specific feature,
a reference to the equivalent or alternative in SPARK 2014.  In the table
headings 2014 RM is the SPARK Reference Manual and Mapping is this
appendix, the SPARK 2005 to SPARK 2014 mapping specification.

================= ======================================== ========================================================= ========
SPARK 2005        SPARK 2014                               2014 RM                                                   Mapping
================= ======================================== ========================================================= ========
~ in post         'Old attribute   - see Ada RM 6.1.1                                                                :ref:`A.2.2 <ms-pre_post_return-label>`
~ in body         'Loop_Entry attribute                    :ref:`5.5.3 <Attribute Loop_Entry>`                       :ref:`A.7 <ms-value_of_variable_on_entry_to_a_loop-label>`
<->               =
A -> B            (if A then B)     - see Ada RM 4.5.7                                                               :ref:`A.2.2 <ms-pre_post_return-label>`
%                 not needed                                                                                         :ref:`A.7 <ms-value_of_variable_on_entry_to_a_loop-label>`
always_valid      not supported                                                                                      :ref:`A.4.1 <ms-proof_assume_contract-label>`
assert            pragma Assert_And_Cut                    :ref:`5.9 <Proof Pragmas>`                                :ref:`A.4.2 <ms-assert_no_loop_contract-label>`
assert in loop    pragma Loop_Invariant                    :ref:`5.5.3 <Loop Invariants, Variants and Entry Values>` :ref:`A.4.1 <ms-assert_loop_contract-label>`
assume            pragma Assume                            :ref:`5.9 <Proof Pragmas>`                                :ref:`A.4.1 <ms-proof_assume_contract-label>`
check             pragma Assert     - see Ada RM 11.4.2                                                              :ref:`A.4.1 <ms-check_contract-label>`
derives on spec   Depends aspect                           :ref:`6.1.5 <Depends Aspects>`                            :ref:`A.2.1 <ms-global_derives-label>`
derives on body   No separate spec - Depends aspect
derives on body   Separate spec - Refined_Depends aspect   :ref:`7.2.5 <Refined_Depends Aspects>`                    :ref:`A.3.2 <ms-asm_abstract_state_refined_in_private_child-label>`
for all           quantified_expression - see Ada RM 4.5.8                                                           :ref:`A.2.3 <ms-attributes_of_unconstrained_out_parameter_in_precondition-label>`
for some          quantified_expression - See Ada RM 4.5.8                                                           :ref:`A.4.1 <ms-assert_loop_contract-label>`
global on spec    Global aspect                            :ref:`6.1.4 <Global Aspects>`                             :ref:`A.2.1 <ms-global_derives-label>`
global on body    No separate spec - Global aspect
global on body    Separate spec - Refined_Global aspect    :ref:`7.2.4 <Refined_Global Aspects>`                     :ref:`A.2.4 <ms-nesting_refinement-label>`
hide              pragma SPARK_Mode - see User Guide
inherit           not needed                                                                                         :ref:`A.3.4 <ms-package_inheritance-label>`
initializes       Initializes aspect                       :ref:`7.1.5 <Initializes Aspects>`                        :ref:`A.2.4 <ms-nesting_refinement-label>`
main_program      not needed
object assertions rule declarations are not needed                                                                   :ref:`A.5.3 <ms-proof_types_and_proof_functions-label>`
own on spec       Abstract_State aspect                    :ref:`7.1.4 <Abstract_State Aspects>`                     :ref:`A.3.2 <ms-asm-label>`
own on body       Refined_State aspect                     :ref:`7.2.2 <Refined_State Aspects>`                      :ref:`A.3.2 <ms-asm-label>`
post on spec      postcondition     - see Ada RM 6.1.1     :ref:`6.1.1 <Preconditions and Postconditions>`           :ref:`A.2.2 <ms-pre_post_return-label>`
post on body      No separate spec - postcondition
post on body      Separate spec - Refined_Post aspect      :ref:`7.2.7 <Refined Postcondition Aspects>`
pre               precondition      - see Ada RM 6.1.1     :ref:`6.1.1 <Preconditions and Postconditions>`
proof functions   Ghost functions                          :ref:`6.9 <Ghost Entities>`                               :ref:`A.5.3 <ms-proof_types_and_proof_functions-label>`
proof types       Ada types                                                                                          :ref:`A.5.5 <ms-quote_own_variable_in_contract-label>`
return            'Result attribute - see Ada RM 6.1.1                                                               :ref:`A.2.2 <ms-pre_post_return-label>`
update            delta aggregate                                                                                    :ref:`A.6 <ms-quote_own_variable_in_contract-label>`
================= ======================================== ========================================================= ========

Subprogram patterns
-------------------

.. _ms-global_derives-label:

Global and Derives
~~~~~~~~~~~~~~~~~~

This example demonstrates how global variables can be accessed through
procedures/functions and presents how the SPARK 2005 `derives` annotation maps
over to `depends` in SPARK 2014. The example consists of one procedure (`Swap`) and
one function (`Add`). `Swap` accesses two global variables and swaps their contents
while `Add` returns their sum.

Specification in SPARK 2005:

.. literalinclude:: ../code/global_derives/05/swap_add_05.ads
   :language: ada
   :linenos:

body in SPARK 2005:

.. literalinclude:: ../code/global_derives/05/swap_add_05.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__global_derives/swap_add_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__global_derives/swap_add_14.adb
   :language: ada
   :linenos:

.. _ms-pre_post_return-label:

Pre/Post/Return contracts
~~~~~~~~~~~~~~~~~~~~~~~~~

This example demonstrates how the `Pre`/`Post`/`Return` contracts are
restructured and how they map from SPARK 2005 to SPARK 2014. Procedure
`Swap` and function `Add` perform the same task as in the previous
example, but the global variables have been replaced by parameters
(this is not necessarry for proof) and they have been augmented by pre
and post annotations. Two additional functions (`Max` and `Divide`)
and one additional procedure (`Swap_Array_Elements`) have also been
included in this example in order to demonstrate further
features. `Max` returns the maximum of the two parameters. `Divide`
returns the division of the two parameters after having ensured that the
divisor is not equal to zero. The `Swap_Array_Elements` procedure
swaps the contents of two elements of an array.

Specification in SPARK 2005:

.. literalinclude:: ../code/pre_post_return/05/swap_add_max_05.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/pre_post_return/05/swap_add_max_05.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__pre_post_return/swap_add_max_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__pre_post_return/swap_add_max_14.adb
   :language: ada
   :linenos:

.. _ms-attributes_of_unconstrained_out_parameter_in_precondition-label:

Attributes of unconstrained out parameter in precondition
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following example illustrates the fact that the attributes of an unconstrained
formal array parameter of mode "out" are permitted to appear in a precondition.
The flow analyzer also needs to be smart about this, since it knows that X'First and
X'Last are well-defined in the body, even though the content of X is not.

Specification in SPARK 2005:

.. literalinclude:: ../code/attributes_of_unconstrained_out_parameter_in_precondition/05/p.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/attributes_of_unconstrained_out_parameter_in_precondition/05/p.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__attributes_of_unconstrained_out_parameter_in_precondition/p.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__attributes_of_unconstrained_out_parameter_in_precondition/p.adb
   :language: ada
   :linenos:

.. _ms-nesting_refinement-label:

Data Abstraction, Refinement and Initialization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This example demonstrates data abstraction and refinement.  It also
shows how abstract data is shown to be initialized during package
elaboration (it need not be - it could be initialized through an
explicit subprogram call, in which case the Initalizes annotation
should not be given).  There is also a demonstration of how procedures
and functions can be nested within other procedures and
functions. Furthermore, it illustrates how global variable refinement
can be performed.

Specification in SPARK 2005:

.. literalinclude:: ../code/nesting_refinement/05/nesting_refinement_05.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/nesting_refinement/05/nesting_refinement_05.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__nesting_refinement/nesting_refinement_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__nesting_refinement/nesting_refinement_14.adb
   :language: ada
   :linenos:

Package patterns
----------------

Abstract Data Types (ADTs)
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _ms-adt_visible-label:

Visible type
^^^^^^^^^^^^

The following example adds no mapping information. The SPARK 2005 and SPARK 2014 versions
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
to this, the SPARK 2005 and SPARK 2014 versions are exactly the same. Only the specification of
the 2005 version shall be presented.

Specification in SPARK 2005:

.. literalinclude:: ../code/adt_private/05/stacks_05.ads
   :language: ada
   :linenos:

.. _ms-adt_private_refinement-label:

Private type with pre/post contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example demonstrates how `pre` and `post` conditions of
subprograms may be specified in terms of functions declared in the
same package specification.  The function declarations are completed
in the body and the postconditions of the completed functions are used
to prove the implementations of the other subprograms.  In SPARK 2014
explicit postconditions do not have to be specified on the bodies of
the functions as they are implemented as expression functions and the
expression, E, of the function acts as a default refined
postcondition, i.e., F'Result = E.  Note that the SPARK 2014 version is
proven entirely automatically whereas the SPARK 2005 version requires
user defined proof rules.

Specification in SPARK 2005:

.. literalinclude:: ../code/adt_private_refinement/05/stacks_05.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/adt_private_refinement/05/stacks_05.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_refinement/stacks_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_refinement/stacks_14.adb
   :language: ada
   :linenos:

.. _ms-adt_public_child_non_tagged_parent-label:

.. Tagged types not supported as yet
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

    Specifications of both parent and child in SPARK 2014:

    .. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_public_child_non_tagged_parent/pairs_14.ads
       :language: ada
       :linenos:

    .. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_public_child_non_tagged_parent/pairs_14_additional_14.ads
       :language: ada
       :linenos:

    Bodies of both parent and child in SPARK 2014:

    As per SPARK 2005.

.. _ms-adt_tagged_type-label:

.. Tagged types not supported as yet
    Tagged type in root ADT package
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    The following example illustrates the use of a tagged type in an ADT package.

    Specification in SPARK 2005:

    .. literalinclude:: ../code/adt_tagged_type/05/stacks_05.ads
       :language: ada
       :linenos:

    Body in SPARK 2005:

    N/A

    Specification in SPARK 2014:

    .. literalinclude:: ../code/adt_tagged_type/14/stacks_14.ads
       :language: ada
       :linenos:

    Body in SPARK 2014:

    N/A

.. _ms-adt_tagged_type_extension-label:

.. Tagged types not supported as yet
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

    Specification in SPARK 2014:

    .. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_tagged_type_extension/stacks_14_monitored_14.ads
       :language: ada
       :linenos:

    Body in SPARK 2014:

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

SPARK 2014 shares Ada's visibility rules. No restrictions have been applied
in terms of visibility.  Note that SPARK 2014 code does not require Inherit annotations.

Specification of parent in SPARK 2005:

.. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05.ads
   :language: ada
   :linenos:

Specification of private child A in SPARK 2005:

.. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05-private_child_a_05.ads
   :language: ada
   :linenos:

Specification of private child B in SPARK 2005:

.. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05-private_child_b_05.ads
   :language: ada
   :linenos:

Specification of public child A in SPARK 2005:

.. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05-public_child_a_05.ads
   :language: ada
   :linenos:

Specification of public child B in SPARK 2005:

.. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05-public_child_b_05.ads
   :language: ada
   :linenos:

Body of parent in SPARK 2005:

.. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05.adb
   :language: ada
   :linenos:

Body of public child A in SPARK 2005:

.. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05-public_child_a_05.adb
   :language: ada
   :linenos:

Body of public child B in SPARK 2005:

.. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05-public_child_b_05.adb
   :language: ada
   :linenos:

Body of private child B in SPARK 2005:

.. literalinclude:: ../code/adt_private_public_child_visibility/05/parent_05-private_child_b_05.adb
   :language: ada
   :linenos:

Specification of parent in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_public_child_visibility/parent_14.ads
   :language: ada
   :linenos:

Specification of private child A in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_public_child_visibility/parent_14-private_child_a_14.ads
   :language: ada
   :linenos:

Specification of private child B in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_public_child_visibility/parent_14-private_child_b_14.ads
   :language: ada
   :linenos:

Specification of public child A in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_public_child_visibility/parent_14-public_child_a_14.ads
   :language: ada
   :linenos:

Specification of public child B in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_public_child_visibility/parent_14-public_child_b_14.ads
   :language: ada
   :linenos:

Body of parent in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_public_child_visibility/parent_14.adb
   :language: ada
   :linenos:

Body of public child A in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_public_child_visibility/parent_14-public_child_a_14.adb
   :language: ada
   :linenos:

Body of public child B in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_public_child_visibility/parent_14-public_child_b_14.adb
   :language: ada
   :linenos:

Body of private child B in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__adt_private_public_child_visibility/parent_14-private_child_b_14.adb
   :language: ada
   :linenos:

.. _ms-asm-label:

Abstract State Machines (ASMs)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Visible, concrete state
^^^^^^^^^^^^^^^^^^^^^^^

.. _ms-asm_visible_concrete_initialized_by_declaration-label:

Initialized by declaration
++++++++++++++++++++++++++

The example that follows presents a way in SPARK 2005 of initializing
a concrete own variable (a state that is not refined) at the point
of the declaration of the variables that compose it.  Generally it
is not good practice to declare several concrete own variables,
data abstraction should be used but here we are doing it for the
point of illustration.

In SPARK 2014 the client's view of package state is either visible
(declared in the visible part of the package) or a state abstraction
representing hidden state.  A variable cannot overload the name of a
state abstraction and therefore a state abstraction must be completed
by a refinement given in the body of the package - there is no concept
of a concrete state abstraction.  The constituents of a state
abstraction may be initialized at their declaration.

Specification in SPARK 2005:

.. literalinclude:: ../code/asm_visible_concrete_initialized_by_declaration/05/stack_05.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/asm_visible_concrete_initialized_by_declaration/05/stack_05.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_visible_concrete_initialized_by_declaration/stack_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_visible_concrete_initialized_by_declaration/stack_14.adb
   :language: ada
   :linenos:

.. _ms-asm_visible_concrete_initialized_by_elaboration-label:

Initialized by elaboration
++++++++++++++++++++++++++

The following example presents how a package's concrete state can be initialized at
the statements section of the body. The specifications of both SPARK 2005 and SPARK 2014
are not presented since they are identical to the specifications of the previous example.

Body in SPARK 2005:

.. literalinclude:: ../code/asm_visible_concrete_initialized_by_elaboration/05/stack_05.adb
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_visible_concrete_initialized_by_elaboration/stack_14.adb
   :language: ada
   :linenos:

.. _ms-asm_private_concrete-label:

Private, concrete state
^^^^^^^^^^^^^^^^^^^^^^^

In SPARK 2005 variables declared in the private part of a package are
considered to be concrete own variables.  In SPARK 2014 they are hidden
state and must be constituents of a state abstraction.

The SPARK 2005 body has not been included since it does not contain
any annotations.

Specification in SPARK 2005:

.. literalinclude:: ../code/asm_private_concrete/05/stack_05.ads
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_private_concrete/stack_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_private_concrete/stack_14.adb
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

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_private_abstract_bodyref_procedureinit/stack_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_private_abstract_bodyref_procedureinit/stack_14.adb
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

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_private_abstract_bodyref_elaborationinit/stack_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_private_abstract_bodyref_elaborationinit/stack_14.adb
   :language: ada
   :linenos:

.. _ms-asm_private_abstract_bodyref_statementinit-label:

Initialized by package body statements
++++++++++++++++++++++++++++++++++++++

This example introduces an abstract state at the specification and refines it at the body.
The constituents of the abstract state are initialized at the statements part of the body.
The specifications of the SPARK 2005 and SPARK 2014 versions of the code are as in the previous
example and have thus not been included.

Body in SPARK 2005:

.. literalinclude:: ../code/asm_private_abstract_bodyref_statementinit/05/stack_05.adb
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_private_abstract_bodyref_statementinit/stack_14.adb
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

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_private_abstract_bodyref_mixedinit/stack_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_private_abstract_bodyref_mixedinit/stack_14.adb
   :language: ada
   :linenos:

.. _ms-asm_initial_condition-label:

Initial condition
^^^^^^^^^^^^^^^^^

This example introduces a new SPARK 2014 feature that did not exist in
SPARK 2005. On top of declaring an abstract state and promising to
initialize it, we also illustrate certain conditions that will be
valid after initialization. There is a verification condition to show that
immediately after the elaboration of the package that the specified
Initial_Condition is True. Checks will be generated that have to be
proven (or executed at run-time) to show that the initial condition is
True.

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_initial_condition/stack_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_initial_condition/stack_14.adb
   :language: ada
   :linenos:

.. _ms-asm_abstract_state_refined_in_private_child-label:

Private, abstract state, refining onto state of private child
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example shows a parent package Power that contains an
own variable (a state abstraction). This state abstraction is refined
onto state abstractions of two private children Source_A and Source_B.

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

Specification of Parent in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_abstract_state_refined_in_private_child/power_14.ads
   :language: ada
   :linenos:

Body of Parent in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_abstract_state_refined_in_private_child/power_14.adb
   :language: ada
   :linenos:

Specifications of Private Children in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_abstract_state_refined_in_private_child/power_14-source_a_14.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_abstract_state_refined_in_private_child/power_14-source_b_14.ads
   :language: ada
   :linenos:

Bodies of Private Children in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_abstract_state_refined_in_private_child/power_14-source_a_14.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_abstract_state_refined_in_private_child/power_14-source_b_14.adb
   :language: ada
   :linenos:

.. _ms-asm_abstract_state_refined_in_embedded_package-label:

Private, abstract state, refining onto concrete state of embedded package
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example is based around the packages from section
:ref:`ms-asm_abstract_state_refined_in_embedded_package-label`,
with the private child packages converted into embedded packages and
the refinement onto concrete visible state.

Specification in SPARK 2005:

.. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/05/power_05.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/asm_abstract_state_refined_in_embedded_package/05/power_05.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_abstract_state_refined_in_embedded_package/power_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__asm_abstract_state_refined_in_embedded_package/power_14.adb
   :language: ada
   :linenos:

.. _ms-asm_abstract_state_refined_in_embedded_and_private_child-label:

Private, abstract state, refining onto mixture of the above
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example is based around the packages from sections
:ref:`ms-asm_abstract_state_refined_in_private_child-label`
and :ref:`ms-asm_abstract_state_refined_in_embedded_package-label`.
Source_A is an embedded package, while Source_B is a private child. In order to
avoid repetition, the code of this example is not being presented.

External Variables
~~~~~~~~~~~~~~~~~~

.. _ms-external_variables_input_output-label:

Basic Input and Output Device Drivers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following example shows a main program - Copy - that reads all available data
from a given input port, stores it internally during the reading process in a stack
and then outputs all the data read to an output port. The specifications of the
stack packages are not presented since they are identical to previous examples.

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

Specification of main program in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_input_output/copy_14.adb
   :language: ada
   :linenos:

Specification of input port in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_input_output/input_port_14.ads
   :language: ada
   :linenos:

Specification of output port in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_input_output/output_port_14.ads
   :language: ada
   :linenos:

Body of input port in SPARK 2014:

This is as per SPARK 2005, but uses aspects instead of representation clauses and pragmas.

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_input_output/input_port_14.adb
   :language: ada
   :linenos:

Body of output port in SPARK 2014:

This is as per SPARK 2005, but uses aspects instead of representation clauses and pragmas.

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_input_output/output_port_14.adb
   :language: ada
   :linenos:

.. _ms-external_variables_input_append_tail-label:

Input driver using \'Tail in a contract
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example uses the Input_Port package from section `Basic Input and Output Device Drivers`_
and adds a contract using the 'Tail attribute. The example also use the Always_Valid attribute
in order to allow proof to succeed (otherwise, there is no guarantee in the proof context
that the value read from the port is of the correct type).

SPARK 2014 does not have the attribute 'Tail but, often, an equivalent
proof can be achieved using assert pragmas.  Neither is there a direct
equivalent of the Always_Valid attribute but the paragma Assume may be
used to the same effect.

Specification in SPARK 2005:

.. literalinclude:: ../code/external_variables_input_append_tail/05/input_port_05.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/external_variables_input_append_tail/05/input_port_05.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_input_append_tail/input_port_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_input_append_tail/input_port_14.adb
   :language: ada
   :linenos:

.. _ms-external_variables_output_append_tail-label:

Output driver using \'Append in a contract
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example uses the Output package from section `Basic Input and Output Device Drivers`_
and adds a contract using the 'Append attribute.

SPARK 2014 does not have the attribute 'Append but, often, an equivalent proof can
be achieved using assert pragmas.

Specification in SPARK 2005:

.. literalinclude:: ../code/external_variables_output_append_tail/05/output_port_05.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/external_variables_output_append_tail/05/output_port_05.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_output_append_tail/output_port_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_output_append_tail/output_port_14.adb
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

Abstract Switch specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_refinement_voting_input_switch/switch.ads
   :language: ada
   :linenos:

Component Switch specifications in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_refinement_voting_input_switch/switch-val1.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_refinement_voting_input_switch/switch-val2.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_refinement_voting_input_switch/switch-val3.ads
   :language: ada
   :linenos:

Switch body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_refinement_voting_input_switch/switch.adb
   :language: ada
   :linenos:

.. _ms-external_variables_complex_io_device-label:

Complex I/O Device
^^^^^^^^^^^^^^^^^^

The following example illustrates a more complex I/O device: the device is fundamentally
an output device but an acknowledgement has to be read from it. In addition, a local register
stores the last value written to avoid writes that would just re-send the same value.
The own variable is then refined into a normal variable, an input external variable
and an output external variable.

Specification in SPARK 2005:

.. literalinclude:: ../code/external_variables_complex_io_device/05/device.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/external_variables_complex_io_device/05/device.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_complex_io_device/device.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_complex_io_device/device.adb
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

In SPARK 2014 we can use assert pragmas in the subprogram instead of
specifying the action in the postcondition, as was done in
:ref:`ms-external_variables_input_append_tail-label`. Another
alternative, as shown in this example, is to use a formal parameter of
a private type to keep a trace of the values read.

Specification in SPARK 2005:

.. literalinclude:: ../code/external_variables_increasing_values_in_input_stream/05/inc.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/external_variables_increasing_values_in_input_stream/05/inc.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_increasing_values_in_input_stream/inc.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__external_variables_increasing_values_in_input_stream/inc.adb
   :language: ada
   :linenos:

.. _ms-package_inheritance-label:

Package Inheritance
~~~~~~~~~~~~~~~~~~~

SPARK 2014 does not have the SPARK 2005 concept of package
inheritance.  It has the same package visibility rules as Ada.

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

Specifications in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__contracts_with_remote_state/raw_data.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__contracts_with_remote_state/processing.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__contracts_with_remote_state/calculate.ads
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

Abstract Switch specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__package_nested_inside_subprogram/switch.ads
   :language: ada
   :linenos:

Component Switch specification in SPARK 2014:

As in `Refinement of external state - voting input switch`_

Switch body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__package_nested_inside_subprogram/switch.adb
   :language: ada
   :linenos:


.. _ms-circular_dependence_and_elaboration_order-label:

Circular dependence and elaboration order
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

SPARK 2005 avoided issues of circular dependence and elaboration order
dependencies through a combination of the inherit annotation and the
restrictions that initialization expressions are constant, user
defined subprograms cannot be called in the sequence of statements of
a package body and a package can only initialize variables declared in
its delarative part.

SPARK 2014 does not have the inherit annotation and only enforces the
restriction that a package can only initialize an object declared in
its declarative region. Hence, in SPARK 2014 two package bodies that
depend on each other's specification may be legal, as is calling a user
defined suprogram.

Instead of the elaboration restrictions of SPARK 2005 a set of rules
is applied in SPARK 2014 which determines when elaboration order control
pragmas such as Elaborate_Body or Elaborate_All are required.  These
rules ensure the absence of elaboration order dependencies.

Examples of the features of SPARK 2014 elaboration order rules are given
below. In the example described below the partial elaboration order
would be either of P_14 or Q_14 specifications first followed by P_14
body because of the Elaborate_All on the specification of R_14
specification and the body of Q_14, then the elaboration of Q_14 body
or the specification of R_14 and the body of R_14 after the
elaboration of Q_14. Elaboration order dependencies are avoided by
the (required) use of elaboration control pragmas.

Package Specifications in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__circular_dependence_and_elaboration_order/p_14.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__circular_dependence_and_elaboration_order/q_14.ads
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__circular_dependence_and_elaboration_order/r_14.ads
   :language: ada
   :linenos:

Package Bodies in SPARK 2014

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__circular_dependence_and_elaboration_order/p_14.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__circular_dependence_and_elaboration_order/q_14.adb
   :language: ada
   :linenos:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__circular_dependence_and_elaboration_order/r_14.adb
   :language: ada
   :linenos:

Bodies and Proof
----------------

Assert, Assume, Check contracts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _ms-assert_loop_contract-label:

Assert (in loop) contract
^^^^^^^^^^^^^^^^^^^^^^^^^

The following example demonstrates how the SPARK 2005 `assert`
annotation is used inside a loop as a loop invariant. It cuts the loop
and on each iteration of the loop the list of existing hypotheses
for the path is cleared. A verification condition is generated to prove
that the assert expression is True, and the expression is the basis of
the new hypotheses.

SPARK 2014 has a specific pragma for defining a loop invariant, `pragma
Loop_Invariant` which is more sophisticated than the SPARK 2005 assert
annotation and often requires less conditions in the invariant
expression than in SPARK 2005. As in SPARK 2005 a default loop
invariant will be used if one is not provided which, often, may be
sufficient to prove absence of run-time exceptions. Like all
SPARK 2014 assertion expressions the loop invariant is executable.

Note in the example below the SPARK 2014 version proves absence of
run-time exceptions without an explicit loop invariant being provided.

Specification in SPARK 2005:

.. literalinclude:: ../code/assert_loop_contract/05/assert_loop_05.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/assert_loop_contract/05/assert_loop_05.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__assert_loop_contract/assert_loop_14.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__assert_loop_contract/assert_loop_14.adb
   :language: ada
   :linenos:

.. _ms-assert_no_loop_contract-label:

Assert (no loop) contract
^^^^^^^^^^^^^^^^^^^^^^^^^

While not in a loop, the SPARK 2005 `assert` annotation maps to
`pragma Assert_And_Cut` in SPARK 2014. Both the assert annotation and
pragma assert clear the list of hypotheses on the path, generate a
verification condition to prove the assertion expression and use the
assertion expression as the basis of the new hypotheses.

.. _ms-proof_assume_contract-label:

Assume contract
^^^^^^^^^^^^^^^

The following example illustrates use of an Assume annotation.  The
assumed expression does not generate a verification condition and is
not proved (although it is executed in SPARK 2014 if assertion
expressions are not ignored at run-time).

In this example, the Assume annotation is effectively being used to
implement the SPARK 2005 Always_Valid attribute.

Specification for Assume annotation in SPARK 2005:

.. literalinclude:: ../code/proof_assume_contract/05/input_port.ads
   :language: ada
   :linenos:

Body for Assume annotation in SPARK 2005:

.. literalinclude:: ../code/proof_assume_contract/05/input_port.adb
   :language: ada
   :linenos:

Specification for Assume annotation in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__proof_assume_contract/input_port.ads
   :language: ada
   :linenos:

Body for Assume annotation in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__proof_assume_contract/input_port.adb
   :language: ada
   :linenos:

.. _ms-check_contract-label:

Check contract
^^^^^^^^^^^^^^

The SPARK 2005 `check` annotation is replaced by `pragma assert` in
SPARK 2014. This annotation generates a verification condition to prove
the checked expression and adds the expression as a new hypothesis to
the list of existing hypotheses.

Specification for Check annotation in SPARK 2005:

.. literalinclude:: ../code/check_contract/05/check_05.ads
   :language: ada
   :linenos:

Body for Check annotation in SPARK 2005:

.. literalinclude:: ../code/check_contract/05/check_05.adb
   :language: ada
   :linenos:

Specification for Check annotation in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__check_contract/check_14.ads
   :language: ada
   :linenos:

Body for Check annotation in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__check_contract/check_14.adb
   :language: ada
   :linenos:

Assert used to control path explosion
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This capability is in general not needed with the SPARK 2014 toolset where
path explosion is handled automatically. In the rare cases where this is
needed you can use `pragma Assert_And_Cut`.

Other Contracts and Annotations
-------------------------------

Always_Valid assertion
~~~~~~~~~~~~~~~~~~~~~~

See section `Input driver using \'Tail in a contract`_ for use of an assertion involving
the Always_Valid attribute.

Rule declaration annotation
~~~~~~~~~~~~~~~~~~~~~~~~~~~

See section `Proof types and proof functions`_.

.. _ms-proof_types_and_proof_functions-label:

Proof types and proof functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following example gives pre- and postconditions on operations that
act upon the concrete representation of an abstract own variable. This
means that proof functions and proof types are needed to state those
pre- and postconditions. In addition, it gives an example of the use
of a rule declaration annotation - in the body of procedure
Initialize - to introduce a rule related to the components of a
constant record value.

SPARK 2014 does not have a direct equivalent of proof types and proof
functions. State abstractions cannot have a type and all functions in
SPARK 2014 are Ada functions.  Functions may be defined to be ghost functions
which means that they can only be called within an
assertion expression such as a pre or postcondition. Assertion
expressions may be executed or ignored at run-time and if they are
ignored Ghost functions behave much like SPARK 2005 proof functions.

Rule declaration annotations for structured constants are not required in SPARK 2014.

The SPARK 2005 version of the example given below will require user
defined proof rules to discharge the proofs because refined
definitions of some of the proof functions cannot be provided as they
would have different formal parameters. The SPARK 2014 version does not
suffer from this problem as functions called within assertion expressions
may have global items.

Specification in SPARK 2005:

.. literalinclude:: ../code/other_proof_types_and_functions/05/stack.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/other_proof_types_and_functions/05/stack.adb
   :language: ada
   :linenos:

Specification in SPARK 2014

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__other_proof_types_and_functions/stack.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__other_proof_types_and_functions/stack.adb
   :language: ada
   :linenos:

Using an External Prover
~~~~~~~~~~~~~~~~~~~~~~~~

One may wish to use an external prover such as Isabelle, with rules
defining a ghost function written in the prover input language. This
can be done in SPARK 2014 by denoting the ghost function as an Import in
lieu of providing a body for it. Of course such ghost functions cannot
be executed.

Specification in SPARK 2014 using an external prover:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__other_proof_types_and_functions/stack_external_prover.ads
   :language: ada
   :linenos:

.. _ms-quote_own_variable_in_contract-label:

Quoting an Own Variable in a Contract
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Sometimes it is necessary to reference an own variable (a state
abstraction) in a contract. In SPARK 2005 this was achieved by
declaring the own variable with a type, either concrete or
abstract. As seen in :ref:`ms-proof_types_and_proof_functions-label`.
Once the own variable has a type it can be used in a SPARK 2005 proof
context.

A state abstraction in SPARK 2014 does not have a type. Instead, an Ada
type to represent the abstract state is declared. A function
which has the state abstraction as a global item is then declared
which returns an object of the type. This function may have the same
name as the state abstraction (the name is overloaded). References
which appear to be the abstract state in an assertion expression are
in fact calls to the overloaded function.

An example of this technique is given in the following example which
is a version of the stack example given in
:ref:`ms-proof_types_and_proof_functions-label` but with the post
conditions extended to express the functional properties of the stack.

The extension requires the quoting of the own variable/state
abstraction in the postcondition in order to state that the contents
of the stack other than the top entries are not changed.

Specification in SPARK 2005:

.. literalinclude:: ../code/other_proof_types_and_functions/05/stack_functional_spec.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/other_proof_types_and_functions/05/stack_functional_spec.adb
   :language: ada
   :linenos:

Specification in SPARK 2014

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__other_proof_types_and_functions/stack_functional_spec.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__other_proof_types_and_functions/stack_functional_spec.adb
   :language: ada
   :linenos:

Main_Program annotation
~~~~~~~~~~~~~~~~~~~~~~~

This annotation isn't needed.  Currently any parameterless procedure
declared at library-level is considered as a potential main program
and analyzed as such.

.. _ms-update_expressions-label:

Update Expressions
------------------

SPARK 2005 has update expressions for updating records and arrays.
They can only be used in SPARK 2005 proof contexts.

The equivalent in SPARK 2014 is a delta aggregate.  This can be
used in any Ada expression.

Specification in SPARK 2005:

.. literalinclude:: ../code/update_examples/05/update_examples.ads
   :language: ada
   :linenos:

Specification in SPARK 2014

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/update_examples.ads
   :language: ada
   :linenos:

.. _ms-value_of_variable_on_entry_to_a_loop-label:

Value of Variable on Entry to a Loop
------------------------------------

In SPARK 2005 the entry value of a for loop variable variable, X, can
be referenced using the notation X%.  This notation is required
frequently when the variable is referenced in a proof context within
the loop.  Often it is needed to state that the value of X is not
changed within the loop by stating X = X%.  This notation is
restricted to a variable which defines the lower or upper range of a
for loop.

SPARK 2014 has a more general scheme whereby the loop entry value of any
variable can be denoted within any sort of loop using the
'*Loop_Entry* attribute.  However, its main use is not for showing
that the value of a for loop variable has not changed as the SPARK 2014
tools are able to determine this automatically.  Rather it is used
instead of ~ in loops because the attribute 'Old is only permitted in
postconditions (including Contract_Cases).

Specification in SPARK 2005:

.. literalinclude:: ../code/loop_entry/05/loop_entry.ads
   :language: ada
   :linenos:

Body in SPARK 2005:

.. literalinclude:: ../code/loop_entry/05/loop_entry.adb
   :language: ada
   :linenos:

Specification in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__loop_entry/loop_entry.ads
   :language: ada
   :linenos:

Body in SPARK 2014:

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_MS__loop_entry/loop_entry.adb
   :language: ada
   :linenos:




..
  RavenSPARK patterns
  ~~~~~~~~~~~~~~~~~~~

  The Ravenscar profile for tasking is not yet supported in SPARK 2014.
  Mapping examples will be added here in future.
