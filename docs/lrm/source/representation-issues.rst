Representation Issues
=====================

.. todo:: Provide full detail on Representation Issues.
          To be completed in a post-Release 1 version of this document.


Operational and Representation Aspects
---------------------------------------

|SPARK| defines several Boolean-valued aspects. These include the
Async_Readers, Async_Writers, Constant_After_Elaboration,
Effective_Reads, Effective_Writes, Extensions_Visible, Ghost,
and Volatile_Function aspects.
[Note that this list does not include expression-valued aspects,
such as Default_Initial_Condition or Initial_Condition.]

The following rules apply to each of these aspects unless specified
otherwise for a particular aspect:

1. In the absence of an aspect specification (explicit or inherited),
   the default value of the given aspect is False.

2. If the given aspect is specified via an aspect_specification
   [(as opposed to via a pragma)] then the aspect_definition
   (if any) shall be a static Boolean expression.
   [Omitting the aspect_definition in an aspect_specification is equivalent
   to specifying a value of True as described in Ada RM 13.1.1(15).]

3. The usage names in an aspect_definition for the given aspect are
   resolved at the point of the associated declaration. [This supersedes
   the name resolution rule given in Ada RM 13.1.1 that states that such names
   are resolved at the end of the enclosing declaration list.]

[One case where the "unless specified otherwise" clause applies
is illustrated by

   X : Integer with Volatile;

where the Async_Readers aspect of X is True, not False.]

Ada allows aspect specifications for package declarations and package
bodies but does not define any aspects which can be specified in this
way. |SPARK| defines, for example, the Initial_Condition and Refined_State
aspects (the former can be specified for a package declaration; the latter
for a package body). Ada's usual rule that

   The usage names in an aspect_definition [are not resolved at the point of
   the associated declaration, but rather] are resolved at the end of the
   immediately enclosing declaration list.

is applied for such aspects as though "the immediately enclosing
declaration list" is that of the visible part (in the former case) or of
the body (in the latter case).
[For example, the Initial_Condition expression of a package which declares a
variable in its visible part can (directly) name that variable. Simlarly, the
Refined_State aspect specification for a package body can name variables
declared within the package body.]

Packed Types
------------

No restrictions or additions.

Operational and Representation Attributes
-----------------------------------------

No restrictions or additions.

Enumeration Representation Clauses
----------------------------------

No restrictions or additions.

Record Layout
-------------

Change of Representation
------------------------

No restrictions or additions.

The Package System
------------------

.. centered:: **Legality Rules**

.. _tu-the_package_system-01:

1. The use of the operators defined for type Address are not permitted
   in |SPARK| except for use within representation clauses.

.. _etu-the_package_system:

Machine Code Insertions
-----------------------

.. centered:: **Legality Rules**

.. _tu-machine_code_insertions-01:

1. Machine code insertions are not in |SPARK|.

.. _etu-machine_code_insertions:

Unchecked Type Conversions
--------------------------

The validity of unchecked type conversions is not currently checked by
|SPARK| the onus is on the user to ensure that the value read from an
unchecked type conversion is valid (see :ref:`data_validity`).

.. todo::
   Provide a detailed semantics for Refined_Pre and Refined_Post aspects on
   Unchecked_Conversion. To be completed in a post-Release 1 version of this document.

.. _data_validity:

Data Validity
~~~~~~~~~~~~~

Currently |SPARK| does not check for data validity.
It is therefore up to users to ensure that data read from
external sources and values from unchecked type conversions are valid.

Validity can be ensured by using a type for the target of the data
read from an external source or an unchecked type conversion which is
sufficient to encompass all possible values of the source.
Alternatively the X'Valid (or X'Valid_Scalars for composite types) may
be used to determine the validity of an object.

The use of invalid values in a program (other than in a Valid, or Valid_Scalars
attribute) may invalidate any proofs performed on the program.

.. todo:: Introduce checks for data validity into the proof model as necessary.
          To be completed in a post-Release 1 version of this document.

Unchecked Access Value Creation
-------------------------------

.. centered:: **Legality Rules**

.. _tu-unchecked_access_value_creation-01:

1. The Unchecked_Access attribute is not in |SPARK|.

.. _etu-unchecked_access_value_creation:

Storage Management
------------------

.. centered:: **Legality Rules**

.. _tu-storage_management-01:

1. Aspect specifications for the Storage_Pool and Storage_Size aspects
are not in |SPARK|, nor are uses of the corresponding attributes.
The predefined unit System.Storage_Pools is not in |SPARK|, nor is
any other predefined unit that semantically depends on it. The pragma
Default_Storage_Pool is not in SPARK.

.. _etu-storage_management:

Pragma Restrictions and Pragma Profile
--------------------------------------

Restrictions and Profiles will be available with |SPARK| to provide profiles
suitable for different application environments.

Streams
-------

.. centered:: **Legality Rules**

.. _tu-streams-01:

1. Stream types and operations are not in |SPARK|.

.. _etu-streams:

Freezing Rules
--------------

No restrictions or additions.
