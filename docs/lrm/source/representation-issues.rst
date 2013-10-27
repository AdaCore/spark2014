Representation Issues
=====================

.. todo:: Provide full detail on Representation Issues.
          To be completed in a post-Release 1 version of this document.
          
          
Operational and Representation Aspects
---------------------------------------

No restrictions or additions.


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

1. As access types are not supported in |SPARK|, neither is this attribute.

.. _etu-unchecked_access_value_creation:

Storage Management
------------------

.. centered:: **Legality Rules**

.. _tu-storage_management-01:

1. These features are related to access types and not in |SPARK|.

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



