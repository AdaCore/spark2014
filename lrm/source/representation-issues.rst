Representation Issues
=====================

.. todo:: Provide full detail on Representation Issues.
          To be completed in the Milestone 4 version of this document.
          
.. todo:: This statement was originally in this chapter 
     "Pragma or aspect ``Unchecked_Union`` is not in |SPARK|" this needs to be 
     recorded in the list of unsupported aspects and pragmas.
          
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

The use of the operators defined for type Address are not permitted in |SPARK| 
except for use within representation clauses. 

Machine Code Insertions
-----------------------

Machine code insertions are not in |SPARK|.

Unchecked Type Conversions
--------------------------

An instantiation of an Unchecked_Conversion may have Refined_Pre and
Refined_Post aspects specified.

Data Validity
~~~~~~~~~~~~~

Currently |SPARK| does not check for data validity although SPARK 2005 did.

.. todo:: Need to put some words in here to describe the precautions that may
   be taken to avoid invalid data.
   
Unchecked Access Value Creation
-------------------------------

As access types are not supported in |SPARK|, neither is this attribute.

Storage Management
------------------

These features are related to access types and not in |SPARK|.

Pragma Restrictions and Pragma Profile
--------------------------------------

Restrictions and Priofiles will be available with |SPARK| to provide profiles 
suitable for different application environments.

Streams
-------

Stream types and operations are not in |SPARK|.

Freezing Rules
--------------

No restrictions or additions.



