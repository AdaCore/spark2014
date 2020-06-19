Representation Issues
=====================

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

Direct manipulation of addresses is restricted in |SPARK|. In particular, the
use of address clauses or aspects to define the address of an object in memory
is restricted in |SPARK|. If the address of an object ``X`` is specified to be
the address of another object ``Y``, then ``X`` is said to overlay ``Y``. Both
``X`` and ``Y`` are said to be overlaid objects. The verification rules below
impose restrictions on overlaid objects in |SPARK|. Other address clauses and
aspects are not restricted; the onus is on the user to ensure that this is
correct with respect to the program semantics of |SPARK|.

.. centered:: **Legality Rules**

1. The use of the operators defined for type Address are not permitted
   in |SPARK| except for use within representation clauses.

.. centered:: **Verification Rules**

2. If an object ``X`` overlays an object ``Y``, then the sizes of ``X`` and
   ``Y`` shall be known at compile-time and shall be equal.

3. If an object ``X`` overlays an object ``Y``, then the alignment of ``X``
   shall be an integral multiple of the alignment of ``Y``.

4. The type of an overlaid object shall be suitable for unchecked conversion
   (see :ref:`Unchecked Type Conversions`);

Machine Code Insertions
-----------------------

.. centered:: **Legality Rules**

1. Machine code insertions are not in |SPARK|.


.. _Unchecked Type Conversions:

Unchecked Type Conversions
--------------------------

A subtype ``S`` is said to be `suitable for unchecked conversion` if:

- ``S`` has a contiguous representation. No part of ``S`` is of a tagged type,
  of an access type, of a subtype that is subject to a predicate, of a type
  that is subject to a type_invariant, of an immutably limited type, or of a
  private type whose completion fails to meet these requirements.

- Given the size N of ``S`` in bits, there exist exactly 2**N distinct values
  that belong to ``S`` and contain no invalid scalar parts.  [In other words,
  every possible assignment of values to the bits representing an object of
  subtype ``S`` represents a distinct value of ``S``.]

Unchecked type conversions are in |SPARK|, with some restrictions described
below. Although it is not mandated by Ada standard, the compiler should ensure
that it does not return the result of unchecked conversion by reference if it
could be misaligned (as GNAT ensures).

.. centered:: **Verification Rules**

1. The source and target subtypes of an instance of ``Unchecked_Conversion``
   shall have the same size.

2. The source and target subtypes shall be suitable for unchecked conversion.

.. _data_validity:

Data Validity
~~~~~~~~~~~~~

|SPARK| rules ensure the only possible cases of invalid data in a |SPARK|
program come from interfacing with the external world, either through the
hardware-software or Operating Systems integration, or through interactions
with non-|SPARK| code in the same program. In particular, it is up to users to
ensure that data read from external sources are valid.

Validity can be ensured by using a type for the target of the data read from an
external source (or an unchecked type conversion when used to read data from
external source) which is sufficient to encompass all possible values of the
source.  Alternatively the X'Valid (or X'Valid_Scalars for composite types) may
be used to help determine the validity of an object.

The use of invalid values in a program (other than in a Valid, or Valid_Scalars
attribute) may invalidate any proofs performed on the program.

Unchecked Access Value Creation
-------------------------------

.. centered:: **Legality Rules**


1. The Unchecked_Access attribute is not in |SPARK|.


Storage Management
------------------

.. centered:: **Legality Rules**


1. Aspect specifications for the Storage_Pool and Storage_Size aspects
are not in |SPARK|, nor are uses of the corresponding attributes.
The predefined unit System.Storage_Pools is not in |SPARK|, nor is
any other predefined unit that semantically depends on it. The pragma
Default_Storage_Pool is not in SPARK.


Pragma Restrictions and Pragma Profile
--------------------------------------

Restrictions and Profiles will be available with |SPARK| to provide profiles
suitable for different application environments.

Streams
-------

.. centered:: **Legality Rules**


1. Stream types and operations are not in |SPARK|.


Freezing Rules
--------------

No restrictions or additions.
