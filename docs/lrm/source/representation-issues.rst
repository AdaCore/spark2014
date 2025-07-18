Representation Issues
=====================

Operational and Representation Aspects
---------------------------------------

|SPARK| defines several Boolean-valued aspects. These include the
Async_Readers, Async_Writers, Constant_After_Elaboration,
Effective_Reads, Effective_Writes, Extensions_Visible, Ghost,
Side_Effects and Volatile_Function aspects.
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
the address of another object ``Y``, using an address clause of the form ``with
Address => Y'Address``, then ``X`` is said to be overlaid on ``Y``. Both ``X``
and ``Y`` are said to be overlaid objects. The verification rules below impose
restrictions on overlaid objects in |SPARK|. Other address clauses and aspects
are not restricted; the onus is on the user to ensure that this is correct with
respect to the program semantics of |SPARK|.

.. container:: heading

   Legality Rules

1. The use of the operators defined for type Address are not permitted
   in |SPARK| except for use within representation clauses.

.. container:: heading

   Verification Rules

2. If an object ``X`` is overlaid on an object ``Y``, then the sizes of ``X``
   and ``Y`` shall be known at compile-time and shall be equal.

3. If an object ``X`` is overlaid on an object ``Y``, then the alignment of
   ``Y`` shall be an integral multiple of the alignment of ``X``.

4. If an object ``X`` is overlaid on an object ``Y``, ``Y`` shall be suitable
   as the source for unchecked conversion (see
   :ref:`Unchecked Type Conversions`); if it is mutable in SPARK, it shall also
   be suitable as the target of an unchecked conversion.
   The overlaid object ``X`` shall be suitable for unchecked
   conversion. If it is not annotated with the aspect `Potentially_Invalid`, it
   shall also be suitable as the target of an unchecked conversion. Moreover,
   if it is mutable in SPARK, it shall also be suitable as the source of an
   unchecked conversion.
   [A constant overlay is similar to an unchecked conversion from the object
   mentioned in the address clause to the object with the address clause. A
   variable overlay is a bidirectional unchecked conversion.]

5. If the address clause of an object ``X`` is not of the form ``with Address
   => Y'Address`` for some object ``Y``, then ``X`` shall be volatile.

6. If the address of an object ``Y`` is taken other than in an address clause
   of the form ``with Address => Y'Address``, then ``Y`` shall be volatile.

7. If an object ``X`` overlays an object ``Y``, then neither ``X`` nor ``Y``
   shall be constituents of an abstract state.

Machine Code Insertions
-----------------------

.. container:: heading

   Legality Rules

1. Machine code insertions are not in |SPARK|.


Unchecked Type Conversions
--------------------------

A subtype ``S`` is said to be `suitable for unchecked conversion` if:

- ``S`` is not of a tagged type, of an access type, of an immutably
  limited type, or of a private type whose
  completion fails to meet these requirements.

- if ``S`` is a composite type, all components of ``S`` are also suitable for
  unchecked conversion.

A subtype ``S`` is said to be `suitable as the source of an unchecked
conversion` if it is suitable for unchecked conversion, and, in addition:

- if ``S`` is a floating-point type, its Size is not greater than the Size of
  the largest floating-point type on the target.

- if ``S`` is a scalar type that is not a floating-point type, its Size is not
  greater than the Size of the largest integer type on the target.

- if ``S`` is a composite type, the Size N of ``S`` is the sum of the Size of
  the components of ``S``, and all components of ``S`` are also suitable as the
  source for unchecked conversion.

[Sources of unchecked conversion shall not have unused bits.
Limits on the Size of scalar types are meant to allow the compiler to zero out
extra bits not used in the representation of the scalar value, when writing a
value of the type (as GNAT ensures).]

A subtype ``S`` is said to be `suitable as the target of an unchecked
conversion` if it is suitable for unchecked conversion, and, in addition:

- ``S`` is not of a subtype that is subject to a predicate, or of a type
  that is subject to a type invariant.
- Given the Size N of ``S`` in bits, there exist exactly 2**N distinct
  valid values that belong to ``S`` and contain no invalid scalar parts.  [In
  other words, every possible assignment of values to the bits representing an
  object of subtype ``S`` represents a distinct value of ``S``.]
- If ``S`` is a composite type, all parts of ``S`` are also suitable as the
  target of an unchecked conversion.

[Note that floating-point types are not suitable as the target of an unchecked
conversion, because NaN is not considered to be a valid value.]

Unchecked type conversions are in |SPARK|, with some restrictions described
below. Although it is not mandated by Ada standard, the compiler should ensure
that it does not return the result of unchecked conversion by reference if it
could be misaligned (as GNAT ensures).

.. container:: heading

   Verification Rules

1. The source and target subtypes of an instance of ``Unchecked_Conversion``
   shall have the same Size.

2. The source subtype shall be suitable as the source of an unchecked
   conversion.

3. The target subtype should be suitable for unchecked conversion and it
   should be suitable as the target of an unchecked
   conversion unless the instance of ``Unchecked_Conversion`` has the
   Potentially_Invalid aspect, see :ref:`Data Validity`.

.. index:: Potentially_Invalid

Data Validity
~~~~~~~~~~~~~

In general, |SPARK| rules ensure the only possible cases of invalid data in a
|SPARK| program come from interfacing with the external world, either through
the hardware-software or Operating Systems integration, or through interactions
with non-|SPARK| code in the same program. In this case, it is up to users to
ensure that data read from external sources are valid.

Validity can be ensured by using a type for the target of the data read from an
external source (or an unchecked type conversion when used to read data from
external source) which is sufficient to encompass all possible values of the
source. Alternatively the X'Valid (or X'Valid_Scalars for composite types) may
be used to help determine the validity of an object.

SPARK defines the aspect Potentially_Invalid. It can be used to identify objects
that might hold invalid values at subprogram boundary and functions that might
return invalid values. The use of invalid values coming from other external
sources in a program may invalidate any proofs performed on the program.

The Potentially_Invalid aspect may be specified for a standalone object or for a
subprogram or entry, where it effectively applies to one or more of its formal
parameters and the return object of a function.

.. container:: heading

   Static Semantics

1. An object is said to *be potentially invalid* if and only if

   * its Potentially_Invalid aspect is True; or

   * it is the return object of a function call and the Potentially_Invalid
     aspect of the function's result is True.

2. A Potentially_Invalid aspect specification for a formal parameter
   of a subprogram or entry or for a function's result is expressed syntactically
   as an aspect_specification of the declaration of the enclosing callable
   entity. In the following example, the parameter ``X1`` and the result of
   ``F`` are specified as potentially invalid; the parameters ``X2``
   and ``X3`` are not:

   .. code-block:: ada

      function F (X1 : T1; X2 : T2; X3 : T3) return T4
        with Potentially_Invalid => (X1, F'Result);

..

   More precisely, the Potentially_Invalid aspect for a subprogram or entry (or
   a generic subprogram) is specified by an ``aspect_specification`` where the
   ``aspect_mark`` is Potentially_Invalid and the ``aspect_definition`` has
   the following grammar for ``profile_aspect_spec``:

   ::

      profile_aspect_spec ::= ( profile_spec_item {, profile_spec_item} )
      profile_spec_item   ::= parameter_name [=> aspect_definition]
                            | function_name'Result [=> aspect_definition]

3. As a special case, a Potentially_Invalid aspect specification for the result
   of an instance of Ada.Unchecked_Conversion is expressed syntactically as an
   aspect_specification of the generic instantiation:

   .. code-block:: ada

      function F is new Ada.Unchecked_Conversion (T1, T2) with
        Potentially_Invalid;

.. container:: heading

   Legality Rules

4. The following rules apply to the profile_aspect_spec of a Potentially_Invalid
   aspect specification for a subprogram, a generic subprogram, or an entry.

   * Each parameter_name shall name a parameter of the given subprogram or
     entry and no parameter shall be named more than once. It is not required
     that every parameter be named.

   * Each aspect_definition within a profile_aspect_spec shall be as for a
     Boolean aspect.

   * The form of profile_spec_item that includes a Result attribute reference
     shall only be provided if the given subprogram or entry is a function or
     generic function; in that case, the prefix of the attribute reference shall
     denote that function or generic function. Such a Result attribute reference
     is allowed, other language restrictions on the use of Result attribute
     references notwithstanding (i.e., despite the fact that such a
     Result attribute reference does not occur within a postcondition
     expression).

   * A parameter or function result named in the aspect_specification shall not
     be of a scalar type, except for the result of an imported function.
     [It is a bounded error to pass an invalid scalar parameter as input for an
     input parameter or as output for an output parameter or function result, so
     there is no benefit of marking such a parameter or result as being
     potentially invalid.]

   * A Boolean value of True is implicitly specified if no aspect_definition
     is provided, as per Ada RM 13.1.1's rules for Boolean-valued aspects.
     A Boolean value of False is implicitly specified if a given parameter
     (or, in the case of a function or generic function, the result) is not
     mentioned in any profile_spec_item.

5. No part of an object or function result annotated with Potentially_Invalid
   shall be of an access type, a tagged type, a concurrent
   type, or an Unchecked_Union type.

6. No object marked Part_Of an abstract state or a concurrent object shall be
   potentially invalid.

7. No part of an object or function result annotated with Potentially_Invalid
   shall be subject to a type invariant.

8. An overlaid object shall not be potentially invalid.

9. A formal parameter of a dispatching operation shall not be potentially
   invalid; the result of a dispatching function shall not be potentially
   invalid.

.. container:: heading

   Verification Rules

10. At the point of a read of a non-discriminant subcomponent X of an object
    or function result that is potentially invalid, a verification condition is
    introduced to ensure that X is a valid value of its type, except if the read
    occurs either:

    * as the prefix of a component selection, indexed component, or array slice,

    * as the expression of a return statement of a function with the
      Potentially_Invalid aspect,

    * as the input value of an actual parameter [of mode **in** or **in out**]
      in a call whose corresponding formal has the Potentially_Invalid aspect,

    * as the expression of the declaration of a potentially invalid object,

    * as the expression of an assignment statement into a subcomponent of a
      potentially invalid object,

    * as the output value of an actual parameter that is a subcomponent of a
      potentially invalid object, or

    * as the prefix of a reference to the attributes Length, First, Last, Size,
      Object_Size, and Valid.

    When a subprogram returns normally or propagates an exception, all its
    parameters and global ouputs are considered to be read for the purpose of
    this rule.

Unchecked Access Value Creation
-------------------------------

.. container:: heading

   Legality Rules


1. The Unchecked_Access attribute is not in |SPARK|.


Storage Management
------------------

.. container:: heading

   Legality Rules


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

.. container:: heading

   Legality Rules


1. Stream types and operations are not in |SPARK|.


Freezing Rules
--------------

No restrictions or additions.
