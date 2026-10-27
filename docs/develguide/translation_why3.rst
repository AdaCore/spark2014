###################
Translation to Why3
###################

..
   devguide-meta:
   covers: Ada to Why3 encoding choices, generated declarations, and modeling
   decisions
   primary_code: gnat2why/, src/why/
   when_to_read: changes to Why3 translation, type modeling, expression
   encoding, or generated Why3 structure

*************************
Content of the Why3 files
*************************

This section describes the generated Why3 declarations and the modeling
decisions behind them. Counterexample-specific metadata is described in
:doc:`counterexamples`.

Modules for Entities
====================

The generated modules describe the types, objects, and subprograms needed for
verification of the current unit. This includes entities from dependency units
and nested scopes, not just the entities selected for verification. A callee's
declaration and contracts, for example, contribute to a caller's proof context
even when the callee's body is not being verified in this invocation.

Proof does not follow Ada's privacy rules when choosing a model for a type. By
default, it uses the most precise view available in SPARK, including private
completions in the specifications of dependency units. The full view serves as
a default model for the type: without it, proofs would be much less precise and
users would have to supply their own models. The same visibility allows proof
to use completions of deferred constants and private expression functions.
Selection of a type's SPARK view is handled by ``Retysp`` in
:file:`src/spark/spark_util-types.adb`.

For example, consider this package:

.. code-block:: ada

   package P with SPARK_Mode is
      type T is private;
      C : constant T;
      function Get (X : T) return Integer;
   private
      type T is record
         F : Integer;
      end record;
      C : constant T := (F => 1);
      function Get (X : T) return Integer is (X.F);
   end P;

A client cannot name ``F`` in Ada, but its proof context contains the record
model, the value of ``C``, and the definition of ``Get``. It can therefore prove
``P.Get (P.C) = 1`` without a user-written model or postcondition.

The placement of expression function bodies gives users control over what is
available to proofs outside the package. A definition in the private part is
available to client proofs even though Ada clients cannot see it. Moving the
definition to the package body hides it from those proofs, while leaving the
declaration and any visible contract available. In this example, moving the
completion of ``Get`` to the package body would hide its definition without
hiding the record model for ``T`` or the value of ``C``.

The default visibility can be restricted by ``Hide_Info`` annotations. A
``SPARK_Mode (Off)`` boundary also prevents use of the hidden implementation:
placing that pragma immediately after ``private`` in this example leaves the
client with an abstract view of ``T`` and no definition of ``C`` or ``Get``.
The equality then cannot be deduced from the remaining declarations alone.

Global effects must still be represented when their objects are opaque to proof,
for example an abstract state or an object outside SPARK. Such objects receive
abstract declarations recording their identity and effects without exposing an
internal structure; see :ref:`Effect-Only Objects`.

Generating these contextual declarations is separate from generating
verification conditions. When proving a client of ``P``, GNATprove includes the
model of ``P.T`` and declarations for ``P.C`` and ``P.Get`` in the client's proof
context. Including them does not mean that ``P.Get``'s body is verified during
that analysis: independent checks are generated for selected entities in the
analyzed unit. Local subprograms analyzed only in their calling contexts need
not have an independent verification module. Marking collects the entities used
by translation;
``Translate_CUnit`` in :file:`src/why/gnat2why-driver.adb` separates declaration,
completion, and check generation.

Types
-----

A type can give rise to several modules, depending on its representation and
the features it uses. These modules introduce types and symbols, supply
completion axioms, or isolate features such as invariants, equality, and default
initialization. Additional modules may describe initialization wrappers,
validity, or reclamation tracking. There is no fixed set of modules generated
for every type, and some representations are shared between types.

Separating declarations from their completions allows symbols to be introduced
before definitions that depend on them. For example, a type predicate or
invariant may call a function declared after the type. Separate modules also
allow definitions to be excluded from verification contexts where using them
would introduce circular reasoning, as discussed under Type Completion.

The ``Module_Kind`` enumeration and ``E_Module`` in
:file:`src/why/why-atree-modules.ads` identify the roles of entity modules. The
enumeration also includes modules for other entities; the checks in
``E_Module``'s body describe which kinds apply to which entities. The following
sections explain the design reasons for the type-related modules.

Common Features
^^^^^^^^^^^^^^^

The following sections describe common mechanisms used in type translation.

References and Havoc
""""""""""""""""""""

Why3 values are generally immutable. Why3 also supports mutable structures,
such as records with mutable fields, but mutable values cannot be stored in
logic types such as maps. Using mutable structures directly would therefore
make it difficult to combine the encodings of Ada types, for example an array
of records.

The translation instead keeps data immutable and stores mutable state in
references to that data. Instead of using Why3's polymorphic ``ref`` type, it
generates monomorphic record types with a single mutable field. Most target
solvers do not support polymorphism. Monomorphizing a polymorphic representation
introduces additional overhead in the proof context that can severely degrade
prover performance; generating monomorphic references directly avoids that
overhead.

For a value type ``t``, the reference has the following form:

.. code-block:: whyml

    type t__ref = { mutable t__content : t }

Updating a record field constructs a new immutable record value and assigns
the whole value to the reference. The other fields keep their previous values.
Why3's record update syntax expresses this directly. If ``t`` is a record type
with a field ``f``, updating that field to ``v`` takes the following form:

.. code-block:: whyml

    x.t__content <- { x.t__content with f = v }

An Ada object may be split into several parts, each represented separately;
see :ref:`Objects`. The same update principle applies to each mutable part.

Havoc models an update whose new value is unknown. It uses an ``any`` expression:

.. code-block:: whyml

    any unit writes {x}

The ``writes`` clause allows
the contents of ``x`` to change, while the absence of a postcondition leaves
the new value unconstrained apart from its Why3 type.

This operation is used before passing an ``out`` parameter with relaxed
initialization. The parameter must be allowed to be uninitialized on entry to
the callee, even if the actual parameter is initialized before the call.
Havoc forgets the previous contents and initialization information in the
reference used for the parameter. It does not assume the dynamic invariant of
the parameter.

Reference declarations can be reused when type encodings reuse an existing
representation. The declaration helpers and naming conventions are documented
in :file:`src/why/why-gen-decl.ads`; the rules for generating or reusing these
declarations are in ``Generate_Ref_Type`` in
:file:`src/why/gnat2why-types.adb`.

Predefined / primitive equality
"""""""""""""""""""""""""""""""

For non-scalar Ada types, we introduce an equality function named ``bool_eq``
for predefined equality. Equality on scalar types is handled separately;
see :ref:`Scalar Types`.

Predefined equality of composite types uses primitive equality to compare
components of record or inherently limited types. Primitive equality is the
predefined equality unless the user has supplied a replacement. When there is
a replacement, we declare a separate function named ``user_eq`` for it.
The enclosing composite type's ``bool_eq`` then uses the component type's
``user_eq`` rather than its ``bool_eq``
(see ``Why.Gen.Expr.New_Ada_Equality``). Keeping these functions separate
preserves the distinction between predefined and primitive equality.

Ada equality cannot in general be replaced by Why3's built-in equality.
For example, predefined record equality uses the appropriate Ada equality
for each component, which may itself be user-defined. The two records can
therefore compare equal without having identical Why3 values.

When it is declared, the boolean equality ``bool_eq`` is given a
definition depending on the kind of the type. Here is for example the
equality which would be generated for a record type with a single ``F``
component of type ``Integer``:

.. code-block:: whyml

    function bool_eq (a : t) (b : t) : bool =
      Standard__integer__rep.to_rep a.__split_fields.rec__t__f =
      Standard__integer__rep.to_rep b.__split_fields.rec__t__f

It simply states that two records are equal when their ``F`` components
are equal.

As for the user-defined primitive equality, it is declared with no
definition. During type completion, an axiom links it to the user-defined
equality when that equality is available in SPARK. Otherwise it remains
abstract:

.. code-block:: whyml

    function user_eq (a : t) (b : t) : bool

Dummy values
""""""""""""

Type encodings provide a dummy value to fill fields that do not represent
an Ada value in the current object:

.. code-block:: whyml

    function dummy : t

Examples are inactive record components and the designated-value field of a
null access value. Dummy values are placeholders in the encoding, not Ada
default initialization values. The record model and its tradeoffs are explained
under :ref:`Logical equality and inactive components`.

Scalar Types
^^^^^^^^^^^^

All scalar types have a representative type, which is the Why type used
to represent this scalar type. It differs depending on the kind of
scalar type which is declared. Scalar types also have a more complete
form, which includes additional constraints (bounds, modulus etc).
These closed forms are only used for objects which are stored inside
data structures, to avoid the need for complex invariants whenever
possible.

The two forms are linked by ``to_rep`` and ``of_rep``. The first exposes
the representative value of a closed value. The second constructs a closed
value from a representative value. Their axioms guarantee that converting a
closed value to its representative and back preserves it, and that every
closed value satisfies the type's range constraint. Converting a representative
value to the closed form and back preserves it only under the range condition;
modular conversion also reduces the value modulo the modulus.

These conversions do not replace Ada range checks. The translation must check
the relevant constraint when an Ada operation requires it. The conversion
functions and their axioms are kept in a separate module, which is only included
when the conversions are used. This improves solver performance by keeping the
proof context smaller when the conversions are not needed.

Predefined equality on scalar types compares values of the corresponding
representative types.

Except for floating-point types, this comparison uses Why3's built-in logical
equality. Logical equality means that the two values are the same: one can
replace the other in any logical expression. This matches predefined equality
for integers, modular integers, enumerations, and fixed-point types, whose
representations preserve this notion of equality.

Floating-point equality uses the float model's equality operation instead.
For example, positive and negative zero compare equal, but they are distinct
values and their signs can affect later operations. They cannot be freely
substituted for each other. Using logical equality for this comparison would
therefore give the proof incorrect assumptions.

We first explain how static non-empty scalar types are translated into
Why3, going over each kind of type individually. Dynamic (and
statically empty) types are handled a bit differently, this is
explained afterwards (see ``Gnat2why.Util.Type_Is_Modeled_As_Base`` for the
exact check).

Signed Integer Types
""""""""""""""""""""

The representative type for signed integer types is mathematical
integers. Indeed, solvers have powerful tactics to reason about linear
arithmetic and comparison operators on mathematical integers.
Arithmetic operations and comparisons on signed integer are
translated as operations on mathematical integers so that GNATprove
can benefit from this support.

The closed form of a static signed integer represents exactly the
range of the Ada type. It is encoded using a Why3 range type with
an of_rep function to convert from mathematical
integers as well as a range axiom.

As an example, let us look at the following type:

.. code-block:: ada

   type Signed_Int is range 1 .. 10;

Here are the relevant axioms and declarations generated in Why3 for it.
Here we inline the clones that are used to share declarations in Why3:

.. code-block:: whyml

    module P__signed_int
     use import "int".Int

     type signed_int = < range 1 10 >

     function first : int = 1

     function last : int = 10

     predicate in_range (x : int)  = (first <= x <= last)

     ...
    end

    module P__signed_int__rep
     use import "int".Int
     use import P__signed_int

     function to_rep (x : signed_int) : int = signed_int'int x
     function of_rep int : signed_int

     axiom inversion_axiom :
	forall x : signed_int [to_rep x].
	  of_rep (to_rep x) = x

     axiom range_axiom :
	forall x : signed_int [to_rep x]. in_range (to_rep x)

     axiom coerce_axiom :
	forall x : int [to_rep (of_rep x)].
	  in_range x -> to_rep (of_rep x) = x
    end

The range, inversion, and coerce axioms enforce that there is exactly
one element in the closed form of a signed integer type per
mathematical integer between first and last. These modules are
generated respectively by Why.Gen.Scalars.Declare_Scalar_Type and
Why.Gen.Scalars.Define_Scalar_Rep_Proj.

GNAT's ``Unsigned_Base_Range`` extension gives an integer type an unsigned
base range. Although the frontend represents these types internally as modular
types, their arithmetic has integer semantics with overflow checks. GNATprove
models this arithmetic with mathematical integers and checks matching GNAT's
selected overflow mode; minimized mode uses the range of ``Long_Long_Unsigned``.

Modular Integer Types
"""""""""""""""""""""

Modular integer types are normally represented in Why as bit-vectors (machine
integers). More precisely, their representative type is the smallest
bit-vector in which they fit (we use bit-vectors of size 8, 16,
32, 64, or 128). Indeed, some backend solvers can handle bitwise
operations such as shift or rotate directly on bit-vectors.
They also handle wrap-around
semantics of operators natively. Solvers can sometimes be more precise
about non-linear arithmetic on bit-vectors, especially on small
bit-vectors.

The ``No_Bitwise_Operations`` annotation selects a mathematical-integer
representation instead. Marking then rejects bitwise operations on the type.
Modular arithmetic still reduces results modulo the Ada modulus.

Operations on modular types are generally translated as operations on
bit-vectors, followed by a reduction modulo the specified modulus when
necessary. However, when the type has a modulus which is not a power
of two, care must be taken to do the computation in a type big enough
to avoid wrap-around in the representative type. To this aim,
operations are usually done in a bigger bit-vector when the modulus is
not a power of two. For power, we even go to mathematical integers
since no bit-vector type is big enough.

As for signed integers, the closed form of a static modular type
contains exactly the values that are allowed by the modulus and the
range if any. The closed form is linked to the representative type
using a range predicate, as well as of_rep and to_rep functions to
convert to and from bit-vectors. As an example, let us look at the
following type:

.. code-block:: ada

   type Modular_Int is mod 500;

Here are the axioms and declarations generated in Why for it. Like for
signed integer types, we only give here the relevant declarations and
to_rep and of_rep functions are separated in a different module:

.. code-block:: whyml

     type modular_int

     function attr__ATTRIBUTE_MODULUS : BV16.t =
      (BV16.of_int 500)

     function first : BV16.t = BV16.of_int 0

     function last : BV16.t = BV16.of_int 499

     predicate in_range (x : BV16.t) = (BV16.ule first x /\ BV16.ule x last)

     function to_rep modular_int : BV16.t
     function of_rep BV16.t : modular_int

     axiom inversion_axiom :
	forall x : modular_int [to_rep x].
	  of_rep (to_rep x) = x

     axiom range_axiom :
	forall x : modular_int [to_rep x]. in_range (to_rep x)

     axiom coerce_axiom :
	forall x : BV16.t [to_rep (of_rep x)].
	  let y = BV16.urem x attr__ATTRIBUTE_MODULUS in
	    in_range y -> to_rep (of_rep x) = y

Like for signed integers, the inversion, range, and coerce axiom
ensure that there is exactly one element in the closed form of a
modular integer per element between first and last. The coerce axiom
ensures that modular values are always considered up to the modulus
attribute.

Since background solvers are often bad at converting between
bit-vectors and mathematical integers, we also provide a range
predicate and a range axiom speaking about the mathematical integer
representation of bit-vectors. It is useful when modular integer types
happen to be converted to signed integer types, or to be compared to
some attributes of universal integer types such as array length:

.. code-block:: whyml

     function first_int : int = 0

     function last_int : int = 499

     predicate in_range_int (x : int) = (first_int <= x <= last_int)

     function to_int (x : modular_int) : int = BV16.t'int (to_rep x)

     axiom range_int_axiom :
	forall x : modular_int [to_int x]. in_range_int (BV16.t'int (to_rep x))

Enumerations
""""""""""""

Enumerations are translated just like signed integer types. The
specific names of enumerated values do not even appear in the
generated Why code. They are directly translated as their position
(see ``Gnat2why.Expr.Transform_Enum_Literal``). A notable exception to
this scheme are standard boolean types (see Is_Standard_Boolean_Type)
for which no new theory is introduced and which are translated
directly as booleans in Why.

Floating Point Types
""""""""""""""""""""

The representative type of an Ada floating point type is a machine
floating point type of the corresponding format (32, 64, or 80 bits).
Background solvers which support floating point numbers abide by the
IEEE 754 standard. GNATprove requires the Ada program to use IEEE 754
floating-point behavior. Operations on floating point numbers in Ada are
translated using the corresponding built-in operations in solvers under
this assumption.

Then, like for integer types, a closed form is defined for static
floating point types which only allows numbers in the specified range.

As an example, let us look at the following type:

.. code-block:: ada

   type Floating_Point is digits 6 range 0.0 .. 100.0;

Here are the axioms and declarations generated in Why for it. Like for
signed integer types, we only give here the relevant declarations and
to_rep and of_rep functions are separated in a different module:

.. code-block:: whyml

     type floating_point

     function first : Float32.t = (0.0:Float32.t)

     function last : Float32.t = (100.0:Float32.t)

     predicate in_range (x : Float32.t)  =
      (Float32.t'isFinite x) && (Float32.le first x /\ Float32.le x last)

     function to_rep floating_point : Float32.t
     function of_rep Float32.t : floating_point

     axiom inversion_axiom :
	forall x : floating_point [to_rep x].
	  of_rep (to_rep x) = x

     axiom range_axiom :
	forall x : floating_point [to_rep x]. in_range (to_rep x)

     axiom coerce_axiom :
	forall x : Float32.t [to_rep (of_rep x)].
	  in_range x -> to_rep (of_rep x) = x

Fixed Point Types
"""""""""""""""""

A value of fixed point types is translated as an integer, the represented value
being the product of the small of the fixed point type with this value. To avoid
confusion, we use an alias of int named ``__fixed``. Apart from that, static fixed
point types are translated as static integer types, with a range, conversion
functions and coerce and range axioms. For example, let us consider the
following type:

.. code-block:: ada

   type My_Fixed is delta 3.0 / 1000.0 range 0.0 .. 3.0
     with Small => 1.0 / 512.0;

Here are the axioms and declarations generated in Why for it. Like for
integer types, we only give here the relevant declarations and
to_rep and of_rep functions are separated in a different module:

.. code-block:: whyml

 type my_fixed

 function num_small
   : Main.__fixed =
  1

 function den_small
   : Main.__fixed =
  512

 function first
   : Main.__fixed =
  0

 function last
   : Main.__fixed =
  1536

 predicate in_range
   (x : Main.__fixed)  =
  ( (first <= x) /\ (x <= last) )

  function to_rep my_fixed : Main.__fixed

  function of_rep Main.__fixed : my_fixed

  axiom range_axiom :
    forall x : my_fixed. in_range (to_rep x)

  axiom inversion_axiom :
    forall x : my_fixed [to_rep x].
      of_rep (to_rep x) = x

  axiom coerce_axiom :
    forall x : Main.__fixed [to_rep (of_rep x)].
      in_range x -> to_rep (of_rep x) = x

Operations on values of a fixed point type depend on the value of the small
of the type. Types with the same small share a module defining these operations.
As an example, here is part of the module introduced for fixed point types of
small 1 / 512 like My_Fixed above:

.. code-block:: whyml

 module Fixed_Point__1_512

   function num_small : int = 1

   function den_small : int = 512

   (* multiplication between a fixed-point value and an integer *)

   function fxp_mult_int (x : __fixed) (y : int) : __fixed = x * y

   function fxp_div_int (x : __fixed) (y : int) : __fixed

   val fxp_div_int_ (x : __fixed) (y : int) : __fixed
     requires { y <> 0 }
     ensures { result = fxp_div_int x y }

   axiom fxp_div_int_def :
     forall x : __fixed, y : int [fxp_div_int x y].
       if x = 0 then
         fxp_div_int x y = 0
       else if x > 0 /\ y > 0 then
         pos_div_relation (fxp_div_int x y) x y
       else if x < 0 /\ y < 0 then
         pos_div_relation (fxp_div_int x y) (-x) (-y)
       else if x < 0 /\ y > 0 then
         pos_div_relation (- (fxp_div_int x y)) (-x) y
       else if x > 0 /\ y < 0 then
         pos_div_relation (- (fxp_div_int x y)) x (-y)
       else (* y = 0 *)
         true

  ...

  end

Note that, in the Why generated code, the type system is not used to ensure
that we always use the correct operation for fixed point types. The translator
must select the module for the correct small. Multiplication and division
between fixed-point types also depend on the smalls of the arguments and result.

A subtlety of operations on fixed-point types is that multiplication and
division involving fixed-point arguments are defined in Ada standard over a
`universal` fixed-point type. The precise semantics for such operations is
defined in Annex G.2.3 of the Ada standard. It differentiates between
operations that are `precise` and those that are not, where being precise means
that the result is one of two values that correspond to the rounded fixed-point
values of the mathematical result.

GNATprove only supports operations that are precise in this sense, and the
uncertainty concerning the direction of rounding is conveyed in predicate
``pos_div_relation``. Operations that are not precise are rejected during
marking. Note that conversions between fixed-points and integers follow the
same pattern, with a slight difference: conversion from fixed-point to integer
always rounds to nearest with ties resolved in the direction away-from-zero
(Ada RM 4.6(33)). This is conveyed in predicate
``pos_div_relation_round_away``.

For example, dividing a fixed-point value represented by 5 by the integer 3
can produce a value represented by 1 or 2. With a value represented by -5,
the possible results are -2 and -1. If the mathematical result is exactly
representable, the model requires that result. Otherwise, the model allows
both neighboring values rather than choosing a rounding direction
that Ada does not require. Division by zero is excluded by a separate check.

The full sign cases and rounding predicates are defined in
``Fixed_Point_Rep`` and ``Fixed_Point_Shared`` in
:file:`share/spark/theories/ada__model.mlw`.

Dynamic scalar types
""""""""""""""""""""

When scalar types have dynamic bounds, or when they are statically
empty, no new closed type is generated for them. Instead, their closed
view is set to the closed view of their base type. Otherwise, the
translation is unchanged, except that first and last bounds can be
functions with parameters instead of constants if their values depend on
variables. As a result, the range predicate is replaced by a
``dynamic_property`` predicate, which takes the current value of first and last as
additional parameters.

Additionally, as no new closed type is generated for them, dynamic
scalar types do not have a specific module for projection to the
representative type (of_rep and to_rep and related axioms), but rather
use the projections of their base type.

This specific translation is triggered when
``Gnat2why.Util.Type_Is_Modeled_As_Base`` returns ``True``. As an example, let
us look at the translation of the following signed integer type
declaration, where X is a non-static constant:

.. code-block:: ada

    subtype Dyn_Ty is Integer range 1 .. X;

Here is its translation into Why:

.. code-block:: whyml

    module P__dyn_ty
     use import "int".Int
     use    	Standard__integer
     use    	Standard__integer__rep

     type dyn_ty = Standard__integer.integer

     function first : int = 1

     function last : int

     predicate dynamic_property
	 (first_int : int) (last_int : int) (x : int)  =
      first_int <= x <= last_int

     function to_rep "inline" (x : dyn_ty) : int =
       Standard__integer__rep.to_rep x
     function of_rep "inline" (x : int) : dyn_ty =
       Standard__integer__rep.of_rep x
    end

Here we can see that, since the first bound is static, it is
translated directly as a constant in Why and its value is given at
declaration. The last bound is a constant too, as X is translated as a
constant in Why3, but it is not given a value here, as its value may
depend on other entities which have not been translated yet.

Instead, an axiom is generated in the types completion module to state
the actual value of Dyn_Ty last bound (see
``Gnat2why.Types.Generate_Type_Completion.Create_Axioms_For_Scalar_Bounds``):

.. code-block:: whyml

     axiom last__def_axiom : last = P__x.x

NB: Not generating a closed form for dynamic or statically empty
scalar types is important for soundness. Indeed, the of_rep function
cannot be defined if the closed form happens to be empty. Another
issue is that, if the first and last bounds of a scalar type depend on
variables, then the range predicate may change over time, so that the
range axiom may become unsound.

Array Types
^^^^^^^^^^^

An (n-dimensional) Ada array is translated in Why as an
(n-dimensional) functional map mapping representative values of the
array index types to closed values of the component type along with
values for index bounds. The map is defined over the whole index representation,
including values outside the array bounds. For example, consider the following
array type:

.. code-block:: ada

       type Modular_Int is mod 2 ** 16;
       type My_Matrix is array
	   (Positive range 1 .. 100,
	    Modular_Int range 1 .. 50) of Natural;

Objects of ``My_Matrix`` are translated as maps from pairs of a mathematical
integer and a bitvector of size 16 to natural closed form along with 4 static
bounds:

.. code-block:: whyml

     type map

     function get map int BV16.t : Standard__natural.natural
     function set map int BV16.t Standard__natural.natural : map

     function first : int = 1

     function last : int = 100

     function first_2 : BV16.t = BV16.of_int 1

     function last_2 : BV16.t = BV16.of_int 50

Representative Array Theories
"""""""""""""""""""""""""""""

To avoid polymorphism, specific theories are introduced for each kind
of functional map used in the program. To facilitate conversions between
array types, the same theory is reused whenever possible. A theory is shared
by arrays with the same representative index types and the same closed
component type. Each of the n index types is represented by a mathematical
integer or a bitvector of size 8, 16, 32, 64, or 128. The bounds are not part of
this choice: arrays with different bounds can use the same map type.
The sharing and naming conventions are documented in
:file:`src/why/why-gen-arrays.ads`.

As an example, declarations related to the map type for the My_Matrix
type presented above are all grouped in a module named
Array__Int_BV16__Standard__natural:

.. code-block:: whyml

    module Array__Int_BV16__Standard__natural
      type map

      function get map int BV16.t : Standard__natural.natural
      function set map int BV16.t Standard__natural.natural : map

      axiom Select_eq :
	forall m : map.
	forall i : int.
	forall j : BV16.t.
	forall a : Standard__natural.natural.
	      get (set m i j a) i j = a

      axiom Select_neq :
	forall m : map.
	forall i i2 : int.
	forall j j2 : BV16.t.
	forall a : Standard__natural.natural.
	not (i = i2 /\ j = j2) -> get (set m i j a) i2 j2 = get m i2 j2

      ...
    end

These declarations come from the abstract theory ``Array__2`` in
:file:`share/spark/theories/_gnatprove_standard.mlw`, cloned with the
appropriate index and component types. The shared theories are provided
for one to four dimensions, which is the current limit supported by
GNATprove.

Background solvers of GNATprove have theories for one dimensional
abstract maps (this theory is called theory of arrays). However, we have chosen
not to directly translate maps for arrays of dimension 1 to the built-in
Map type in Why to benefit from this support.
This is a trade-off, as, on the one hand, solvers are
usually more efficient on multiple consecutive updates of arrays when
using the theory, while, on the other hand, the built-in support may
hinder quantifier instantiation of universally quantified axioms
involving arrays.  Experiments showed that the additional complexity introduced
by having interpreted symbols in quantified axioms over arrays was not made up
for by the benefits of the encoding. As solvers are improving all the time, it
may have to be revisited at some point.

As a result of our encoding of arrays, Why3 values for Ada arrays contain
elements for out-of-bounds indexes. The predicate ``has_bounds`` is introduced
and maintained over arrays so that these elements do not prevent proof of
logical equality. It stands for the property that values outside the given
bounds are fixed. Intuitively, they contain a dummy value, as for inactive
record components (see :ref:`Logical equality and inactive components`);
the choice of that value does not matter.
An extensionality axiom allows Why3 to prove that two arrays with the same
bounds are logically equal if they agree on the value of elements within the
bounds:

.. code-block:: whyml

  predicate has_bounds map int int

  predicate eq_ext map map int int

  axiom eq_ext_def :
    forall a1 a2 : map, f l : int [eq_ext a1 a2 f l].
      eq_ext a1 a2 f l <-> a1 = a2

  axiom extensionality :
    forall a1 a2 : map, f l : int [eq_ext a1 a2 f l].
      a1 <> a2 -> has_bounds a1 f l -> has_bounds a2 f l ->
      exists i : int. f <= i <= l /\ get a1 i <> get a2 i

The predicate eq_ext here is only used to provide SMT solvers with a trigger
to apply the extensionality axiom. It is used to translate calls to functions
annotated with Logical_Equal over arrays.

This allows users to prove logical equality by comparing only elements within
the array bounds. Once logical equality is established, it gives congruence
for all logical functions: applying any such function to either array gives
the same result. Agreement within the bounds would not imply this if the maps
could still differ outside them.

This choice has a cost. ``has_bounds`` occurs in the dynamic invariant of array
values and must be maintained by array operations. Slicing can no longer be
translated as the identity on the map in general. The ``slice`` operation
preserves elements within the new bounds and produces a map whose values
outside those bounds are fixed. These costs are a trade-off for being able to
prove logical equality from the elements that users can access in Ada.

To reduce this cost, ``has_bounds`` is an abstract, uninterpreted predicate.
Its axioms give bounded extensionality and describe how array operations
establish or preserve the predicate, without defining the out-of-bounds values
explicitly. This limits the reasoning about those values required of solvers.

Operators on Maps
"""""""""""""""""

In addition to the usual get and set operations on maps, we also
introduce more complex operations that are used to model Ada
operations. The first one is an equality function which checks for
equivalence of elements using the appropriate Ada equality for the component
type (see :ref:`Predefined / primitive equality`). It only considers elements
within the array bounds and compares corresponding positions, even when the
lower bounds differ.

Here is the equality function introduced for My_Matrix:

.. code-block:: whyml

     function bool_eq (a : map) (a__first : int) (a__last : int)
		      (a__first_2 : BV16.t) (a__last_2 : BV16.t)
		      (b : map) (b__first : int) (b__last : int)
		      (b__first_2 : BV16.t) (b__last_2 : BV16.t) : bool =
	(if a__first <= a__last then
	      b__first <= b__last
	   /\ a__last - a__first = b__last - b__first
	 else b__first > b__last)
     /\ (if BV16.ule a__first_2 a__last_2 then
	      BV16.ule b__first_2 b__last_2
	   /\ BV16.sub a__last_2 a__first_2 =
	      BV16.sub b__last_2 b__first_2
	 else BV16.ugt b__first_2 b__last_2)
     /\ (forall x1  : int.
	(forall x2  : BV16.t.
	   (if a__first <= x1 <= a__last
	    /\ BV16.ule a__first_2 x2
	    /\ BV16.ule x2 a__last_2 then
	      to_rep (get a x1 x2) =
	       to_rep (get b ((b__first - a__first) + x1)
			(BV16.add (BV16.sub b__first_2 a__first_2) x2)))))

The function first states that the bounds given for each dimension of a
and b represent slices of the same length, and then that elements
at corresponding positions inside the slices are Ada equal. It is generated
for each map type by ``Declare_Equality_Function`` in
:file:`src/why/why-gen-arrays.adb`. This differs from logical equality, which
requires the same bounds and logically equal elements at the same indexes.

Unlike the equality function, other operations on maps are declared
via clones of static modules. The function slide shifts
all elements stored in a map by a given offset in each dimension. The
offsets are given by two positions per dimension, which stand
for the old and the new value of the first index of the Ada array. As
an example, here is the slide function defined for My_Matrix:

.. code-block:: whyml

      function slide map int int BV16.t BV16.t : map

      axiom slide_def :
	forall a : map.
	forall new_first    old_first   : int.
	forall new_first_2  old_first_2 : BV16.t.
	forall i : int.
	forall j : BV16.t.
	  get (slide a old_first new_first old_first_2 new_first_2) i j =
	    get a (i - (new_first - old_first))
		  (BV16.sub j (BV16.sub new_first_2 old_first_2))

This excerpt shows the element-preservation part of the defining axiom.
Each element of the shifted array is logically equal to the corresponding
element in the input array. Sliding models the positional correspondence
required by Ada assignment and conversion when lower bounds differ.

The axiom also preserves ``has_bounds`` with appropriately shifted bounds,
provided that sliding preserves nullness in every dimension. This guard is
necessary for modular indexes: shifting both endpoints with wraparound can turn
a nonempty interval into an empty one, or conversely. Without the guard, the
axiom could assign empty bounds to distinct slid maps, contradicting
extensionality. The guard belongs in the axiom itself, independently of the
length checks generated for Ada conversions, because logic functions must be
consistently axiomatized even for arguments that would fail a runtime check.

Concatenation is only defined for one-dimensional arrays. Its map operation
preserves the first operand's elements and shifts the second operand to follow
them. The result's last bound is supplied separately, so the defining axiom can
restrict its element equations to the result's range. Separate operations handle
concatenation with single components. ``singleton`` constructs the map for a
single element, including when concatenating a component with an empty array.
The exact definitions are kept in ``Array__1`` in
:file:`share/spark/theories/_gnatprove_standard.mlw`.

Comparison Operators
""""""""""""""""""""
Comparison operators (<, >, <=, and >=) are defined for one-dimensional arrays
with a discrete component type. These operators are translated in Why through the
means of a ``compare`` logic function. This function is left uninterpreted, but
its sign is uniquely defined by 3 axioms:

 * ``compare_def_eq`` states that ``compare`` returns 0 if and only if both
   arrays are equal (using Ada equality),
 * ``compare_def_lt`` states that ``compare`` returns a negative number if and
   only if the first array is less than the second (using lexicographic
   ordering), and
 * ``compare_def_gt`` states that ``compare`` returns a positive number if and
   only if the first array is greater than the second.

Lexicographic ordering compares corresponding elements after a common equal
prefix. If one array is a proper prefix of the other, the shorter array is less.
Only the sign of ``compare`` matters; its magnitude is unspecified.
To avoid adding unnecessary axioms to the context when ``compare`` is not used,
these declarations are grouped in a separate module. The shared definitions
are in ``Array_Comparison_Axiom`` and its specializations in
:file:`share/spark/theories/ada__model.mlw`; cloning is handled by
``Declare_Comparison_Symbols`` in :file:`src/why/why-gen-arrays.adb`.

Logical Operators
"""""""""""""""""

Ada also defines logical operators (and, or, xor, not) for one-dimensional
arrays whose component type is a boolean subtype. These operators are all
translated as uninterpreted logic functions. Definitions applying the underlying
operator on each element of the arrays are given through axioms. As an example,
consider the array type ``Bool_Array`` defined as follows:

.. code-block:: ada

   type Bool_Array is array (Positive range <>) of Boolean;

For example, the element equation for xor on ``Bool_Array`` is:

.. code-block:: whyml

  forall a b : map.
  forall a_first a_last b_first b_last : int.
  forall i : int.
    a_first <= i <= a_last ->
    get (xorb a a_first a_last b b_first b_last) i =
      Bool.xorb (get a i) (get b (i - a_first + b_first))

The second operand is indexed by position relative to its lower bound. Length
checks are generated at the Ada operation; the element equation does not replace
them. The shared definitions are in the logical-operator modules in
:file:`share/spark/theories/ada__model.mlw`.

As explained in section Enumerations, subtypes of Boolean types are
generally translated as boolean in Why. However, it is not the case for subtypes
of Boolean which define their own ranges (see ``Is_Standard_Boolean_Type``).
Those are translated as mathematical integers, just like other enumeration
types. The defining axioms for logical operations on such type therefore need
to introduce conversions. For example, for the following type:

.. code-block:: ada

   subtype Only_True is Boolean range True .. True;

the corresponding element equation is:

.. code-block:: whyml

  forall a b : map.
  forall a_first a_last b_first b_last : int.
  forall i : int.
    a_first <= i <= a_last ->
    get (xorb a a_first a_last b b_first b_last) i =
      of_rep (Boolean.to_int
        (Bool.xorb (Boolean.of_int (to_rep (get a i)))
          (Boolean.of_int (to_rep (get b (i - a_first + b_first))))))

Note that the equality test is done on the closed form of ``Only_True``, and not
on its representative type or on ``bool``.
Indeed, we do not want to assume an incorrect axiom when the result
of the boolean operation is out of range (here for example, applications of
xor are always out of range of ``Only_True``).

Constrained Arrays with Static Bounds
"""""""""""""""""""""""""""""""""""""

Array types are translated differently depending on whether they are
statically constrained or not (see Why.Gen.Arrays.Declare_Ada_Array).
For statically constrained array types, no new type is introduced.
Instead, constants are declared for the bounds and the underlying map
type is reused as is.

As an example, let us consider the following array type:

.. code-block:: ada

     type My_Array_100 is array (Positive range 1 .. 100) of Natural;

Here are the declarations generated for it:

.. code-block:: whyml

      function first : int = 1
      function last  : int = 100

      type __t = Array__Int__Standard__natural.map

      function bool_eq (x : __t) (y : __t) : bool =
	Array__Int__Standard__natural.bool_eq x first last
		      y first last

We see that boolean equality on arrays reuses the bool_eq function
introduced for maps with appropriate values for bounds. In a similar
way, whenever references to bounds of statically constrained array
objects are encountered, they are directly translated using the
constants defined above, removing completely the need for storing
these values in the actual object.

Unconstrained or Dynamically Constrained Arrays
"""""""""""""""""""""""""""""""""""""""""""""""

Unlike for statically constrained array objects, array bounds are
stored inside objects of an unconstrained or dynamically constrained
type. To this aim, a new why record type is introduced for them,
containing both the map and the bounds. Bounds themselves are
represented as pairs of values of the closed form of the base type of
the index type (indeed, in Ada, bounds of an array object can be
outside the range of the index type if the array is empty). Here is
for example the module for the bounds of objects of the following type:

.. code-block:: ada

   type My_Array is array (Positive range <>) of Natural;

.. code-block:: whyml

    module I1

      type t

      function first t : Standard_integer.integer

      function last t : Standard_integer.integer

      function mk int int : t

      axiom mk_def :
	forall f l : int [mk f l].
	  Standard_integer.in_range f ->
	  Standard_integer.in_range l ->
	  (to_rep (first (mk f l)) = f /\
	    to_rep (last (mk f l)) = l)

      predicate dynamic_property
	(range_first : int) (range_last : int) (low : int) (high : int) =
	Standard_integer.in_range low /\ Standard_integer.in_range high /\
	   (low <= high -> (Standard_positive.in_range low
			 /\ Standard_positive.in_range high))
    end

Here first and last are of type Integer (the base type of Positive)
but the dynamic property for the type states that, if the array is non
empty (low <= high) then the bounds must be in Positive. The
additional parameters range_first and range_last stand for the first
and last bounds of the index type. Here they are unused because
Positive is static, so its range predicate does not request them. For
an index type with dynamic bounds, we would have used the appropriate
dynamic_property which takes these additional parameters.

For an array type of dimension n, n modules like the one above are
generated. They are then used to define the actual why translation of
the array type. Here are the declarations introduced for the My_Array
type:

.. code-block:: whyml

      type __t = { elts: Array__Int__Standard__natural.map; rt : I1.t }

      function to_array (a : __t) : Array__Int__Standard__natural.map =
	a.elts

      function of_array (a : Array__Int__Standard__natural.map)
	  (f l : int) : __t =
	{ elts = a; rt = I1.mk f l }

      function first (a : __t) : int = to_rep (I1.first a.rt)
      function last (a : __t) : int = to_rep (I1.last a.rt)
      function length (a : __t) : int =
	if first a <= last a then
	 last a - first a + 1
	else 0

      predicate dynamic_property (range_first range_last f1 l1 : int) =
	I1.dynamic_property range_first range_last f1 l1

      function bool_eq (x : __t) (y : __t) : bool =
        Array__Int__Standard__natural.bool_eq
          x.elts (first x) (last x)
          y.elts (first y) (last y)

The type __t defined for objects of type My_Array is record holding
one set of bounds (since the type has one dimension) and an infinite
map of naturals. The theory also provides conversion functions to and
from the representative map type as well as getters computing the
first and last bounds, as well as the length of the array. A
dynamic_property predicate for the array is introduced which groups
all dynamic properties on indexes (here there is only one). Finally,
the predefined equality bool_eq on arrays is defined in terms of the
bool_eq function defined in the representative map theory.

Note that these declarations are not generated directly by Gnat2why,
instead they are given in abstract modules ``Unconstr_Array`` and
``Unconstr_Array_<dim>`` in :file:`share/spark/theories/ada__model.mlw`
(similar modules named ``Constr_Array`` and ``Constr_Array_<dim>`` are
declared for statically constrained array types). These modules are
then cloned by Gnat2why as appropriate (see
Declare_Unconstrained/Declare_Constrained declared in Why.Gen.Arrays).

Array Conversions
"""""""""""""""""

Most array conversions can be handled by going to the underlying map
type and applying sliding if necessary. However, statically matching component
subtypes can have different closed forms, so the arrays can use distinct map
types. Specific Why3 conversion functions then relate those map types.
They are generated as needed and reused; the conventions are documented in
:file:`src/why/why-gen-arrays.ads`.

As an example, assume we want to convert between the two following
types:

.. code-block:: ada

   type My_Array is array (Positive range <>) of Natural;

   subtype My_Natural is Natural;
   type My_Array_2 is array (Positive range <>) of My_Natural;

The element equation for the conversion from ``My_Array`` to ``My_Array_2`` is:

.. code-block:: whyml

   forall a : Array__Int__Standard__natural.map.
     let b = convert a in
       forall i : int.
         to_rep (Array__Int__Standard__natural.get a i) =
         to_rep (Array__Int__my_natural.get b i)

The defining axiom for convert states that both maps contain the same
elements. Note that here we need to go to the representative type of
elements to be able to compare them, as their closed types are
different. Each ``to_rep`` here is the conversion for its operand's component
type; module qualifications are omitted.
The conversion also preserves ``has_bounds``, so logical equality can still be
proved from the elements within the bounds after conversion. These equations
describe the representation change; length and subtype checks required by Ada
are generated at the conversion.

Converting between array types with different representative index types is not
supported. In particular, conversions between integer and bitvector indexes,
or between bitvectors of different sizes, are rejected during marking. Supporting
them would require conversion functions that also convert the indexes.

Record Types, Private Types, and Concurrent Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Record types, task types, protected types, and private types use a common
record model (see ``Gnat2why.Util.Is_Record_Type_In_Why``). A representative
module describes the stored data and operations shared by types with the same
representation. A type-specific module uses that representation and adds
declarations specific to the Ada type, such as its tag. Sharing a
representative type between types of a hierarchy with the same components
avoids unnecessary conversions. The declaration and sharing conventions are
documented in :file:`src/why/why-gen-records.ads`.

Representative Type
"""""""""""""""""""

The representative type of a type which can have discriminants is a
why record type with immutable fields. Mutation of components is
handled by modifying the whole object. A representative why record
type has a layered structure.

Variant records also use this structure, with fields for every variant,
including inactive ones. An algebraic datatype with a constructor for each
variant would make Why3 generate checks on accesses to fields that are not
present in every constructor. GNATprove needs to generate these checks itself
to track them precisely. Pattern matching would avoid those implicit checks,
but would introduce cases that previous checks have already ruled out, making
the VCs more complex. The record representation allows field access without
another check or case split. This fits the common translation pattern for
contracts and assertions:
first generate the checks for an expression, then translate its logical value.

At the top-level, a field is defined for each kind of information that
needs to be stored in the value (discriminants, components, tag...). Fields for
components or discriminants are themselves records holding the values of the
actual components. This separation lets the object and subprogram encodings
treat each top-level field according to its mutability. For example, a call that
cannot change discriminants can receive them by value while receiving the
ordinary components by reference. See :ref:`Record Objects` for the split
object model.

As an example, consider the following record type:

.. code-block:: ada

     type My_Rec (L : Natural) is record
        H : Integer;
     end record;

Its representative type has two top-level fields, one for the
discriminants and one for the components:

.. code-block:: whyml

      type __split_discrs =
	{ rec__my_rec__l : Standard__natural.natural }

      type __split_fields =
	{ rec__my_rec__h : Standard__integer.integer }

      type __rep = { __split_discrs : __split_discrs;
		     __split_fields : __split_fields }

The field __split_discrs contains every discriminant of the type. SPARK does not
allow adding discriminants in a derivation, so all types of a given hierarchy
share this top-level field. The field __split_fields
contains every component of the type that can be visible in SPARK as
well as ``Part_Of`` variables for single protected objects. Components hidden
by Ada privacy remain in the proof representation when their declarations are
in SPARK. For all types modeled as records, proof translation retrieves
the component set only through ``Gnat2why.Tables.Get_Component_Set``.
The frontend's component list is insufficient, since Ada privacy can remove
inherited components from it. The tables and their conventions are documented in
:file:`src/why/gnat2why-tables.ads`; field naming conventions are in
:file:`src/why/why-gen-records.ads`.

When the type is derived, or when a subtype is defined, the
representative type can be preserved when no components are added and no
component type changes, for example because of a discriminant constraint.
In our example, the following My_Rec_100 subtype will have the same
representative type as My_Rec:

.. code-block:: ada

      subtype My_Rec_100 is My_Rec (100);

.. _why3-discriminant-dependent-record-example:

Let us consider a slightly different example where My_Rec contains a
discriminant-dependent component:

.. code-block:: ada

     type My_Rec (L : Natural) is record
        C : My_Array (1 .. L);
     end record;

     subtype My_Rec_100 is My_Rec (100);

Here, My_Rec_100 will define a new representative type in which the C
component has the more precise My_Array (1 .. 100) type. However, as
discriminants themselves cannot be discriminant dependent, the type
for the discriminants field will be preserved:

.. code-block:: whyml

     type __split_fields =
      { rec__my_rec__c : Array__Int__Standard__natural.map }

     type __rep =
      { __split_discrs : P__my_rec.__split_discrs;
	__split_fields : __split_fields }

Discriminant checks
"""""""""""""""""""

There are two kinds of discriminant checks for types with
discriminants. First, components that are under a variant require a
check when accessed. Why3 records contain fields for every variant, so a field
access in the encoding is possible even when the Ada component is absent.
The discriminant check prevents the program from reading such a field.

For components that may need a discriminant check, a predicate is defined that
checks whether the component is present in a record object depending
on the value of its discriminants. If the component is not nested in a
variant part, this predicate simply returns True.

As an example, let us consider a record type with a variant part:

.. code-block:: ada

     type My_Rec (L : Natural) is record
	case L is
	when 0 =>
	   null;
	when others =>
	   C : My_Array (1 .. L);
	end case;
     end record;

The C component is only defined in a record if its discriminant is not
zero. This is expressed in its associated discriminant predicate:

.. code-block:: whyml

     predicate types__c__pred (d : __split_discrs) =
       not (to_rep d.rec__my_rec__l = 0)

The predicate takes the value of the top-level field for discriminants. The
type of this field can be shared even when component types differ between
record views.

A discriminant check is also needed for types and subtypes with
discriminant constraints, to check that a record belongs to the type or subtype.
A predicate shared by the hierarchy compares the expected discriminants with
the discriminants stored in the corresponding top-level field. For example,
the check for ``My_Rec_100`` uses the following predicate with
``expected_l = 100``:

.. code-block:: whyml

     predicate in_range (expected_l : int) (d : __split_discrs) =
       expected_l = to_rep d.rec__my_rec__l

Note that the actual value of the discriminant is not inlined here,
but rather needs to be supplied at each call. This is because this
value may depend on variables, in particular if the subtype is defined
in a loop (loop indices are translated as variables in Why).

Private components
""""""""""""""""""

As discussed under :ref:`Modules for Entities`, proof uses the most precise
SPARK view of types by default. However, it can happen
that a type is completely or partially hidden from SPARK analysis
under a SPARK_Mode (Off) pragma (see
``Gnat2why.Tables.Has_Private_Part``). Omitting the hidden components would make
objects with the same visible components logically equal. Proof could then
substitute one object for the other even when functions using hidden state
can distinguish them. Instead, the translation
creates a special field for them, named rec__t for a type T, of an
abstract logic type.

.. _why3-private-record-example:

As an example, let us consider a semi private
type of which only the discriminants are available in SPARK:

.. code-block:: ada

       package P with SPARK_Mode is
	  type Priv (B: Boolean) is private;
       private
	  pragma SPARK_Mode (Off);
	  type Priv (B: Boolean) is null record;
       end P;

Here is how it is translated in Why:

.. code-block:: whyml

     type __main_type

     type __split_discrs = { rec__priv__b : bool }

     type __split_fields = { rec__priv : __main_type }

     type __rep =
      { __split_discrs : __split_discrs;
	__split_fields : __split_fields }

As __main_type has no definition, we can deduce nothing about the
rec__priv field, not even whether it actually can take several values
or not.

Record equality
"""""""""""""""

Predefined equality on record types is the conjunction of equalities
on discriminants and present components, using the appropriate Ada equality
for each component type (see :ref:`Predefined / primitive equality`). It does
not compare placeholder values in inactive variants. Predefined equality is
generated in the representative module, as it is shared between record
types with the same fields. When a user-defined primitive equality is needed,
its ``user_eq`` symbol belongs to the type-specific module, as equality can be
overridden after derivation.

As an example, let us consider the following type structure:

.. code-block:: ada

      type My_Rec (L : Natural) is record ...;

      subtype My_Rec_100 is My_Rec (100);

      type Rec_Eq is new My_Rec (100);

      function "=" (X, Y : Rec_Eq) return Boolean;

      type Big_Rec (B : Boolean) is record
	 X : My_Rec_100;
	 Y : Rec_Eq;
      end record;

Here is the function defined for predefined equality on type Big_Rec:

.. code-block:: whyml

    function bool_eq (a : __rep) (b : __rep) : bool =
      (a.__split_discrs.rec__big_rec__b =
       b.__split_discrs.rec__big_rec__b)
      /\ (types__big_rec__x__pred a.__split_discrs ->
	     P__my_rec_100.bool_eq
			 a.__split_fields.rec__big_rec__x
			 b.__split_fields.rec__big_rec__x)
      /\ (types__big_rec__y__pred a.__split_discrs ->
	    P__rec_eq.user_eq
			 a.__split_fields.rec__big_rec__y
			 b.__split_fields.rec__big_rec__y)

We see that it uses the predefined equality on X and the primitive
equality on Y. Also notice that, if the type has discriminants,
equalities on components are only considered if the components are
indeed present (i.e. when the predicate discriminant check for the
corresponding component returns True).

On tagged record extensions, the predefined equality is defined in
terms of the primitive equality of the parent. As a consequence, if
the primitive equality is overridden by the user on a tagged type,
this user-defined equality function will be used in the predefined
equality of all of its descendants. For example, consider the types
``Root`` and ``Child`` below:

.. code-block:: ada

      type Root is tagged record
         F, G : Integer;
      end record;
      function "=" (X, Y : Root) return Boolean is (X.F = Y.F);

      type Child is new Root with record
         H : Integer;
      end record;

The user-defined primitive equality of ``Root`` will be used for the
fields ``F`` and ``G`` in the predefined equality of ``Child``:

.. code-block:: whyml

  function bool_eq (a: __rep) (b: __rep) : bool =
      P__root.user_eq
          { P__root.__split_fields =
              { P__root.rec__root__f = a.__split_fields.rec__root__f;
                P__root.rec__root__g = a.__split_fields.rec__root__g;
                P__root.rec__ext__ = P__root.null__ext__ };
            P__root.attr__tag = P__root.__tag }
          { P__root.__split_fields =
              { P__root.rec__root__f = b.__split_fields.rec__root__f;
                P__root.rec__root__g = b.__split_fields.rec__root__g;
                P__root.rec__ext__ = P__root.null__ext__ };
            P__root.attr__tag = P__root.__tag }
     /\ to_rep a.__split_fields.rec__child__h
          = to_rep b.__split_fields.rec__child__h

For types with a private part, a separate function stands for equality on the
hidden state. It uses Why3's logical equality when that is an appropriate model
of Ada equality for the hidden representation. The translation can inspect
the full view to make this choice without exposing its structure to proof;
``Use_Real_Eq_For_Private_Type`` in :file:`src/spark/spark_util-types.adb`
implements this decision, including predefined-equality annotations.

When Ada equality can identify values that a function could distinguish, logical
equality would give unsound congruence assumptions. For example, floating-point
equality identifies positive and negative zero, and unconstrained array equality
does not compare bounds. User-defined component equality and equality on tagged
types can also ignore parts of the represented state. In these cases, the
equality function for the private part is left uninterpreted. Even reflexivity
cannot then be assumed.

For example, here is the function defined for predefined equality on
type :ref:`Priv <why3-private-record-example>`:

.. code-block:: whyml

     function __main_eq (a : __main_type) (b : __main_type) : bool = a = b

     function bool_eq (a : __rep) (b : __rep) : bool =
      (a.__split_discrs.rec__priv__b = b.__split_discrs.rec__priv__b)
      /\ (__main_eq a.__split_fields.rec__priv
		    b.__split_fields.rec__priv)

The hidden completion of ``Priv`` is a null record, so logical equality can be
used for its abstract private part. If the completion instead contained a
floating-point component, ``__main_eq`` would have no definition.

Logical equality and inactive components
""""""""""""""""""""""""""""""""""""""""

Why3 record values contain all fields, including those of inactive variants.
Field accesses must check that the component is present, and predefined record
equality only compares present components. The values stored in inactive fields
therefore cannot affect the result of Ada equality.

However, Why3's logical equality compares the whole representation. If inactive
fields could contain arbitrary values, two records with matching discriminants
and logically equal present components could still differ in those fields.
To avoid this, all fields of inactive variants are fixed to their respective
dummy values. In the earlier variant record example, the field for ``C`` is
fixed to its dummy value whenever ``L = 0``.

Absent components can then no longer prevent proof of logical equality. Once
established, logical equality gives congruence for all logical functions:
applying any such function to either record gives the same result. This requires
logical equality of the present components, rather than just Ada equality;
user-defined or floating-point equality may identify distinct Why3 values.
Any private fields, tags, and extension fields must also be logically equal.

This choice has a cost, as for the fixed out-of-bounds values of arrays.
The dynamic invariant of a record requires each inactive field to equal its
dummy value. Record construction and operations must establish or preserve
these conditions. For example, aggregates fill absent fields with dummy values,
and assignment of a new variant must leave the fields of the old variant dummy
when they are no longer present. These conditions add to the proof context even
though Ada code cannot read the fields. They are the tradeoff for being able to
prove logical equality from the state present in the Ada record.

Mutable discriminants
"""""""""""""""""""""

Objects of a type with mutable discriminants can be either constrained
or unconstrained (this information is available through the ``'Constrained``
attribute). It depends on how the object was declared and does not change during
its lifetime. An assignment can change an unconstrained object's discriminants,
but must preserve a constrained object's discriminants.

As an example, consider the following type with mutable discriminants:

.. code-block:: ada

     type My_Option (Present : Boolean := False) is record
	case Present is
	   when True  =>
	      Content : Integer;
	   when False =>
	      null;
	end case;
     end record;

Constrainedness belongs to the object, rather than to the record value copied
by assignment. When it is not known statically, the translation keeps it in a
separate immutable Boolean alongside the object's mutable discriminants and
components (see :ref:`Record Objects`). For example, these objects can contain
the same record value while having different constrainedness:

.. code-block:: ada

   X : My_Option := (Present => False);
   Y : My_Option (False) := (Present => False);

``X`` can later receive a value with ``Present = True``; ``Y`` cannot. Copying a
value to either object does not copy the source object's constrainedness.
Before an assignment to a constrained target, a check verifies that the new
discriminants match the old ones.

The value of the ``'Constrained`` attribute also depends on its prefix; for example,
components of constants are constrained. ``New_Constrained_Attribute_Expr`` in
:file:`src/why/gnat2why-expr.adb` uses the statically known result when available
and the separate object flag otherwise. It does not retrieve constrainedness
from the component value.

Record Conversions
""""""""""""""""""

When two types of a record hierarchy share the same representative
type, no conversion is required. Otherwise, conversions go through the
root type of the hierarchy. More precisely, for every record type or
subtype which is not a root, two conversion functions, to and from the
root type are introduced. As an example, here are the conversion functions for
the earlier :ref:`My_Rec_100 <why3-discriminant-dependent-record-example>` subtype
whose ``C`` component has static array bounds:

.. code-block:: whyml

     function to_base (a : __rep) : my_rec =
      {__split_discrs = a.__split_discrs;
       __split_fields =
	{ rec__my_rec__c =
		(of_array a.__split_fields.rec__my_rec__c 1 100) }}

     function of_base (r : my_rec) : __rep =
      { __split_discrs = r.__split_discrs;
	__split_fields =
	{ rec__my_rec__c = (to_array r.__split_fields.rec__my_rec__c) } }

As SPARK does not allow adding discriminants in derivation, the field for
discriminants is always preserved. As for regular components, they may
require a conversion if their type has changed, like here for the C
component. The map is preserved without sliding: this is a change of record
view, and a discriminant-dependent component keeps its indexes. The conversion
functions are not inverses of each other outside the subtype's constraints.
Conversion conventions are documented in :file:`src/why/why-gen-records.ads`.

Tagged types
""""""""""""

An object of a tagged type T has the particularity that it can in fact
be a view conversion of an object of descendant of T. To represent
tagged objects, we therefore need a tag, which allows to specialize
treatment when necessary (conversions, dispatching, tag checks...), as
well as a way to store an unknown number of unknown components which
may arise from future derivations.

The tag is represented by an additional top-level field of
mathematical integer type named attr__tag. For each specific tagged type,
a logic constant of type ``int`` is introduced to represent
the specific tag of objects of this type. A fresh integer value is
given for this constant on each derived type so it can be deduced that
different types have different tags. Subtypes reuse the tag of their base type.
These constants are used to
specify the value of the tag of an object when it is known, so that the
object can be handled more precisely.

The notion of derivation class is represented through an abstract
``__compatible_tags`` predicate symbol. It is declared in the
``Compatible_Tags`` module of ``_gnatprove_standard``:

.. code-block:: whyml

   module Compatible_Tags
     (* A predicate to check compatibility between tags:
        __compatible_tags tag1 tag2 means objects of type T1'Class also
       have type T2'Class. *)

      val predicate __compatible_tags (from_tag : int) (to_tag : int)
   end

This module also contains axioms which give useful properties of the
derivation classes (``__compatible_tags`` is reflexive and transitive
etc.). In addition to this general module, a specific
``Compatible_Tags`` module is generated for the root of each
tagged derivation tree. It contains axioms giving the value of the
``__compatible_tags`` predicate on each specific tag in the derivation
tree which is visible from the current unit (see
``Why.Gen.Records.Create_Compatible_Tags_Theory``).

In addition to the attr__tag top-level field, tagged types also have a
special regular field named rec__ext__ of an abstract ``__ext_type``.
It is stored in the __split_fields top-level field, along with other
components and stands for potential hidden component of derived types.

As an example, let us consider the following tagged type:

.. code-block:: ada

     type Root is tagged record
        F : Integer;
     end record;

The why type introduced for it contains two top-level fields, one for
components and one for the tag, and its component field contains a
special component for extensions:

.. code-block:: whyml

     type __ext_type

     type __split_fields =
      { rec__root__f : Standard__integer.integer;
	rec__ext__ "model_trace:" : __ext_type }

     type __rep =
      { __split_fields : __split_fields;
	attr__tag      : int }

Like for other record types, tagged conversions go through the root of
the type hierarchy. For each tagged type which is not a root, logic
functions are provided to hide components that are not present in the
root type inside the extension and to retrieve them.

As an example, let us consider a tagged extension of Root named Child:

.. code-block:: ada

     type Child is new Root with record
        G : Integer;
     end record;

Like for Root, the translation of Child has a top-level attr__tag
field as well as a regular rec__ext__ field to store potential
extensions:

.. code-block:: whyml

     type __split_fields =
      { rec__child__g : Standard__integer.integer;
	rec__root__f  : Standard__integer.integer;
	rec__ext__    : __ext_type }

     type __rep =
      { __split_fields : __split_fields;
	attr__tag      : int }

Then, conversions to and from the Root type are defined through the
means of abstract hide and extraction functions.

.. code-block:: whyml

     function hide_ext__ (g : Standard__integer.integer)
			  (rec__ext__ : __ext_type) : P__root.__ext_type

     function extract__g (x : P__root.__ext_type) : Standard__integer.integer

     function extract__ext__(x : P__root.__ext_type) : __ext_type

     function to_base (a : __rep) : P__root.root =
      {__split_fields =
	    {rec__root__f = a.__split_fields.rec__root__f;
	     rec__ext__ = (hide_ext__ a.__split_fields.rec__child__g
				      a.__split_fields.rec__ext__) };
       attr__tag = a.attr__tag }

     function of_base (r : P__root.root) : __rep =
      { __split_fields =
	 { rec__child__g = (extract__g r.__split_fields.rec__ext__);
	   rec__root__f = r.__split_fields.rec__root__f;
	   rec__ext__ = (extract__ext__ r.__split_fields.rec__ext__) };
       attr__tag = r.attr__tag }

To avoid losing information when converting between types which share
a component which is not in the root, the same extraction function is
reused for every type which shares the same component. For example, consider
the following extension:

.. code-block:: ada

     type Grand_Child is new Child with record
        H : Integer;
     end record;

This type reuses the extraction function for G declared in Child's
representative module:

.. code-block:: whyml

     function extract__g (x : P__root.__ext_type) : Standard__integer.integer =
        P__child.extract__g x

To link the extraction functions and the various hide__ext__ functions
together, we introduce a bijection from the abstract ``__ext_type`` to a
concrete record type in a separate representative completion module. This
concrete type is a logical view of the single abstract extension field, rather
than additional fields in the tagged record itself. For a root type, it contains
all components introduced in extensions visible from the analyzed unit, plus
one field for the unknown remaining extension. For example, the concrete
extension type of Root contains
components for Child.G and Grand_Child.H:

.. code-block:: whyml

  type ext__ =
    { rec__p__child__g__ext__ : Standard__integer.integer;
      rec__p__grand_child__h__ext__ : Standard__integer.integer;
      rec__hidden_ext__ : Main.__private }

  val function __open (x : P__root.__ext_type) : ext__
  val function __close (x : ext__) : P__root.__ext_type

  axiom close_open:
    forall x : P__root.__ext_type [__open x]. __close (__open x) = x

  axiom open_close:
    forall x : ext__ [__close x]. __open (__close x) = x

The bijection functions ``__open`` and ``__close`` are generated by cloning
``Incomplete_type`` from :file:`share/spark/theories/ada__model.mlw`.
Completion modules also contain axioms defining the extraction functions used
in the extensions:

.. code-block:: whyml

  axiom extract__p__child__g__def:
    forall rec__ext__ : P__root.__ext_type.
      P__child.extract__p__child__g rec__ext__
         = (P__root___rep__compl.__open rec__ext__).rec__p__child__g__ext__

  axiom extract__p__grand_child__h__def:
    forall rec__ext__ : P__root.__ext_type.
      P__grand_child.extract__p__grand_child__h rec__ext__
         = (P__root___rep__compl.__open rec__ext__).
             rec__p__grand_child__h__ext__

For tagged types which are not roots, the concrete extension type contains
all components occurring in visible extensions *of the root* which are not
present in the type. In our hierarchy, the concrete extension type for Child
has only a component for Grand_Child.H, but, if we were to add a new child
Other_Child of Root with a component J, then J would be in the concrete
extension type of Child even though it cannot occur in any descendant of Child.

Keeping these fields allows ``__open`` and ``__close`` to remain inverse for
all values of the extension types. If fields absent from the current type were
discarded, a validity condition would be needed to fix their values to dummy
values before stating those inverse properties. The chosen model avoids that
condition by retaining the extra unknown values. This changes little in the
abstraction, since it already contains an unknown remaining extension field.

The extension module of non-root tagged types also contains axioms defining the
hide__ext__ and extract__ext__ functions of the type. Here are those defined
for Child:

.. code-block:: whyml

  type ext__ =
    { rec__p__grand_child__h__ext__ : Standard__integer.integer;
      rec__hidden_ext__ : Main.__private }

  axiom hide_ext__def:
    forall g : Standard__integer.integer.
      forall ext : P__child.__ext_type.
        let open_ext = __open ext in
          P__root___rep__compl.__open (P__child.hide_ext__ g ext)
           = { rec__p__child__g__ext__       = g;
               rec__p__grand_child__h__ext__ =
	            open_ext.rec__p__grand_child__h__ext__;
               rec__hidden_ext__             = open_ext.rec__hidden_ext__ }

  axiom extract__ext__def:
    forall ext : P__root.__ext_type.
      let open_ext = P__root___rep__compl.__open ext in
        __open (P__child.extract__ext__ ext)
         = { rec__p__grand_child__h__ext__ =
	          open_ext.rec__p__grand_child__h__ext__;
             rec__hidden_ext__             = open_ext.rec__hidden_ext__ }

Equality on a specific tagged type only compares fields that are visible
in the current view of the objects. So the equality between view
conversions to Root of two objects of type Child will still compare
only the F component:

.. code-block:: whyml

     function bool_eq (a : __rep) (b : __rep) : bool =
      (to_rep a.__split_fields.rec__root__f =
       to_rep b.__split_fields.rec__root__f)

On the other hand, when comparing objects of a classwide type, a check
is first made that the tags match and then the appropriate equality is
used. This behavior is modelled using an abstract function
__dispatch_eq which is introduced in every root type to
stand for the dispatching equality in the hierarchy (see
``Gnat2why.Expr.New_Op_Expr``):

.. code-block:: whyml

     function __dispatch_eq (attr_tag : int) (a : __rep) (b : __rep) : bool

The abstract function is axiomatized in the completion module for the
type.

Ownership Annotations
"""""""""""""""""""""

Private types whose full view is not in SPARK can be annotated with
Ownership to state that copying them might create aliases. In addition, it
is possible to state that they need some kind of reclamation when they
are finalized. In this case, it is necessary to generate WhyMl code to
track whether a value of this type has been moved to another object
before the finalization. This is done by declaring a ``__move_tree`` type
and a ``__is_moved_or_reclaimed`` predicate like for
:ref:`Access-To-Object Types`. The private representation cannot expose the
owned parts, so the reclamation condition comes from the user-supplied
``Is_Reclaimed`` function. The move flag is stored separately from the value
and is used to exclude moved objects from leak checks. For example, consider
the following package:

.. code-block:: ada

   package P is
      type T is private with
        Default_Initial_Condition,
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      function Is_Reclaimed (X : T) return Boolean with
        Annotate => (GNATprove, Ownership, "Is_Reclaimed");

      ...
   private
      pragma SPARK_Mode (Off);
      ...
   end P;

Since ``T`` needs reclamation, a ``__move_tree`` type and a
``__is_moved_or_reclaimed`` predicate are declared for it. They are used when
checking for leaks when an object of this type is finalized:

.. code-block:: whyml

  module Test__p__t___move_tree

    type __move_tree = bool

    predicate __is_moved_or_reclaimed (tree: __move_tree) (obj: Test__p__t.t) =
      tree \/ Test__p__is_reclaimed.is_reclaimed obj = True

  end

Special Cases
"""""""""""""

As record types in Why must contain at least one field, untagged null
records are translated as an abstract type.
To allow conversions between types of a hierarchy of null records, the
abstract type introduced for the root of the hierarchy is reused by
descendants. Therefore, conversion functions on null record types are
always the identity. Predefined equality returns ``True`` because an Ada null
record has no components to distinguish its values.

Simple private types are untagged private types with no discriminants
whose full view is not in SPARK:

.. code-block:: ada

      package P with SPARK_Mode is
	 type Priv is private;
      private
	 pragma SPARK_Mode (Off);
	 type Priv is new Integer;
      end P;

Such types can model mathematical types (unbounded integers, reals...). Keeping
their representation free of a record wrapper makes it easier to map them to
interpreted types, both in proof assistants and in GNATprove's hardcoded models.
Unlike for null record types, we introduce a representative theory for them,
but a minimalist one, where the representative type is normally left abstract.
Predefined equality uses logical equality
when the full view permits it, and remains uninterpreted otherwise. For the
integer completion above, it is:

.. code-block:: whyml

     type __rep

     function bool_eq (a : __rep) (b : __rep) : bool = a = b

Classwide types reuse the representation of their specific type. The same
fields and tag can describe values from the whole hierarchy; operations use
the tag to select classwide behavior, as discussed under Tagged types.
Other representation-reuse cases are documented with ``Record_Type_Is_Clone``
in :file:`src/why/why-gen-records.ads`.

Access-To-Object Types
^^^^^^^^^^^^^^^^^^^^^^
Value-Based Representation
""""""""""""""""""""""""""
Access values are modeled by their designated values, without addresses or a
shared heap. Updating a designated value is a functional update of the access
value, just like updating a component of a record.

Ownership checking prevents a write from leaving another usable alias with an
outdated designated value in this model. See :ref:`Ownership Checking` for the
aliasing restrictions and :ref:`Local Borrows` for the translation of borrowing.

Access types with the same designated type share a representative type to allow
conversions, including conversions from named to anonymous access types.
Module selection and sharing conventions are documented in
:file:`src/why/why-gen-pointers.ads`.

This representative type has two fields. One for the value and a boolean flag
to register whether the access object is null. As an example, consider an
access type to natural numbers:

.. code-block:: ada

  type Ptr is access Natural;

Here is the representative type introduced for it:

.. code-block:: whyml

   type __rep =
     { rec__p__ptr__is_null_pointer : bool;
       rec__p__ptr__pointer_value   : natural }

An option datatype could omit the designated value for null pointers. However,
accessing the value would then require a Why3-generated check or pattern
matching on the null case. As for :ref:`variant records <Representative Type>`,
the record representation lets GNATprove generate and track the null check
itself, then translate the value access without an additional check or case
split. The designated-value field is therefore retained even for null pointers.

Along with the representative type, the representative module contains other
declarations which are shared between access types. Among them, the null
pointer, a protected access function which checks whether a pointer is null
before returning its value, and the primitive equality over access objects. Here
are these declarations for the ``Ptr`` type defined above:

.. code-block:: whyml

   function __null_pointer : __rep

   axiom __null_pointer__def_axiom :
      __null_pointer.rec__p__ptr__is_null_pointer = True
      /\ __null_pointer.rec__p__ptr__pointer_value = Standard__natural.dummy

   val rec__p__ptr__pointer_value_
     (a : __rep) : Standard__natural.natural
    requires { not a.rec__p__ptr__is_null_pointer }
    ensures  { result = a.rec__p__ptr__pointer_value }

   function bool_eq  (a : __rep) (b : __rep) : bool =
      a.rec__p__ptr__is_null_pointer = b.rec__p__ptr__is_null_pointer
   /\ (not a.rec__p__ptr__is_null_pointer ->
          a.rec__p__ptr__pointer_value = b.rec__p__ptr__pointer_value)

The designated-value field of a null pointer is fixed to a dummy value by the
dynamic invariant, as for inactive fields of variant records. This ensures that
all null pointers of this representative type are logically equal.

The ``bool_eq`` function does not model address equality: two pointers might
designate equal values at different addresses. SPARK permits predefined equality
on access values only when one operand is statically null. The first conjunct
of ``bool_eq`` is enough for this case; the comparison of designated values is
not used to decide the result. For composite types, predefined equality is
forbidden when it would compare access subcomponents.

Subtype Constraints
"""""""""""""""""""
Subtypes of access types to unconstrained composite objects can be supplied with
a composite constraint which applies to the designated values. When generating
the representative module for such an access subtype, we introduce
conversion functions to and from the base access type, as well as a range check
function to check membership in the subtype. A null exclusion is checked
separately using the ``is_null`` flag.

For example, consider an access type to unconstrained arrays of natural numbers,
and a subtype of this access type only storing arrays ranging from 1 to 5:

.. code-block:: ada

   type Arr_Ptr is access Nat_Array;
   subtype S is Arr_Ptr (1 .. 5);

Since ``S`` has static bounds, its designated array is represented by a map.
``to_base`` restores these bounds when converting to ``Arr_Ptr``, and
``of_base`` extracts the map in the other direction. The range predicate
checks the required bounds:

.. code-block:: whyml

   predicate in_range (expected_first expected_last : int) (r : arr_ptr) =
     not r.rec__p__arr_ptr__is_null_pointer ->
       first r.rec__p__arr_ptr__pointer_value = expected_first
       /\ last r.rec__p__arr_ptr__pointer_value = expected_last

We can see that the range predicate for arrays takes the array bounds as
parameters. This is because the bounds may contain references to constants which
are translated as variables in Why (this is similar to what is done for
discriminants in range predicates for records).

The range predicate is used both for checking that a value is in the expected
type, when translating conversions, qualifications, and allocators, and to
translate explicit membership test in the user code.

Recursive Access Types
""""""""""""""""""""""

An access type can designate an incomplete type whose completion contains
components of that access type. For example:

.. code-block:: ada

   type Node;
   type Node_Ptr is access Node;
   type Node is record
      Value : Integer;
      Next : Node_Ptr;
   end record;

With the value-based representation, the pointer type contains a node value,
and the node type contains a pointer value. Declaring these as recursive Why3
datatypes would require declaring all mutually recursive types together.
This would require changing the current organization, where types are
declared separately, one per module.

Instead, the representative module for ``Node_Ptr`` uses an abstract type for
its designated-value field. The representation of ``Node`` can then refer to
``Node_Ptr`` without a cycle between the type declarations. A separate
completion module connects the abstract designated-value type to the completed
node type through ``__open`` and ``__close`` functions. Dereference opens the
abstract value; updating the designated value closes the new node value.
The conversion axioms relate these two views without requiring recursive type
declarations. This completion is generated by ``Declare_Rep_Pointer_Compl`` in
:file:`src/why/why-gen-pointers.adb`.

Move trees for recursive structures use separate abstract declarations and
completions for the same reason. The concrete layout is supplied after the
component types are available, and the abstract reclamation predicate is
connected to the predicate on the concrete tree. The corresponding APIs are
documented in :file:`src/why/why-gen-pointers.ads`.

Move Trees
""""""""""

Ownership checking prevents invalid uses of moved values, but it does not prove
that allocated memory is reclaimed. For objects containing parts which need
reclamation (typically of a pool-specific access type), the translation tracks
whether responsibility for reclamation has been transferred to another object.
The source's designated value need not change when it is moved, so nullness
alone cannot tell whether the source still owns memory.

This is done by storing boolean move flags in variables and subprogram
parameters. These flags are stored in a separate structure which mimics the
form of the object. It does not duplicate information coming from the object
(whether a pointer is null, discriminants, bounds of arrays). The type
``__move_tree`` and the predicate ``__is_moved_or_reclaimed`` are declared in
a separate module. The predicate takes a move tree and an object and returns
true if no part of the object still requires reclamation by its owner.
As an example, consider the following data structure. To know whether ``V``
has been moved or reclaimed, we
need to decide, depending on the value of the discriminant ``L``, whether the
component ``F`` or all components of ``A`` have been either moved or set to
null:

.. code-block:: ada

   type Int_Acc is access Integer;
   type Int_Acc_Array is array (Positive range <>) of Int_Acc;
   type Rec (L : Natural) is record
      G : Integer;
      case L is
         when 0 =>
            F : Int_Acc;
         when others =>
            A : Int_Acc_Array (1 .. L);
      end case;
   end record;

   V : Rec (...);

For this, a type ``__move_tree`` to store the flags and a predicate
``__is_moved_or_reclaimed`` are declared for each type used in the structure.
Here is the move-tree type and predicate for subcomponents of type
``Int_Acc``. The move tree holds a single flag for the pointer itself, and the
``__is_moved_or_reclaimed`` predicate returns true if either the object has
been moved as per the move tree, or it is null, as per the object value:

.. code-block:: whyml

   type __move_tree = { rec__is_moved__ : bool }

   predicate __is_moved_or_reclaimed (tree: __move_tree) (obj: int_acc) =
     tree.rec__is_moved__ = True \/ obj.rec__test__int_acc__is_null_pointer = True

For arrays, we need a flag per component. Similarly to theories used for array
values, we use a total map from indices to component move trees. It has no
bounds of its own. The ``__is_moved_or_reclaimed`` predicate gets the bounds
either from the type (if
its bounds are static) or from the object and only considers elements which
are in bounds:

.. code-block:: whyml

   predicate __is_moved_or_reclaimed (tree: __move_tree) (obj: int_acc_array) =
     forall i : int. first obj <= i <= last obj ->
       Test__int_acc___move_tree.__is_moved_or_reclaimed
         (__get tree i) (Test__int_acc_array.get (to_array obj) i)

Move trees for records are Why3 records with a field per component which needs
reclamation. Discriminants are not present. The ``__is_moved_or_reclaimed``
predicate gets them from the value of the object and only considers components
which are present in the current variant. Note that ``G`` is not present
as it does not need reclamation:

.. code-block:: whyml

   type __move_tree =
     { rec__test__rec__f : Test__int_acc___move_tree.__move_tree;
       rec__test__rec__a : Test__int_acc_array___move_tree.__move_tree }

   predicate __is_moved_or_reclaimed (tree: __move_tree) (obj: rec) =
     (if test__rec__f__pred obj then
        Test__int_acc___move_tree.__is_moved_or_reclaimed
          tree.rec__test__rec__f obj.__split_fields.rec__test__rec__f)
     /\
     (if test__rec__a__pred obj then
        Test__int_acc_array___move_tree.__is_moved_or_reclaimed
          tree.rec__test__rec__a obj.__split_fields.rec__test__rec__a)

The field-presence predicates come from the record representation: ``F`` is
present when ``L = 0``, and ``A`` when ``L /= 0``.

For a pool-specific access type, the move tree contains a flag for the pointer
itself and, when needed, a subtree for the designated value. General access
types have no flag for the pointer itself; they reuse the designated value's
move tree when it contains parts needing reclamation.

The move-tree layouts and operations are documented with
``Create_Move_Tree_Theory_For_Pointer`` in
:file:`src/why/why-gen-pointers.ads` and the corresponding array and record
routines in :file:`src/why/why-gen-arrays.ads` and
:file:`src/why/why-gen-records.ads`.

Checks are needed when an owning value is overwritten or leaves its scope.
``Unchecked_Deallocation`` frees the allocation itself, but still needs a check
that owned parts inside the designated value have been moved or reclaimed.

To check whether ``V`` has been moved or reclaimed, the predicate is called
with its current move tree and reconstructed value:

.. code-block:: whyml

   assert {
      Test__rec___move_tree.__is_moved_or_reclaimed
      Test__v.v__rec__is_moved__.__move_tree__content
      { __split_fields = Test__v.v__split_fields.__split_fields__content;
        __split_discrs = Test__v.v__split_discrs } }

These checks are generated by ``Check_No_Memory_Leaks`` in
:file:`src/why/gnat2why-expr.adb`. They are isolated from the rest of the proof:
resource-leak checks do not correspond to run-time checks, so justifying one
must not introduce an assumption that could prove unrelated obligations.

Access-To-Subprogram Types
^^^^^^^^^^^^^^^^^^^^^^^^^^

The Built-in Theory for Subprogram Types
""""""""""""""""""""""""""""""""""""""""

A module ``Subprogram_Pointer_Rep`` for access-to-subprogram types is defined in
:file:`share/spark/theories/_gnatprove_standard.mlw`. It declares an abstract
``__subprogram`` type. A type ``__rep`` for all access-to-subprogram types is
then defined as a record with
two fields, one for the value designated by the access, considered to have type
``__subprogram``, and a flag to encode whether the access is ``null`` or not:

.. code-block:: whyml

  type __rep =
    { __is_null_pointer : bool;
      __pointer_value   : __subprogram }

Ordinary subprogram accesses require a null ``Global`` contract, including
inferred globals. The shared call model therefore needs no global-state
parameters. :ref:`Higher Order Specializations` allow function actuals that
read globals by adding those globals as inputs of the specialized call.
Types annotated ``Handler`` may designate subprograms with globals, but their
values cannot be called in SPARK and need no call model.

Representative Theory for Profiles
""""""""""""""""""""""""""""""""""

For callable access types, a module is generated for every designated profile,
a profile being an ordered sequence of subtypes for parameters with their
mode, as well as the result type for functions. It is shared between all
access-to-subprogram types with the same profile. Contracts and formal parameter
names do not affect this sharing. Naming and sharing conventions are documented
with ``Get_Profile_Theory_Name`` in :file:`src/why/why-atree-modules.ads`.
For procedures, the representative module is empty. For functions, it contains
a ``__call`` function and an axiom guard ``pred_call``. Here is an example.
Consider the access-to-function type ``F`` below:

.. code-block:: ada

   type F is access function (X1 : T1) return T;

The representative module will have the following form:

.. code-block:: whyml

  module Profile__In__T1__Return__T

    val function __call (subp : __subprogram) (x1 : t1) : t

    val predicate pred_call (result : t) (subp : __subprogram) (x1 : t1)
  end

Compared with the translation of regular functions, ``__call`` and
``pred_call`` have an additional ``subp`` parameter which is the subprogram
object which should be called.

As ``__call`` is shared between types with the same profile, converting an
access value preserves the result of logical calls through that value.
``pred_call`` serves the same role as the call guard for ordinary functions
(see :ref:`Functions`): it controls when the contract can be used.

For procedures, only the access type's contract is retained at indirect
calls. Preserving a known procedure's more precise postcondition through
``Access`` and conversions would require a shared postcondition predicate,
as for dispatching calls. That model has not yet been implemented.

Range Predicates
""""""""""""""""

Access-to-function types can have a contract. When they do, we need a way to
state that the ``__call`` function used in the logic domain respects this
contract. However, ``__call`` is shared between types with the same profile,
which can have different contracts. A global axiom for one type's contract
would also constrain functions accessed through the other types.

Instead, each access-to-subprogram type has an ``__in_range`` predicate on
subprogram values. For functions, it states that the value satisfies the
guarded postcondition axiom of that type. The dynamic invariant of an access
object uses this predicate to supply its type's contract for logical calls.
For procedures, it is simply ``True``: there is no logical call whose result
needs a postcondition axiom. Their contracts are still used for program calls.

The ``in_range`` predicate is declared in the definition module for the
access-to-subprogram type, but, because of dependencies, its definition is
supplied as an axiom in the completion module. As an example, let us consider
the access-to-function type ``F`` below:

.. code-block:: ada

   type F is access function (X1 : T1; ...) return T with
     Pre  => F_Pre (X1, ...),
     Post => F_Post (F'Result, X1, ...);

In the definition module for ``F`` a range predicate is declared:

.. code-block:: whyml

  val predicate __in_range (subp : __subprogram)

Its definition is deferred to the completion module. Ignoring implicit type
facts, it is:

.. code-block:: whyml

   axiom post_axiom: forall subp : __subprogram.
     __in_range subp <->
       (forall x1 : t1 ... .
         let result = __call subp x1 ... in
	   pred_call result subp x1 ... ->
	   f_pre x1 ... ->
	     f_post result x1 ...)

These contracts are used as axioms, so their feasibility is checked at the type
declaration. For every input satisfying the precondition, some result must
satisfy the postcondition and the result's type properties. Otherwise an
inconsistent axiom could prove ``False``, then prove the compatibility check
for taking a function's ``Access`` with the same infeasible contract.

An indirect call uses the access type's contract rather than the contract of
its run-time target. Recursion through an access value therefore does not by
itself make the target functions' contract axioms depend on one another.
The access type's contract still needs the feasibility check above.

Program Functions
"""""""""""""""""

The completion module of a callable access type also contains a program
function ``__call_`` which can be used to call a subprogram in the
program domain. Like for regular subprograms, this function will have the
pre and postcondition of the access-to-subprogram type if any. For functions,
the postcondition also states equality with the logic function ``__call``.
As an example, here is the program function generated for the access-to-function
type ``F`` above:

.. code-block:: whyml

  val __call_ (subp : __subprogram) (x1 : t1) ... : t
    requires { f_pre x1 ... }
    ensures  { result = __call subp x1 ... /\
                pred_call result subp x1 ... /\
                f_post result x1 ... }

The null check occurs when the designated subprogram value is extracted from
the access object, before the call to ``__call_``.
The generation conventions are documented in
:file:`src/why/gnat2why-subprograms-pointers.ads`. Taking a subprogram's
:ref:`Access attribute <Access Attribute on Subprograms>` connects these shared
call symbols to that subprogram's symbols. See
:ref:`Access-To-Subprogram Conversions` for the contract checks on conversions.

Type Completion
^^^^^^^^^^^^^^^

In addition to their main and possibly their representation module, types also
have completion modules. These contain declarations and axioms which may
reference entities (types, functions...) defined after the type declaration.
For example, scalar types with dynamic bounds need axioms giving the values
of bounds that do not have a static value.

Access types designating incomplete types need representation completions:
``Type_Completion`` and, when an initialization wrapper is needed,
``Init_Wrapper_Completion``. They connect the abstract designated-value
representation to the completed type once its dependencies are available.
See :ref:`Recursive Access Types` for the mechanism and its rationale.

Completion modules are located after modules for declarations but before modules
for checks in the generated mlw file. ``Generate_Type_Completion`` in
:file:`src/why/gnat2why-types.adb` generates the following modules as needed.
The module kinds below are those used by ``E_Module``:

.. list-table:: Modules generated during type completion
   :header-rows: 1
   :widths: 30 70

   * - Module
     - Contents
   * - ``Axiom``
     - The main completion, with the ``__axiom`` suffix. It defines dynamic
       invariants and non-static scalar bounds. For composite initialization
       wrappers, it also defines the initialization predicate, or completes
       its earlier declaration. Callable access-to-subprogram types have their
       call model completed here, as described above.
   * - ``Default_Initialialization``
     - The default initial assumption, including any default initial condition.
   * - ``Invariant``
     - The predicate for the type's own invariant.
   * - ``User_Equality_Axiom``
     - The definition of the ``user_eq`` symbol declared separately in
       ``User_Equality``.
   * - ``Dispatch_Equality_Axiom``
     - The definition of the root type's ``__dispatch_eq`` symbol declared in
       ``Dispatch_Equality``, including compatibility axioms for descendants.
   * - ``Move_Tree``
     - The reclamation tree and its operations for types containing allocated
       parts. It also completes any abstract tree declared in
       ``Incomp_Move_Tree``. See :ref:`Move Trees` for the tree model and
       :ref:`Recursive Access Types` for its abstract declarations and
       completions.
   * - ``Record_Rep_Completion``
     - The concrete extension representation and its connection to the abstract
       representation of a tagged record. See :ref:`Tagged types`.
   * - Tag compatibility module
     - For a tagged hierarchy root, axioms describing compatibility between
       the tags of its visible descendants. See :ref:`Tagged types`.

Separating invariants, default initialization, and equality from the type
representation is needed for soundness. Their definitions can use functions
whose verification in turn relies on properties of the type. The proof
dependency analysis identifies these cycles, and the translator withholds the
affected function axioms to prevent circular reasoning. This also handles
dependencies through subtype predicates.

Dynamic invariants
""""""""""""""""""
Not all information provided by Ada types is encoded into the corresponding
Why3 types. Here are some examples of information missing from Why3 types (see
``Gnat2Why.Expr.Compute_Dynamic_Invariant`` for the exhaustive list):

 * Type predicates and invariants,
 * Bounds of empty or dynamically constrained scalar types,
 * Bounds of dynamically constrained array types,
 * Discriminants of constrained record types...

This additional information is supplied by assumptions throughout Why3
programs. It is assumed for inputs on subprogram entry (see
``Compute_Dynamic_Property_For_Inputs``), added to the postcondition of
subprograms for subprogram outputs, assumed inside loops as implicit invariants
etc. To make these assumptions easier and to improve readability in the Why3
files, a Why3 predicate named ``dynamic_invariant`` is defined
in the main completion of ordinary type entities. Internal types (Itypes) may
depend on locally defined constants such as 'Old, so their dynamic invariants
are recomputed where needed. Standard Boolean and Universal_Fixed also have no
named dynamic invariant.

To see how this all works together, let's consider some examples. First,
here is a simple integer type with dynamic bounds:

.. code-block:: ada

   type Dyn_Int is new Integer range - Max .. Max;

Constants have already been introduced for its bounds, but ``Dyn_Int`` itself is
translated as a renaming of ``Integer``. The dynamic invariant of ``Dyn_Int``
simply states that its parameter is in the expected bounds:

.. code-block:: whyml

 predicate dynamic_invariant (expr : int) (is_init : bool)
    (skip_constant : bool) (do_toplevel : bool) (do_typ_inv : bool)  =
  (if is_init \/ dyn_int.first  <= dyn_int.last then
      dyn_int.first <= expr <= dyn_int.last
   else true)

The ``is_init`` guard prevents assumptions that could make the modeled type
empty, such as membership in an empty scalar range or an unsatisfiable subtype
predicate. The example still assumes range membership for an uninitialized
scalar when the range is nonempty. Uninitialized values cannot be read, so
assumptions about them need not describe their actual values; they must only
avoid making the proof context inconsistent. For initialized values, the
initialization checks justify the stronger assumptions. Initialization wrappers
and validity information also affect these guards.

The other arguments allow the caller to omit facts that are already known or
cannot yet be assumed: immutable bounds and discriminants at the top level,
the subtype predicate whose runtime checks are being proved, or type invariants
that the current subprogram may break. The API parameter meanings are documented
with ``Compute_Dynamic_Invariant`` in :file:`src/why/gnat2why-expr.ads`.

Subtype predicates are inlined in the type's dynamic invariant. For example,
consider a subtype for sorted arrays:

.. code-block:: ada

   subtype Sorted_Nat_Array is Nat_Array with
     Predicate => Is_Sorted (Sorted_Nat_Array);

Its dynamic invariant includes the subtype predicate alongside the array's
bounds and component properties. Here names are simplified and those other
properties are abbreviated:

.. code-block:: whyml

  predicate dynamic_invariant (x : sorted_nat_array) (is_init : bool)
    (skip_constant : bool) (do_toplevel : bool) (do_typ_inv : bool) =
    ... (* bounds and component properties *) /\
    (if is_init /\ do_toplevel then is_sorted x else true)

Scalar constants used in subtype predicates can be modeled as variables in
Why3. The predicate expression then has variable inputs, which are passed as
additional parameters to ``dynamic_invariant``. Here is an example:

.. code-block:: ada

   for I in 1 .. 10 loop
      declare
         subtype Dynamic_Bounds is Integer with
           Predicate => Dynamic_Bounds in 1 .. I;
      begin
         ...

Because loops are sometimes (partially) unrolled, scalar constants declared in
loops, and in particular loop indexes, are
translated as variables in Why. As a result, the dynamic invariant of
``Dynamic_Bounds`` takes the value of the loop index at the current iteration
as an additional parameter. Abbreviating the scalar range property, its
declaration is:

.. code-block:: whyml

  predicate dynamic_invariant (x : int) (is_init : bool)
    (skip_constant : bool) (do_toplevel : bool) (do_typ_inv : bool)
    (L_1__i : int) =
    ... (* scalar range property *) /\
    (if is_init /\ do_toplevel then 1 <= x <= L_1__i else true)

Let's now consider a more complex example. We can declare an option type
with a mutable discriminant containing a value of type ``Dyn_Int``, but only
when the discriminant is True:

.. code-block:: ada

   type Result_Type (Found : Boolean := False) is record
      case Found is
      when True  =>
        Result : Dyn_Int;
      when False =>
         null;
      end case;
   end record;

Here is its dynamic invariant:

.. code-block:: whyml

 predicate dynamic_invariant (expr : result_type) (is_init : bool)
    (skip_constant : bool) (do_toplevel : bool) (do_typ_inv : bool) =
  (if p__result_type__result__pred expr.__split_discrs then
    (if is_init \/ dyn_int.first  <= dyn_int.last then
      dyn_int.first <= dyn_int.to_rep expr.__split_fields.result <= dyn_int.last
     else true)
  else expr.__split_fields.result = dyn_int.dummy)

We see that dynamic invariants of composite types repeat the dynamic invariants
of their components. As ``Result_Type`` has a discriminant, the dynamic property
of the ``Result`` component is only assumed if the component is present. An
absent component instead has its type's dummy value, as explained under
:ref:`Record Types, Private Types, and Concurrent Types`. Note
that the ``dynamic_invariant`` predicate of components is not reused here. This
sometimes allows simplifications.

Let us now consider an unconstrained array of ``Result_Type``:

.. code-block:: ada

   type Result_Array is array (Positive range <>) of Result_Type;

Like for records, its dynamic invariant contains the invariant of its
components, but it also contains information about its bounds, which are only
assumed if ``skip_constant`` is false:

.. code-block:: whyml

 predicate dynamic_invariant (expr : result_array) (is_init : bool)
    (skip_constant : bool) (do_toplevel : bool) (do_typ_inv : bool) =
  (if skip_constant then true
   else dynamic_property Standard__positive.first Standard__positive.last
           (first expr) (last expr))
  /\ (forall i : int.
        (if (first expr) <= i <= (last expr) then
            ... (* dynamic invariant of get (to_array expr) i *)
         else true))

As a last example, let's use this array type to define a type of stacks. This
type contains a dynamically constrained subtype of ``Result_Array`` and features
a subtype predicate:

.. code-block:: ada

   type Result_Stack (Max : Natural) is record
      Content : Result_Array (1 .. Max);
      Length  : Natural;
   end record
     with Predicate => Length in 0 .. Max;

The frontend introduces an entity for the type of the content component. As
this entity is an Itype, it does not have its own dynamic invariant. However,
we will see it inlined in the invariant of ``Result_Stack``:

.. code-block:: whyml

 predicate dynamic_invariant (expr : result_stack) (is_init : bool)
    (skip_constant : bool) (do_toplevel : bool) (do_typ_inv : bool) =
  (if do_toplevel then
   (if is_init then
     0 <= to_rep expr.__split_fields.length <= to_rep expr.__split_discrs.max
    else true)
   else true) /\
   first expr.__split_fields.content = 1 /\
   last expr.__split_fields.content = to_rep expr.__split_discrs.max /\
   ... (* valid Content bounds and dynamic invariants of its elements *)

The first conjunct of the dynamic invariant of ``Result_Stack`` concerns the
subtype predicate. We see that it only holds if ``do_toplevel`` and ``is_init``
are true (that is, if ``expr`` is initialized and if we do not intentionally
skip this predicate). The second conjunct is the invariant of the ``Content``
component (the ``Length`` component has no dynamic invariant, it is of a static
scalar type, all necessary information is contained in its Why3 type). The
first part of the invariant of ``Content`` assumes the value of its bounds.
Note that this assumption is made even when ``skip_constant`` is true.
Immutable parts of objects are only split into separate objects at the top
level. A nested array can be replaced by assigning its enclosing object, so its
bounds must be included again when the enclosing object's dynamic invariant is
assumed.

Type invariants
"""""""""""""""

A type invariant has a named Why3 predicate in the separate ``Invariant``
module. Like dynamic invariants, it takes additional parameters for any
constants modeled as Why3 variables.

The type-invariant predicate is reused for both assumptions and checks.
``Compute_Dynamic_Invariant`` includes invariants assumed throughout the
analyzed unit in the reusable ``dynamic_invariant`` definition. Invariants
whose availability depends on the current scope are added at each use, outside
that definition. This keeps the named dynamic invariant independent of the
scope in which it is used.

When verifying the package that defines the type, the remaining invariants
are included in generated subprogram contracts: input invariants in the
precondition, and output and result invariants in the postcondition. The caller
checks the input invariants before the call and gets the output invariants from
its postcondition. Conversely, verification of the callee assumes the input
invariants on entry and proves the output invariants on return. These contract
conditions omit invariants relaxed for private subprogram parameters.
``Compute_Type_Invariant`` selects the applicable invariants, including those
of parent types and components, for both assumptions and checks. The selection
rules are shared with :file:`src/spark/spark_util-types.adb`.

Default initialization
""""""""""""""""""""""

For types which can be default initialized (ie. definite subtypes, see
``Can_Be_Default_Initialized``), a Why3 predicate named
``default_initial_assumption`` is defined for the type. It can be used to
express that a value of this type has been obtained by default initialization.
Note that even types which do not define full default initialization have a
``default_initial_assumption`` predicate. Parts of types which do not have
default values are simply left unspecified by the predicate. For example,
Ada does not define a default value for the standard type ``Integer``. A
predicate for the default initial assumption of values of type ``Integer`` is
still generated as variables of this type can be left uninitialized, but it does
not give any information on the value of its parameter:

.. code-block:: whyml

 predicate default_initial_assumption (x : int) (skip_top_level : bool) =
  true

As can be seen on the example above, the ``default_initial_assumption``
predicate takes a boolean ``skip_top_level`` argument in addition to the value
``x`` for which we want to assume default initialization. This argument can be
used to short circuit the top-level default initial condition of the type if
any. For example, consider the following ``Holder`` type which is empty when
default initialized:

.. code-block:: ada

   package P is
      type Holder is private with
        Default_Initial_Condition => Is_Empty (Holder);

      function Is_Empty (X : Holder) return Boolean;
   private
      type Holder is record
         Present : Boolean := False;
         Content : Natural := 0;
      end record;
      function Is_Empty (X : Holder) return Boolean is (not X.present);
   end P;

We can see that its default initial condition is ignored if ``skip_top_level``
is set to true:

.. code-block:: whyml

 predicate default_initial_assumption (x : holder) (skip_top_level : bool) =
  x.__split_fields.rec__present = false /\
  to_rep (x.__split_fields.rec__content) = 0 /\
  (if skip_top_level then true else is_empty x)

This short-circuit is used in particular in code that checks the
``Default_Initial_Condition`` aspect itself, see
``Gnat2Why.Expr.Check_Type_With_DIC``. It is also used to ignore default
initial conditions when checking that type invariants and subtype predicates
hold on default values, since the default initial condition itself is checked
assuming all applicable invariants and predicates (at least when the default
initial condition is checked at declaration, see ``Needs_DIC_Check_At_Decl``
and ``Needs_DIC_Check_At_Use``).

The default initial assumption has its own ``Default_Initialialization`` module,
as described above. Its expression can depend on functions used in component
defaults as well as in the default initial condition.

User equality
"""""""""""""
If primitive equality over a type which ultimately is a record is redefined by
the user, an axiom is provided to supply a definition for the primitive
equality function ``user_eq``. For example,
consider a type with two components, a ``Main`` component, which is the one we
care about, and another ``Ignored`` component which is only used for some
secondary usage, like logging. We define equality on this record type as
equality of the ``Main`` component only:

.. code-block:: ada

   type T_Rec is record
      Main    : Integer;
      Ignored : Integer;
   end record;

   function "=" (X, Y : T_Rec) return Boolean is (X.Main = Y.Main);

The "=" function above is translated as a normal function, producing a Why3
logic function named ``P__Oeq.oeq``. Using this function, we can define the
value of the generic primitive equality function ``user_eq`` introduced for
``T_Rec`` (see :ref:`Record equality` for usage of ``user_eq``):

.. code-block:: whyml

 axiom user_eq__def_axiom :
  (forall a b : t_rec__. P__t_rec.user_eq a b = P__Oeq.oeq a b)

The symbol is declared in ``User_Equality`` and its definition is supplied
separately in ``User_Equality_Axiom``. This keeps the declaration independent of
the overriding function and allows its function axioms to be withheld when
using them would create circular reasoning through equality.

Dispatching equality
""""""""""""""""""""

For tagged types which are not marked as limited, axioms are generated
to define the dispatching equality on those types.
There are two cases. If the primitive equality is overridden by a function
``Oeq`` on the root type of the hierarchy, then a single axiom is generated.
It states that ``__dispatch_eq`` is equal to the dispatching version of
``Oeq``:

.. code-block:: whyml

  axiom __dispatch_eq__def_axiom:
    forall attr__tag : int.
      forall a : root, b : root [__dispatch_eq attr__tag a b].
        __dispatch_eq attr__tag a b = Dispatch.oeq attr__tag a b

Otherwise, the dispatching equality is defined specifically for each new
derivation of the root type. A compatibility axiom is generated for each
type ``Child`` of the hierarchy giving a value to the ``__dispatch_eq``
function when the tag is known to be the tag of ``Child``. This is similar
to what is done for other primitive functions of tagged types. For predefined
equality, the axiom is:

.. code-block:: whyml

  axiom child__compat_axiom:
    forall a :root, b : root [__dispatch_eq Child.__tag a b].
      (attr__tag a = Child.__tag /\ attr__tag b = Child.__tag) ->
         __dispatch_eq Child.__tag a b =
           Child.bool_eq (Child.of_base a) (Child.of_base b)

If ``Child`` has a user-defined primitive equality, ``Child.user_eq`` replaces
``Child.bool_eq`` in this axiom.

The symbol is declared in ``Dispatch_Equality`` and its axioms are supplied in
``Dispatch_Equality_Axiom`` for the root of the hierarchy. Proof dependencies
include the possible overriding equalities, so their function axioms can be
withheld when using them would create circular reasoning through dispatching.

Wrapper types for Relaxed_Initialization
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
The ``Relaxed_Initialization`` aspect is a SPARK-specific construct. It relaxes
the additional initialization rules imposed by SPARK on selected objects and
allows their initialization to be verified by proof instead of flow analysis.
It was introduced to answer user needs for procedures only
initializing parts of an object, or only initializing objects conditionally.
Here is a motivating example:

.. code-block:: ada

  procedure Init_By_Proof with SPARK_Mode is

   type Int_Array is array (Positive range <>) of Integer;

   procedure Init_By_4 (A : out Int_Array; Error : out Boolean) with
     Relaxed_Initialization => A,
     Pre  => A'Length = 4,
     Post => (if not Error then A'Initialized)
   is
   begin
      A := (1 .. 4 => 10);
      Error := False;
   end Init_By_4;

   procedure Read (Buf   : out Int_Array;
                   Size  : Natural;
                   Error : out Boolean)
   with Relaxed_Initialization => Buf,
        Pre  => Buf'Length >= Size,
        Post => (if not Error then
                 Buf (Buf'First .. Buf'First + (Size - 1))'Initialized)
   is
      Offset    : Natural := Size mod 4;
      Nb_Chunks : Natural := Size / 4;
   begin
      if Offset /= 0 then
         Error := True;
         return;
      end if;

      Error := False;

      for Loop_Var in 0 .. Nb_Chunks - 1 loop
         pragma Loop_Invariant
           (Buf (Buf'First .. Buf'First + (Loop_Var * 4) - 1)'Initialized);
         Init_By_4 (Buf (Buf'First + Loop_Var * 4 .. Buf'First + Loop_Var * 4 + 3), Error);
         exit when Error;
      end loop;

   end Read;

   Buf   : Int_Array (1 .. 150) with Relaxed_Initialization;
   Error : Boolean;
   X     : Integer;
  begin
   Read (Buf, 100, Error);
   if not Error then
      X := Buf (10);
      X := Buf (110); -- medium: "Buf" might not be initialized
   end if;
  end Init_By_Proof;

In this example, initialization is only guaranteed if ``Error`` is false.
Additionally, ``Read`` only guarantees initialization of a prefix of length
``Size`` and initializes the array components four by four, which is currently
out of reach of the very simple heuristic used by flow analysis to recognize
loops which fully initialize an array.

We recognize objects for which we want to handle initialization by
proof using the ``Relaxed_Initialization`` aspect. It can be supplied on
standalone objects (like ``Buf`` above), on types (in which case it applies to
all parts of objects of this
type), and on subprograms (it applies to either parameters or the return
object). The attribute ``Initialized`` expresses that an object is initialized,
except for subcomponents whose types have ``Relaxed_Initialization``. These
subcomponents keep their initialization flags across ordinary assignments and
subprogram boundaries.

``Initialized`` is a ghost attribute because its proof meaning cannot be
implemented by an ordinary runtime test. GNAT implements it using
``Valid_Scalars``, which checks scalar validity, using ``Valid`` for scalar
values. An uninitialized value can happen to be valid, so a successful runtime
test does not establish initialization. The Why3 encoding instead tracks
initialization through assignments and contracts. At runtime, a test such as
``if X'Initialized then`` could therefore allow a read of uninitialized ``X``
inside the branch. Such reads can produce unpredictable behavior, which SPARK's
initialization checks are intended to prevent. GNATprove therefore assumes that
code referencing ``Initialized`` is not executed in the delivered program.
Contracts and other ghost code using the attribute can still be
executed during testing, under this assumption about the delivered program.
See ``SPARK_INITIALIZED_ATTRIBUTE`` in the User's Guide's list of proof
assumptions.

To keep these tests useful, proof does not generally assume that ``Initialized``
is false on uninitialized data. Otherwise, uninitialized values whose bit
patterns happen to be valid would cause frequent disagreements between proof
and execution. This choice keeps the two meanings close for testing; it does
not remove the non-execution assumption for the delivered program.

In our example, initialization of objects marked with ``Relaxed_Initialization``
is handled by proof whereas other objects are handled by flow analysis.
Handling initialization by proof requires more annotations because it relaxes
assumptions at subprogram boundaries. For example, a procedure reading the prefix
initialized by ``Read`` needs a precondition stating that this prefix is
initialized; it cannot assume that the whole array is initialized on entry.

Initialization is distinct from value validity. An initialization flag records
whether a value may be read under SPARK's initialization rules. It does not
record whether a bit pattern represents a value of its Ada type. Initialized
but potentially invalid values are tracked separately; initialization wrappers
do not replace that model.

Wrapper Types
"""""""""""""

If expressions of a given type might have relaxed initialization (see
``Has_Init_Wrapper``), we introduce a special Why3 `wrapper` type for
them (see ``Declare_Init_Wrapper``).

We use wrappers instead of a separate initialization tree, like the move and
validity trees, because initialization information must follow values through
expressions. For example, an aggregate
containing a partially initialized record must retain which fields of that
record are initialized. With wrappers, the flags are part of the record value
used to build the aggregate. With a separate tree, expression translation would
have to compute and combine both values and initialization trees. Validity and
move information are generally handled on objects, so their separate trees do
not need to follow intermediate expression values in this way.

For scalar types, the wrapper type is
a record with two components, the value of the scalar, and a boolean flag
encoding whether it is initialized or not. This type is declared in a separate
``<My_type>__init_wrapper`` module. For example, in ``Init_By_Proof`` above, the
type ``Integer`` might be used for expressions with relaxed initialization,
as we can access the value of an array object annotated with the aspect. Here
is the wrapper module introduced for ``Integer``:

.. code-block:: whyml

  module Standard__integer__init_wrapper

    type integer__init_wrapper = {
      rec__value   : integer ;
      __attr__init : bool
    }

    function of_wrapper (a : integer__init_wrapper) : integer =
      rec__value a

    function to_wrapper (x : integer) : integer__init_wrapper =
      { rec__value = x; __attr__init = True }

  end

The usual reference declarations are omitted here. The conversion to the wrapper
marks the value as initialized. The conversion from the wrapper extracts the
value; it does not itself check the flag. Its use for a read must be justified
by an initialization check or by flow analysis.

The wrapper type of a composite type or access-to-object type is not really a
wrapper. It is constructed similarly to the usual translation of the type, but
uses wrapper types for its components. Immutable discriminants of records and
array bounds do not have an initialization flag as they cannot be modified.
For private types whose full view is outside SPARK, the abstract value has a
single initialization flag because its components are unavailable. A record
with a part hidden from SPARK similarly has a flag for that abstract part,
alongside the wrappers for its visible components.
For example, ``Int_Array`` uses a map whose elements have the integer wrapper
type. Each element therefore has its own initialization flag. The shared array
theories and conversion modules are generated in the same way as for arrays
with different component types; see :ref:`Array Types`.

Mutable discriminants and access addresses can never be uninitialized in Ada
but reading them might be inconsistent with the rules of SPARK (for parameters
of mode OUT or global variables of mode Output). This might cause incorrect
dependencies to be inferred if an incorrect mode is used. To avoid that, we
need to generate initialization checks for them. An additional top-level
initialization flag is introduced for types with mutable discriminants and for
access-to-object types. It is checked whenever (any part of) the object is
accessed. Note that the flag for the access types is necessary even though the
pointer address is not modelled. It protects the ``Is_Null`` flag and the
bounds and discriminants of the designated object. Here is an example of
a wrapper type introduced for an access to an ``Int_Array``. We see that it has
its own initialization flag, which will be used when the pointer is
dereferenced or compared to null. The designated value itself is a wrapper
type as it could not be initialized even if the pointer itself is:

.. code-block:: whyml

  type __rep = {
    pointer_value : int_array__init_wrapper;
    is_null_pointer : bool;
    __attr__init : bool
  }

The field names are shortened here.

For an access type designating an incomplete type, the wrapper initially uses
an abstract designated value. Its separate ``Init_Wrapper_Completion`` module
connects that value to the designated type's wrapper when the full view is
translated. This is the same mechanism used for ordinary pointer
representations; see :ref:`Recursive Access Types`.

When translating an expression or an object of a type which has a wrapper type,
we choose between the wrapper type and the standard type depending on whether or
not the expression (the object) has relaxed initialization, see
``Expr_Has_Relaxed_Init`` and ``Obj_Has_Relaxed_Init``.
Representation and conversion conventions are described in
``src/why/why-gen-init.ads``.

Initialization Checks
"""""""""""""""""""""

Without applicable subtype predicates, ``Initialized`` is a conjunction of
initialization flags (see ``Compute_Is_Initialized``). Subcomponents whose types
have ``Relaxed_Initialization`` are excluded. These checks follow the shape of
the object: only array elements within the bounds and record fields present for
the current discriminants are considered. A null pointer has no designated
value to check. These guards prevent unused parts of the Why3 representation
from imposing initialization requirements on the Ada object.

Translating ``Initialized`` inspects initialization information without reading
the selected value. Otherwise, the attribute would require the very
initialization it is meant to test. Checks needed to identify the selected part
still apply: for example, ``A (I)'Initialized`` requires a valid index within
the array bounds, but does not require the element's value to be initialized.
Similarly, ``X.F'Initialized`` does not check the predicate of ``X`` just to
locate ``F``. If ``F`` is composite, its own predicates can contribute to the
attribute's Boolean result, as explained below.

For example, the failed initialization check
at the end of the ``Init_By_Proof`` procedure is translated as:

.. code-block:: whyml

  assert { (get (map__content buf) 110).__attr__init }

The initialized-prefix condition in the postcondition of ``Read`` becomes:

.. code-block:: whyml

  ensures { not error ->
              (forall i : int.
                 buf__first <= i <= buf__first + size - 1 ->
                   (get (map__content buf) i).__attr__init) }

When the destination of a composite assignment has relaxed initialization,
we copy the source's component flags along with their values. If the source is
only partially initialized, the destination becomes partially initialized too,
even if it was fully initialized before the assignment. Whether the destination
has relaxed initialization is determined by its annotations. If it does not,
an initialization check is performed on the source, except for subcomponents
whose types have ``Relaxed_Initialization``.

This propagation is possible because a composite copy need not read the values
of its individual scalar components. A scalar copy does read its value, so it
requires an initialization check to avoid an Ada bounded error. A subtype
predicate can impose the same initialization requirement on a composite copy;
the predicate rules below explain when this happens.

We introduce initialization checks when converting from a wrapper type to any
normal type (see ``Insert_Checked_Conversion``). A conversion used to fetch an
``out`` parameter for a subsequent update need not read its old value and can
omit this check. The API documents how such checks are disabled.

Note that an initialization check might be required even for a Why3 expression
which doesn't have a wrapper type (see ``Insert_Initialization_Check``). Indeed,
if a type is annotated with the ``Relaxed_Initialization`` aspect, then
components of this type in a composite type are translated using the wrapper
type, even in the normal translation of the composite
(see ``W_Type_Of_Component``).

In general, initialization checks inserted on conversions are partial
in the sense that they do not include components whose type is annotated
with ``Relaxed_Initialization``. This is because the
type of these components is a wrapper type even in the standard translation
of the type.

Additional initialization checks are manually inserted when translating
operators on composite types which imply a read of its components (equality,
logical operations...). As opposed to the ones introduced for conversions, these
checks include the components read by the operation. Predefined equality on
arrays and records, for example, reads components recursively. A component
compared using its user-defined equality only needs the initialization required
at that subprogram boundary.
As a result, there might be two initialization checks on an
operand of an operator. One to convert the operand to its standard type, and one
to ensure that components whose type is annotated with
``Relaxed_Initialization`` are also initialized. These checks are not
duplicates, one or the other might fail while the other passes.

Composite wrappers normally have a named ``is_initialized`` predicate for
conversion checks. It checks the parts required by the ordinary representation,
excluding components whose types have relaxed initialization. Its definition
also includes applicable subtype predicates, as explained below. For recursive
types, this predicate can be declared before its definition is available and
completed by an axiom in the type's main completion module. This lets pointer
conversions refer to it before the designated full view has been translated.

Types With Predicates
"""""""""""""""""""""

In general, SPARK ensures that the predicate holds on all objects and
expressions of a type with a predicate (predicate checks are inserted on all
updates, see ``One_Level_Update``). This makes it possible to assume the
predicates in the dynamic invariant of the type, provided the object is known
to be initialized (see ``Compute_Dynamic_Invariant``). This is no longer the
case with relaxed initialization, as some components can remain uninitialized
even at a boundary where initialization is normally assumed. Therefore, the
predicate should depend on the initialization status of the particular object
or component. For scalar types, it is easy, as each object or component has its
own initialization flag. It is therefore enough to guard the predicate with
this flag in its dynamic invariant. As an example, consider
the subtype ``S`` defined below:

.. code-block:: ada

   type My_Int is new Integer with
     Relaxed_Initialization;
   function B return My_Int is (1);

   subtype S is My_Int with
     Predicate => S <= B;

   type H is record
      C : S;
   end record;

The predicate on objects and components of type ``S`` in their dynamic invariant
will be conditioned to their initialization flag, as can be seen in the dynamic
invariant of ``H`` defined above:

.. code-block:: whyml

  predicate dynamic_invariant
   (expr: h) (is_init: bool) (skip_constant: bool)
   (do_toplevel: bool) (do_typ_inv: bool)
  =
    (if expr.__split_fields.rec__c.__attr__init then
        let temp = expr.__split_fields.rec__c in
          of_wrapper temp <= b ()
     else true)

For composite wrappers, the component flags do not establish that the subtype
predicates hold. These predicates can relate several components and can have
different initialization requirements. A predicate declared on a type without
``Relaxed_Initialization`` requires initialization of the parts whose types do
not have the aspect. A predicate declared on a type with the aspect can allow
partial initialization. Inherited predicates retain the requirements of the
type where they were declared, so both kinds can apply to the same type.

We could introduce a flag recording that the applicable predicates hold to
reduce the number of predicate checks: currently, they are checked at every
value read, which can generate many checks. We have not done so yet. This is
consistent with the rest of the tool: the Why3 datatypes represent values and
properties guaranteed by the Ada type system and SPARK assumptions, rather
than cache proof results. Subtype predicates need not hold on a partially
initialized composite, so such a flag would record a property that must be
proved separately.

The dynamic invariant of a composite wrapper does not assume its subtype
predicates. Instead, ``Initialized`` combines the initialization checks described
above with the applicable predicates (see ``Compute_Is_Initialized``). This
establishes subtype membership for the parts covered by those checks. At object
and subprogram boundaries where the predicates are required to hold, they are assumed
separately by ``Compute_Dynamic_Inv_And_Initialization``.

As an example, consider the following record type:

.. code-block:: ada

   type R is record
      F, G : Integer;
   end record with
     Predicate => F < G;

If ``X`` is an object of type ``R`` with relaxed initialization, the attribute
``X'Initialized`` is translated in the following way:

.. code-block:: whyml

  x.__split_fields.rec__f.__attr__init /\
  x.__split_fields.rec__g.__attr__init /\
  let temp = of_wrapper x in
     to_rep (temp.__split_fields.rec__f)
       < to_rep (temp.__split_fields.rec__g)

The following type ``H1`` has a predicate that allows partial initialization:

.. code-block:: ada

   type H1 is record
      C : R;
      I : Integer;
      B : Boolean;
   end record with
     Relaxed_Initialization,
     Ghost_Predicate => B'Initialized
     and then
       (if B then C'Initialized and then I'Initialized and then C.G < I);

   procedure P1 (X : H1) with
     Global => null
   is
   begin
      if X.B then
         pragma Assert (X.C.F < X.I);
      end if;
   end P1;

   procedure Q1 (X : out H1) with
     Global => null,
     Relaxed_Initialization => X
   is
   begin
      null;
   end Q1;

The example uses ``Ghost_Predicate`` because ``Initialized`` is ghost.
At the beginning of ``P1``, we can assume that the predicate of ``H1`` holds,
as SPARK checks the predicate at the subprogram boundary. Since ``H1`` is
annotated with ``Relaxed_Initialization``, its predicate does not enforce the
initialization of ``X`` completely, but it is enough to prove the assertion
inside ``P1``. Similarly, the predicate check at the end of ``Q1`` does not
require the whole object to be initialized, as can be seen below:

.. code-block:: whyml

    assert
        { x.__split_fields.rec__b.__attr__init
          /\
           (if of_wrapper x.__split_fields.rec__b then

	      (* X.C'Initialized *)
              (let temp___c  = x.__split_fields.rec__c in
	          temp___c.__split_fields.rec__f.__attr__init
	       /\ temp___c.__split_fields.rec__g.__attr__init
	       /\  let temp__c_init = of_wrapper temp___c in
                       to_rep temp__c_init.__split_fields.rec__f
                            < to_rep temp__c_init.__split_fields.rec__g)

	      (* X.I'Initialized *)
              /\ x.__split_fields.rec__i.__attr__init

	      (* X.C.G < X.I *)
	      /\ to_rep
	            (of_wrapper x.__split_fields.rec__c.__split_fields.rec__g)
		       < to_rep (of_wrapper x.__split_fields.rec__i)
            else true) }

For the type ``H2`` below, it is different. As it is not annotated with
``Relaxed_Initialization``, its predicate enforces the complete initialization
of ``X``.

.. code-block:: ada

   type H2 is record
      C : R;
      I : Integer;
   end record with
     Predicate => C.G < I;

   procedure P2 (X : H2) with
     Global => null,
     Relaxed_Initialization => X
   is
   begin
      pragma Assert (X.C.F < X.I);
   end P2;

   procedure Q2 (X : out H2) with
     Global => null,
     Relaxed_Initialization => X
   is
   begin
      null;
   end Q2;

At the end of ``Q2``, both the initialization and the predicate of ``X`` are
verified:

.. code-block:: whyml

   (* Initialization check *)
   assert
       { (let temp___c  = x.__split_fields.rec__c in
	     temp___c.__split_fields.rec__f.__attr__init
	  /\ temp___c.__split_fields.rec__g.__attr__init
	  /\  let temp__c_init = of_wrapper temp___c in
                 to_rep temp__c_init.__split_fields.rec__f
                      < to_rep temp__c_init.__split_fields.rec__g)
           /\ x.__split_fields.rec__i.__attr__init }
   (* Predicate check *)
   assert
       { to_rep (of_wrapper x.__split_fields.rec__c.__split_fields.rec__g)
	  < to_rep (of_wrapper x.__split_fields.rec__i) }


For parameters of mode IN or IN OUT like the parameter ``X`` of ``P2``, the
predicate requires initialization on entry and on subsequent copies into the
object. These checks prevent ``X`` from becoming uninitialized,
so we do not use the wrapper type for them. Scalar input parameters similarly
use the ordinary representation because passing them already requires a read
of their value.

The null bodies of ``Q1`` and ``Q2`` illustrate the generated obligations;
they do not satisfy them. ``Q1`` has not established even ``B'Initialized``,
and ``Q2`` has not established initialization or its predicate.

Note that, like for normal objects, the predicate of objects annotated with
``Relaxed_Initialization`` is enforced at every update. In addition, we have
chosen to also check it at every value read (namely on identifiers and component
accesses, see ``Transform_Identifier`` and ``One_Level_Access``). Unlike
normal objects, checks on updates are not sufficient as the predicate still
might not hold if the object is not initialized. Still, we could have chosen
to only verify it where mandated by Ada (parameter passing, default
initialization, type conversion etc). We chose to check all reads as it was
simpler to be sure that no language mandated checks were missed. Accesses used
only to locate a part for an update or to test ``Initialized`` do not require
these read-time predicate checks on their prefixes.

Split Form For Wrappers
"""""""""""""""""""""""

Scalar objects with relaxed initialization can be in split form. Their value
and initialization flag are then stored separately, so updating the flag does
not require rebuilding a record wrapper. The flag is only introduced when
initialization is not always known, for example for an ``out`` parameter or a
variable without full default initialization. Reads still require the same
initialization checks. The item layout and flag conventions are
described in ``src/why/why-gen-binders.ads``.

Objects
-------
Mutable and Constant Objects
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Objects are translated differently depending on their type, but also depending
on whether they are mutable or not. Let's first consider constants. Are
translated as constants in Why3 all Ada objects which are constants in Ada
except:

 * Loop parameters, as they need to be updated during the generated Why3 loop;
 * Scalar constants with variable inputs declared in unrolled loop, or before
   the loop invariant in normal loops, because they can appear twice with
   different values due to loop handling (see
   ``SPARK_Definition.Check_Loop_Invariant_Placement`` and
   ``SPARK_Definition.Check_Unrolled_Loop``);
 * Volatile in parameters with asynchronous writers;
 * Constants of an access-to-variable type which is not a private type.

See ``Is_Mutable_In_Why`` for more details.

Ada objects which are constant in Why3 are translated as functions without
parameters. Here are is an example:

.. code-block:: ada

   B : constant Boolean := True;

This declaration is translated into a single uninterpreted logic function
without parameters:

.. code-block:: whyml

 module P__b
   function b2 : bool
 end

If the definition of the constant does not depend on variables, it is supplied
as an axiom in a completion module for the object:

.. code-block:: whyml

 module P__b___axiom
   use        P__b

   axiom b__def_axiom :
    P__b.b = True
 end

Variables on the other hand, are translated using an uninterpreted program
declaration returning an object of a reference type. If we remove the
``constant`` keyword form the declaration of ``B``, the translation will become:

.. code-block:: whyml

 module P__b
  val b : bool__ref
 end

No axiom is generated for the value of a variable. The value will be provided
as an assignment at the location of the object declaration:

.. code-block:: whyml

 P__b.b.bool__content <- True;

In fact, even for constants code might be generated at the location of the
object declaration to specify the value of the constant. This can have several
reasons:

 * No axiom can be generated for the constant, or the axiom might be
   incomplete. For example, we can't currently generate axioms for non-static
   constants in protected objects, and axioms for constants that are defined
   using a recursive call might be incomplete.
 * Repeating the value of the constant in a different form might help provers.

The relevant subprograms for the handling of constant values are:

 * Gnat2why.Decls.Translate_Constant_Value for the generation of the axiom for
   the constant, if possible.
 * Gnat2why.Expr.Assignment_Of_Obj_Decl for the insertion of assumptions in
   some cases
 * Gnat2why.Expr.Assume_Value_Of_Constants for the insertion of assumptions for
   constants

Scalar Objects
^^^^^^^^^^^^^^
For some Ada types, expressions, and in particular objects, can be either in a
open, or split, form or in a closed, or abstract, form. This is the case for
most scalar types, arrays, records, and pointers. ``Why.Inter.EW_Abstract`` and
``Why.Inter.EW_Split`` are used to create the split and abstract form of
a type. Note that, whereas all types have an abstract form (it is always OK to
call ``EW_Abstract`` on an Ada type), only scalar types and array types have
a split form (even if record and access objects do have a split form, see
corresponding section).

Scalar types which are not standard boolean use their representative type as a
split form: When an expression of a scalar type which is not standard boolean is
in split form, if it is translated as a value of the underlying representative
type (mathematical integer, bitvector, floating point type...). Objects of
scalar types are always in split form (see ``Use_Split_Form_For_Type``). For
example, let's consider the following objects:

.. code-block:: ada

   X : constant Integer := 15;
   Y : Integer := 15;

As ``Integer`` is a signed integer type, its representative type is ``int``:

.. code-block:: whyml

 function x : int

 axiom x__def_axiom :
   P__x.x = 15

 val y : int__ref

Using this split form for scalar types avoids having to introduce conversions
between the closed form and the
representative type for computations. Missing information about the
bounds of the objects are supplied as assumptions
through dynamic invariant (see the corresponding section in Type Completion).

Array Objects
^^^^^^^^^^^^^
For arrays that are mutable in Why, separating the content of the array from its
bounds makes proof easier. Indeed, it allows to translate the bounds as
constants, so that their preservation comes for free, while keeping a
reference for the content. To achieve this,
unconstrained and dynamically constrained array types use the underlying map
type as a split form. Since the separation is only used for preservation of
information, only mutable arrays are in split form. Let us look at some
examples.

As array constants are in closed form, constants of constrained array types with
static bounds will be translated as functions returning the underlying Why3 map
and constants of unconstrained array types, or of dynamically constrained array
types, as functions returning the corresponding abstract type:

.. code-block:: ada

   type Nat_Array is array (Positive range <>) of Natural;

   A1 : constant Nat_Array (1 .. 10) := (1 .. 10 => 15);
   A2 : constant Nat_Array := (1 .. 10 => 15);

The type of ``A1`` is statically constrained. It will be translated as a Why3
map, the bounds being declared directly inside the module for the Ada type of
``A1``:

.. code-block:: whyml

 function a1 : Array__Int__Standard__natural.map

The type of ``A2`` is unconstrained. It will be translated using the abstract
type introduced for ``Nat_Array`` from which both the bounds and the
underlying map can be queried:

.. code-block:: whyml

 function a2 : P__nat_array.nat_array

Let us now consider mutable arrays:

.. code-block:: ada

   A1 : Nat_Array (1 .. 10) := (1 .. 10 => 15);
   A2 : Nat_Array := (1 .. 10 => 15);

Since the bounds of statically constrained array types are translated
separately, we simply need a global reference for the content of ``A1``:

.. code-block:: whyml

 val a1 : Array__Int__Standard__natural.map__ref

For unconstrained or dynamically constrained array types, mutable objects are
split into different parts, the bounds, which are constant, and the mutable
content. For one-dimensional arrays, this results in the declaration of three
Why3 objects:

.. code-block:: whyml

 val a2 : Array__Int__Standard__natural.map__ref

 function a2__first : Standard__integer.integer

 function a2__last : Standard__integer.integer

A draw back of this approach is that array variables need to be
reconstructed using the ``of_array`` conversion function when they are involved
in computations. Indeed, as the bounds are associated to Ada objects, they
cannot easily be retrieved from more complex expressions, therefore requiring
the switch to closed form.

Record Objects
^^^^^^^^^^^^^^
Like arrays, records can have both constant and variable parts. The regular
components of a mutable record object are always mutable, whereas discriminants
are constant most of the time, and tag of tagged record objects can never
change. As a result, it is interesting to split record objects so that
preservation of constant parts can come for free. However, unlike array objects,
record objects do not have a single main mutable part. As a result, there is not
a single type for the split form of a record and record expressions which are
not objects are never in split form (see assertions in ``New_Kind_Base_Type``
enforcing that it is never called with kind ``EW_Split`` on record types).

Record constants are in closed form. They are translated as a single
uninterpreted logic function of the corresponding abstract record type with
no parameters.

On the other hand, a mutable record object may produce up to four declarations:

 * A mutable Why3 record for the regular components of the Ada record type,
 * A Why3 record for the discriminants of the Ada record type (mutable only
   if the Ada type has defaulted discriminants),
 * A mathematical integer constant for the tag attribute of tagged types, and
 * A boolean constant for the constrained attribute of records with defaulted
   discriminants.

As an example, let us consider the following tagged Ada record:

.. code-block:: ada

   type Tagged_Rec is tagged record
      F : Integer;
   end record;

   T : Tagged_Rec := (F => 15);

As it has no discriminants, two declarations are emitted for it, a reference for
the regular components and a constant for the tag attribute:

.. code-block:: whyml

 val t2__split_fields : P__tagged_rec.__split_fields__ref

 function t2__attr__tag : int

Let us now consider a record type with mutable discriminants:

.. code-block:: ada

   type Option (Present : Boolean := False) is record
      case Present is
      when True  =>
        Content : Integer;
      when False =>
         null;
      end case;
   end record;

   O1 : Option := (Present => True, Content => 15);

As ``Option`` has defaulted discriminants, both its regular and its discriminant
parts are mutable. However, its constrained attribute is not:

.. code-block:: whyml

 val o1__split_fields : P__option.__split_fields__ref

 val o1__split_discrs : P__option.__split_discrs__ref

 function o1__attr__constrained : bool

If the discriminant of ``Option`` is fixed in its Ada type, the discriminant
part will be declared as a constant:

.. code-block:: ada

   O2 : Option (True) := (Present => True, Content => 15);

.. code-block:: whyml

 val o2__split_field : P__To2S.__split_fields__ref

 function o2__split_discrs : P__option.__split_discrs

 function o2__attr__constrained : bool

Access Objects
^^^^^^^^^^^^^^
Access objects are made of two parts: a boolean flag to encode whether the
access is null and the value designated by the
access. Whereas the designated value is mutable as soon as the access object
is not entirely constant, the ``is_null`` flag can be constant.
It happens when we are declaring a constant of an access-to-variable type
which is not a private type (those objects are not constant in Why as the
value they designate can be modified). Thus, it may be interesting to split
access objects so that preservation of constant parts can come for free.
Like for records, we have not introduced a type of kind ``EW_Split`` for access
types, and access expressions which are not objects are never in split form.

Constants of an access-to-constant type are in closed form. They are translated
as a single uninterpreted logic function of the corresponding abstract access
type with no parameters.

For other access objects, two declarations are produced: one for the boolean
``is_null`` flag and one for the designated value. The
latter is always a reference, whereas the former can be a constant or a
variable depending on whether the Ada access object is mutable or not.

As an example, let us consider the following Ada access constant:

.. code-block:: ada

   type Int_Acc is access Integer;

   X : constant Int_Acc := new Integer'(15);

As it is a constant, its boolean ``is_null`` flag is constant.
However, the designated value can be modified, since ``Int_Acc`` is an
access-to-variable type:

.. code-block:: whyml

 val x__pointer_value : Standard__integer.integer__ref

 val constant x__is_null_pointer : bool

Let us now consider a variable:

.. code-block:: ada

   Y : Int_Acc;

Here, both the designated value and the ``is_null`` flag
are mutable, so we declare two references:

.. code-block:: whyml

 val y__pointer_value  : Standard__integer.integer__ref

 val y__is_null_pointer : bool__ref

In addition, if the access object is a local borrower (a constant or a
variable of an anonymous access-to-variable type, see ``Is_Local_Borrower``),
its module also contains the declarations for two additional objects. One
is a constant which stands for the value of the borrowed expression at the
end of the borrow, the other is a variable, holding the value at the end of
the borrow of the structure designated by the borrower at all time. This is
the reason why it is a variable, as the part of the borrowed structure
designated by the borrower might change during the borrow.
We call these objects predicted values as they are used and linked together
during the borrow prior to assuming their actual value when the end of the
borrow is actually reached.

Consider, as an example, the following borrow:

.. code-block:: ada

   B : access Integer := Y;

In the module generated for ``B``, in addition to the declarations of the
components described previously, we generate:

.. code-block:: whyml

   val b__brower_at_end : Test__T2b.t2b__ref

   val function b__borrowed_at_end : Test__T2b.t2b

Here ``t2b`` is the type introduced by the compiler for the anonymous type of
``B``. We can see that, even though ``Y`` has type ``Int_Acc``, the borrowed
expression has the type of the borrower. This is important as it is possible
that constraints on the actual type for the borrowed expression might be broken
during the borrow.

Effect-Only Objects
^^^^^^^^^^^^^^^^^^^
Global annotations may refer to state whose exact definition is hidden from the
analysis. The most common occurrence of this case is for state abstraction. When
analyzing a unit, abstract states defined in other units are opaque for SPARK.
To encode this unknown state, abstract states are translated in Why as a global
variable of the predefined ``__private`` type. Here is an example:

.. code-block:: ada

   package Withed_Unit with
     Abstract_State => State
   is
      ...
   end Withed_Unit;

   with Withed_Unit;
   procedure P with Global => (In_Out => Withed_Unit.State);

A global reference is introduced in Why for the abstract state of
``Withed_Unit``, so that it can be used in the translation of ``P``:

.. code-block:: whyml

 module Withed_unit__state
   use import "_gnatprove_standard".Main

   val state  : __private__ref
 end

 val p (__void_param : unit) : unit
  reads  {Withed_unit__state.state}
  writes {Withed_unit__state.state}

Global annotations can also refer to entities which are not in SPARK.
In the following example, ``P`` can state that it modifies ``V``
even if ``V`` is declared in a package with ``SPARK_Mode => Off``.

.. code-block:: ada

   package Nested with
     SPARK_Mode => Off
   is
      V : access Integer;
   end Nested;

   procedure P with Global => (In_Out => Nested.V);

``V`` should be translated to express the data dependency, but we should
not try to translate its type, which may not be in SPARK (here for example it is
an access type, but the translation mechanism would be the same if it was an
integer). To this aim, we emit a dummy variable declaration for ``V`` using the
predefined ``__private`` type:

.. code-block:: whyml

 module P__nested__v
   use import "_gnatprove_standard".Main

   val v  : __private__ref
 end

 val p (__void_param : unit) : unit
  reads  {P__nested__v.v}
  writes {P__nested__v.v}

Remark that dummy variables for effects of subprograms will also be defined for
generated Global contracts (when no user provided global contract is supplied
for a subprogram).

Subprograms
-----------

Global View
^^^^^^^^^^^

The declaration of a SPARK subprogram will lead to the declaration of
one or several Why function declarations and axioms located in one or
several modules.

Procedures
""""""""""

For procedures that are not primitives of tagged types, have no
refined postcondition, and are not boundary subprograms of any type
with an invariant, only one abstract program function is declared in
Why (see ``Gnat2why.Subprograms.Generate_Subprogram_Fun``). It is supplied
in a module named <my_subprogram_full_name>___program_fun and mimics as much
as possible the effects and contracts of the Ada procedure.

As an example, let us consider the following minimalist procedure declaration:

.. code-block:: ada

     procedure P;

It leads to the declaration of a single Why program function as follows:

.. code-block:: whyml

    module P__p___program_fun
     val p (__void_param : unit) : unit
      requires { true }
      ensures { true }
    end

Since the procedure P has no parameters, its Why translation has a
single unit argument. The pre and postconditions of the Why program
function (introduced by requires and ensures) are set to True because
the P procedure has no explicit or implicit contracts. Note that the
Why declaration is introduced by the val keyword, which means that it
won’t have a body. Indeed, in our translation, verification of a
subprogram body is completely decorrelated from the declaration of the
subprogram. Said otherwise, this declaration will be used to translate
calls to the P procedure, but not to verify it.

Functions
"""""""""

For functions, declarations are separated in three modules to avoid
circularity issues caused by forward references of other entities in
function contracts. The first module, <my_subprogram_full_name>___logic_fun,
contains a (generally abstract) logic function declaration for
the Ada function, along with a guard predicate which is used to
specifically determine when the function is actually called. This package is
then exported as is in a module named by the subprogram full name. It is the
logic function from this module which is used to transform function calls
occurring in assertions in the generated Why code, as Why does not allow calling
program functions in assertions. Since this function is logic, it is
terminating and complete, unlike the translated Ada function. This
means that special care should be taken when giving a meaning to such
a function. More precisely, we only give information about the result
of a why logic function in the context of its precondition. This information is
supplied through axioms generated in separate modules named
<my_subprogram_full_name>___post_axiom for the postcondition and
<my_subprogram_full_name>___def_axiom for the body of expression functions.
The additional axiom modules are included each time the logic function is used
in VCs modules. In cases where we detect that the entity for which we generate
VCs and the function are inter-dependent (for recursive functions in particular)
the axioms are not included. The guard predicate is used to give
additional protection against errors in function contracts by only
assuming the information on actual calls of the subprogram. It is not
required if all functions are thoroughly verified, which is why its
usage can be disabled by the --function-sandboxing=off option.

As an example, let us look at the following Ada function:

.. code-block:: ada

     function F return Boolean;

Here are the logic declarations introduced for F:

.. code-block:: whyml

    module P__f___logic_fun
     function f (__void_param : unit) : bool
     predicate f__function_guard (result : bool) (__void_param : unit)
    end

To avoid circularity issues, the contract of the logic function f is
not given in this module, but is postponed until after all functions,
types, and objects have been defined.

Just like for procedures, a Why program function is defined for Ada
functions in a second module named <my_subprogram_full_name>___program_fun:

.. code-block:: whyml

    module P__f___program_fun
     val f (__void_param : unit) : bool
      requires { true }
      ensures { result = P__f___logic_fun.f ()
	     /\ P__f___logic_fun.f__function_guard result () }
    end

Axioms are generated for the contract of the associated Why logic function and
its definition (if any) in separate modules. Here is the axiom introduced
for F:

.. code-block:: whyml

    module P__f___post__axiom

     axiom f__post_axiom :
      (forall __void_param : unit.
       (let result = P__f.f __void_param in
	  if P__f.f__function_guard result __void_param then
	  true))
    end

Like procedure P, the function F has no contract. However, we can see
that the associated Why program function has a postcondition. It is
used to link the two definitions of f (the logic one and the program
one). Each time the program function f is called, we will assume that
F’s guard predicate is true, and that the result of the call is equal
to the result of the logic function f. Remark that the symbols used in this
postcondition are the symbols declared in P__f___logic_fun. This is so that
programs using only the program function do not pull the axioms associated
to the logic function.

We see that the P__f___post__axiom module also contains a post axiom for the
logic function f (see ``Gnat2why.Subprograms.Generate_Axiom_For_Post``).
It is used to state that results of f are always compliant with its
postcondition. Since F has no postcondition, this axiom is useless
here (it allows to deduce True). However, we can see by its form how
the guard predicate is used to protect against wrong contracts which
could lead to false post axioms if the function is not verified.

Borrowing traversal functions (see ``Is_Borrowing_Traversal_Function``)
return local borrowers. We need to be able to reconstruct the value of the
borrowed parameter at the end of the borrow from the value of the part of
the structure designated by the result of the function.
In the main module of borrowing functions, we declare an
additional function doing this reconstruction. It takes the same
parameters as the regular function plus the value of the result at the end
of the borrow.

For example, let us consider a function borrowing an element of an array of
access types:

.. code-block:: ada

   type Int_Acc is access Integer;
   type Int_Acc_Arr is array (Positive range <>) of Int_Acc;
   type Int_Acc_Arr_Acc is access Int_Acc_Arr;

   function F (X : Int_Acc_Arr_Acc; I : Integer) return access Integer;

We generate for it a function which returns the reconstructed
borrowed parameter from the value of the structure designated by the result
of the function at the end of the borrow:

.. code-block:: whyml

   val function f__borrowed_at_end
      (x: int_acc_arr_acc) (i: int) (f__result_at_end: t8b) : int_acc_arr_acc


Just like for usual functions, we don't assume much about what it
actually returns unless the traversal function is an expression function.
Here is the axiom generated for the function ``F`` above:

.. code-block:: whyml

   axiom f__post_axiom:
      forall x : int_acc_arr_acc.
      forall i : int [ f x i].
         dynamic_invariant x /\ dynamic_invariant i ->
         let result = f x i in
         (forall f__result_at_end : t8b [ f__borrowed_at_end x i f__result_at_end].
            f__result_at_end.is_null_pointer = result.is_null_pointer ->
            let borrowed_at_end = f__borrowed_at_end x i f__result_at_end in
               borrowed_at_end.is_null_pointer = x.is_null_pointer) /\
          f__borrowed_at_end x i result = x

It is made of two conjuncts. The first one describes what is known about the
reconstructed borrowed parameter depending on the new value of the result
``f_result_at_end``. Here since we have no postcondition and ``F`` is not an
expression function, it is only that its ``is_null`` field cannot be
modified. The second conjunct states that, if the result is unchanged, so is
the borrowed parameter. If ``F`` has a postcondition, generated or user-defined,
then it is translated inside the first conjunction, so that, if a user wants to
give additional information about the value of the borrowed parameter at the
end of the borrow using a call to a function annotated with ``At_End_Borrow``,
we have a name for it.

Subprogram Signature
^^^^^^^^^^^^^^^^^^^^

Parameters and Return Type
""""""""""""""""""""""""""

When an Ada subprogram is converted into Why, its parameters are
translated into parameters of the associated Why logic or program
function. The translation of a subprogram parameter depend both on the
mode and on the type of the parameter (see
Gnat2why.Subprograms.Compute_Raw_Binders). More precisely, in
parameters will be translated as constants, and thus, if they are of a
composite type, be presented in closed form, whereas in out and out
parameters will be translated as variables, and are therefore given in
split form.

As an example, let us consider the following Ada subprograms:

.. code-block:: ada

   function F (X : Integer; Y : My_Rec; Z : My_Array) return Integer;
   procedure P
        (X : in out Integer; Y : in out My_Rec; Z : in out My_Array);

Parameters F and P have the same type, but not the same mode, which
will result in different translations in Why:

.. code-block:: whyml

     function f (x : int) (y : my_rec) (z : my_array) : int

     val f (x : int) (y : my_rec) (z : my_array) : int
      requires { true }
      ensures { ... }

     val p (x : int__ref)
	   (y__split_fields : P__my_rec.__split_fields__ref)
	   (y__split_discrs : P__my_rec.__split_discrs__ref)
	   (y__attr__constrained : bool)
	   (z : Array__Int__Standard__natural.map__ref)
	   (z__first : integer)
	   (z__last : integer) : unit
      requires { true }
      ensures { ... }
      writes {x, y__split_fields, y__split_discrs, z}

We can see that the parameters of F are given as a whole whereas the
parameters of P that are of a composite type are splitted in different
parts. Another difference between the two declarations, is of course
that parameters of P that are mutable are given through a reference
type, so that their value can be modified. Note that only mutable
parts of mutable parameters are of a reference type. For Y, both the
fields and discriminants are mutable because My_Rec has mutable
discriminants, but the Constrained attribute is not. As for Z, the
content of the array is mutable whereas the bounds are constant.

NB: In the frontend, a specific (constrained) subtype is introduced
for parameters of an unconstrained record or array type (see
``Einfo.Actual_Subtype``). For subprogram declarations, we do not use this
subtype but rather the nominal unconstrained type for the parameters
to be able to call the function on any object of the type.

Self Reference of Protected Objects
"""""""""""""""""""""""""""""""""""

One special case worth noting: for subprograms located inside a
protected type (see Sem_Util.Within_Protected_Type), an additional
parameter named Self is added to the list of parameters to handle
direct references to protected components (see call to
``Why.Gen.Binders.Concurrent_Self_Binder`` in
``Gnat2why.Subprograms.Compute_Raw_Binders``).

Global Variables
""""""""""""""""

In Ada, functions and procedures are allowed to access (and for
procedures to modify) global variables. In Why, only program functions
can access global variables, and so, only if they appear in an
appropriate reads (or writes if the global variables are modified)
annotation. Thus, when an Ada subprogram accessing variables is
translated in Why, its program functions are annotated with
appropriate reads and writes annotations (see
``Gnat2why.Subprograms.Compute_Effects``) whereas its logic function (if
any) will take additional parameters for each referenced variable (see
``Gnat2why.Subprograms.Add_Logic_Binders``). Note that, unlike regular
parameters, the parameters introduced for global variables will be in
split form whenever the Why declaration of the variable is in split
form, and so, even if the global mode in Input. Also, for global
variables in split form, only the variable parts are given as
parameters to the Why logic function.

As an example, let us look at the following Ada subprograms:

.. code-block:: ada

   function F return Integer with Global => (X, Y, Z);

   procedure P with Global => (In_Out => (X, Y, Z));

Here is the logic function introduced for F:

.. code-block:: whyml

     function f (x : int)
		(y__fields : P__my_rec.__split_fields)
		(y__discrs : P__my_rec.__split_discrs)
		(z : Array__Int__Standard__natural.map) : int


Here, although the global mode of X, Y, and Z in the contract of F is
Input, we can see that parameters for Y and Z are given in split form.
No parameter is supplied for the Constrained attribute of Y, nor for
the bounds of Z since they are translated as global constants.

As an example of effects of program function, we consider the translation of P:

.. code-block:: whyml

     val p (__void_param : unit) : unit
      requires { true }
      ensures { ... }
      reads {x, y__split_fields, y__split_discrs, z}
      writes {x, y__split_fields, y__split_discrs, z}

We can see that p has no parameter. Instead, global variables read and
written by the subprogram are described in the reads and writes
annotations. Note that global constants are not referenced here.

Volatile Functions
""""""""""""""""""

Volatile functions are functions which may read from a volatile
variable. As a result, they may have effects which should be modeled
in Why. First, since volatile functions cannot be called in
assertions, they have no associated logic functions. Then, to model
effects of volatile functions, a new global variable is introduced and
added as a write effect of the subprogram.

As an example, let us consider the following volatile function:

.. code-block:: ada

   function F_Vol return Integer with Volatile_Function;

Here is the program function introduced for it:

.. code-block:: whyml

 val volatile__effect : Main.__private__ref

 val f_vol (__void_param : unit) : int
  requires { true }
  ensures { Standard__integer___axiom.dynamic_invariant result
                True False True }
  writes {volatile__effect}

Note that functions declared inside protected objects, though
theoretically volatile, are not handled with this mechanism. Instead,
the additional self parameter works as the mutable reference.

Contracts
^^^^^^^^^

Contracts or definitions of generated Why functions can come from
several sources: typing information, Ada contracts, bodies of
expression functions... These informations are given as Why contracts
for program functions and through axioms (or possibly immediate
definition in particular cases) for logic functions. Why contracts are
always safe, as they are only assumed at call site. Conversely, axioms
can easily allow to deduce unsound hypothesis if not carefully
handled. More precisely, we do not generate axioms for Ada contracts
and type information of potentially non terminating function (see
Flow_Generated_Globals.Pase_2.Is_Potentially_Nonreturning) and of
recursive functions (see Flow_Generated_Globals.Pase_2.Is_Recursive).
Indeed, these contracts could be unsound in cases where the function
does not return, and could be used to prove themselves in recursive
functions. For definition of expression functions, we are less
restrictive. Indeed, an axiom of the form f x ... = expr cannot be
unsound unless expr depends (directly or through other axioms) on f x.
To prevent this case, it is enough to avoid generating axioms for
expression function bodies of functions which are both potentially
non-terminating and recursive.

Implicit Contracts
""""""""""""""""""

It is often the case that a only part of the Ada typing information is
available in the Why types of the subprogram (both parameter types and
result type). For example, the result type of both Why functions f is
int, that is, mathematical integers, although the result type of the
Ada function F is Integer. Additional information for types are added
in a dynamic way, by enriching the postcondition for the result type
or for parameters which are references, and by constraining the
precondition for in parameter types (see
``Gnat2why.Subprograms.Compute_Guard_Formula``). Note that the
precondition needs only to be strengthened for the logic function. For
the program functions, the translation mechanism is enough to ensure
that it will always be called on adequate arguments.

As an example, we can see that the postcondition of the program
function f includes the dynamic invariant of its result, but that its
precondition is still true:

.. code-block:: whyml

     val f (x : int) (y : my_rec) (z : my_array) : int
      requires { true }
      ensures { result = P__f___logic_fun.f x y z
	     /\ P__f___logic_fun.f__function_guard result x y z
	     /\ Standard__integer___axiom.dynamic_invariant result
		     True False True }

As for the post axiom of f, it uses the dynamic invariants of
parameters as a guard to prevent solvers from deducing anything from
applications of F to out of type parameters:

.. code-block:: whyml

     axiom f__post_axiom :
      (forall x : int.
      (forall y : my_rec.
      (forall z : my_array.
	 Standard__integer___axiom.dynamic_invariant x True True True
      /\ P__my_rec___axiom.dynamic_invariant y True True True
      /\ P__my_array___axiom.dynamic_invariant z True True True
      ->
	 let result = P__f.f x y z in
	 if P__f.f__function_guard result x y z then
	 Standard__integer___axiom.dynamic_invariant result
	      True False True)))

In a similar way, the postcondition of P is enriched with the dynamic
invariant of its mutable parameters (see
``Gnat2why.Subprograms.Compute_Dynamic_Property_For_Effects``):

.. code-block:: whyml

     val p   (x : int__ref)
	     (y__split_fields : P__my_rec.__split_fields__ref)
	     (y__split_discrs : P__my_rec.__split_discrs__ref)
	     (y__attr__constrained : bool)
	     (z : Array__Int__Standard__natural.map__ref)
	     (z__first : Standard__integer.integer)
	     (z__last : Standard__integer.integer) : unit
      requires { true }
      ensures
	{ Standard__integer___axiom.dynamic_invariant x.int__content
	      True True True)
       /\ P__my_rec___axiom.dynamic_invariant
	   {__split_fields = y__split_fields.__split_fields__content;
	    __split_discrs = y__split_discrs.__split_discrs__content;
	    attr__constrained = y__attr__constrained } True True True }
      writes {x, y__split_fields, y__split_discrs, z}

Note that no additional information is required for Z, as the bounds
cannot be modified by the subprogram.

Unlike type predicates, type invariants applying to a type T are not
part of its dynamic invariant during analysis of T’s enclosing unit.
Indeed, type invariants may be broken for objects inside local
subprograms or during internal subprogram calls. However, for boundary
and external subprograms, the type invariant should be added to the
postcondition for outputs of type T and to the precondition for inputs
of type T (see
``Gnat2why.Subprograms.Compute_Type_Invariants_For_Subprogram``). This is
what is done for the Why logic function generated for the subprogram
in its post axiom.

As an example, let us consider the following function F_Inv, where
type T has a type invariant, and F_Inv is boundary for T:

.. code-block:: ada

    package P is
       type T is private;
       function F_Inv (X : T) return T;
    private
       type T is record
	  F : Integer;
       end record with Type_Invariant => F in Natural;
    end P;

Here is the logic function generated for it along with its post axiom,
during the analysis of P:

.. code-block:: whyml

     function f_inv (x : t) : t

     axiom f_inv__post_axiom :
      (forall x : t.
	 (P__t___axiom.dynamic_invariant x True True True
       /\ P__t___axiom.type_invariant x) ->
	let result = f_inv x in
	if f_inv__function_guard result x then
	  P__t___axiom.dynamic_invariant result True False True
       /\ P__t___axiom.type_invariant result)

We see that the type invariant of X is used as a guard, ensuring that
the axiom will only be used on parameters which comply with the
invariant. The type invariant is also assumed to hold for the result
of f_inv.

As we need to differentiate between precondition checks and type
invariant checks, type invariant checks cannot be added directly to
the precondition of the Why program functions. Instead, another
program function named f_inv__check_invariants_on_call is created in
the module with the same parameters as f_inv and the type invariants
as a precondition. This program function is called when necessary (see
``Spark_Util.Subprograms.Subp_Needs_Invariant_Checks``) when translating
procedure or function calls (see ``Transform_Function_Call`` and
``Transform_Statement_Or Declaration`` from ``Gnat2why.Expr``). Here is the
program function introduced for F_Inv, along with the function used
for the type invariant checks:

.. code-block:: whyml

     val f_inv (x : t) : t
      requires { true }
      ensures { result = P__f_inv.f_inv x
	     /\ P__f_inv.f_inv__function_guard result x
	     /\ P__t___axiom.dynamic_invariant result True False True
	     /\ P__t___axiom.type_invariant result }

     val f_inv__check_invariants_on_call (x : t) : unit
      requires { P__t___axiom.type_invariant x }
      ensures { P__t___axiom.type_invariant x }

Note that the program function f_inv__check_invariants_on_call as the
invariant of X both as a pre and as a postcondition. This is used to
ensure that, once a check has been emitted for the type invariant of
X, it is assumed to hold for the rest of the program.

NB: Non-local invariants are not introduced specifically in
requirements and assumptions of subprograms, but rather included
inside dynamic invariants, as type invariants should always hold
outside of the invariant enclosing package. There is an exception to
this rule for parameters and result of private subprograms of the
enclosing package. These subprograms cannot be called directly (as
they are private) but can still appear in completions of public
entities (expression functions body for example). To avoid introducing
unsound axioms, care should be taken to not assume the type invariants
in this case (see
``Gnat2why.Subprograms.Include_Non_Local_Type_Inv_For_Subp``).

Ada Contracts
"""""""""""""

When supplied, Ada contracts are translated into Why logical
expressions and added to the contracts of the Why program function and
to the post axiom of the logic function. As an example, let us
consider the following function:

.. code-block:: ada

   function F (X : Integer) return Integer with
     Pre  => My_Pre (X),
     Post => My_Post (F'Result);

Here are its program function and its post axiom (the syntax of
function calls has been simplified to improve readability):

.. code-block:: whyml

     val f (x : int) : int
      requires { my_pre x }
      ensures { result = P__f___logic_fun.f x
	     /\ P__f___logic_fun.f__function_guard result x
	     /\ Standard__integer___axiom.dynamic_invariant result
		     True False True
	     /\ my_post result }

     axiom f_3__post_axiom :
      (forall x.
	(Standard__integer___axiom.dynamic_invariant x True True True
      /\ my_pre x) ->
	 let result = P__f.f x in
	   if P__f.f__function_guard result x then
	     my_post result
	  /\ Standard__integer___axiom.dynamic_invariant result
	       True False True)

In the postcondition of the Why program function, references to the
result of the function must use the word result. In Gnat2why, this
keyword is stored in the global variable Result_Name of Gnat2why.Expr
when generating this postcondition (a different name will be stored
when generating checks for the postcondition, see later). To simplify
the translation, the same identifier is used to generate the post
axiom. However, in this case, the result word does not have any
special meaning and it needs to be defined through a let expression.

A similar mechanism is used for the Old attribute which must be
translated using the old key word when in postconditions and as local
references when generating checks (see ``Gnat2why.Expr.Name_For_Old``).

Pre and postconditions are not the only Ada aspects which are stored
into these contracts. When a subprogram has a contract case, it is
transformed into an if expression and conjuncted to the postcondition
(see ``Gnat2why.Subprograms.Compute_Contract_Cases_Postcondition``).

As an example, lets us consider the following procedure:

.. code-block:: ada

    procedure P (X : in out Integer);
      Contract_Cases =>
        ((X in Natural) => My_Post (X'Old, X),
         others         => X = X’Old);

The contract case of P is used as a postcondition to describe the
result of its Why program function:

.. code-block:: whyml

    val p_4 (x : int__ref) : unit
     requires { true }
     ensures
	{ if old (Standard__natural.in_range x.int__content) then
	     my_post (old x.int__content) x.int__content
	  else x.int__content = (old x.int__content)
	    /\ Standard__integer___axiom.dynamic_invariant x.int__content
		   True True True True }
     writes {x}

Following the SPARK semantics, guards of contract cases must be
evaluated in the prestate. It is expressed in Why using the old
keyword. Just like the Old attribute in SPARK, it can be applied to a
whole expression. Note that, unlike in Ada, the disjointness and
completeness of the contract cases is not expressed in this
translation. Gnat2why will still verify them of course.

Another source of contracts in Ada is classwide contracts. More
precisely, when no contracts are specified for a primitive of a tagged
type, Gnat2why will use the (potentially inherited) classwide contract
instead. As an example, let us look at a primitive of a tagged Root
type:

.. code-block:: ada

     function F (X : Root) return Integer with
       Pre'Class  => X.F > 0,
       Post'Class => F'Result > 0;

As it has a classwide contract, but no specific postcondition, its
classwide pre and postconditions are used in the definition of its
program function:

.. code-block:: whyml

     val f (x :root) : int
      requires { to_rep (x.__split_fields.rec__subp__root__f) > 0 }
      ensures {result = P__f___logic_fun.f x
	   /\ P__f___logic_fun.f__function_guard result x
	   /\ Standard__integer___axiom.dynamic_invariant result
		 True False True True
	   /\ result > 0 }

Since classwide contracts are inherited, the same contracts will be
used for the overriding of F on a derived type Child of Root if no
other contract is supplied:

.. code-block:: whyml

   function F (X : Child) return Integer;

     val f__2 (x : child) : int
      requires { result = P__f__2___logic_fun.f x
	   /\ P__f__2___logic_fun.f__2__function_guard result x
	   /\ Standard__integer___axiom.dynamic_invariant result
		 True False True True
	   /\ result > 0 }

But if a specific postcondition is used, then the classwide
postcondition won’t be used anymore. Indeed, there is no point in
conjuncting it with the specific post, as in SPARK the specific
postcondition must always be stronger than the classwide one:

.. code-block:: whyml

    function F (X : Child) return Integer with
       Post => F'Result > 10;

     val f__2 (x : child) : int
      requires { result = P__f__2___logic_fun.f x
	   /\ P__f__2___logic_fun.f__2__function_guard result x
	   /\ Standard__integer___axiom.dynamic_invariant result
		 True False True True
	   /\ result > 10 }

A special case which should be considered are procedures
annotated with the No_Return aspect (see ``Einfo.No_Return``). A function
with this aspect will never return, so its postcondition will never be
exercised. To express it, the postcondition of the associated program
function is set to false. As an example, the following procedure:

.. code-block:: ada

   procedure P (X : in out Integer) with
     No_Return;

is translated as:

.. code-block:: whyml

     val p (x : int__ref) : unit
      requires { true }
      ensures { false }
      writes {x}

Another special case to consider are procedures annotated with
``Might_Not_Return``, whose postcondition is verified only in the cases where
the procedure returns. As an example, the following procedure:

.. code-block:: ada

   procedure P (X : in out Integer) with
     Annotate => (GNATprove, Might_Not_Return),
     Post => Whatever (X);

is translated as:

.. code-block:: whyml

     val p (x : int__ref) : unit
      requires { true }
      ensures { if Main.no__return = false then whatever (x) }
      writes {x, Main.no__return}

while a call to ``P`` is translated as:

.. code-block:: whyml

     p x;
     assume (Main.no__return = False);

Expression Functions
""""""""""""""""""""

Inlining
""""""""

Alternative Views of Subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Refined View
Dispatching View
Error Signaling View

Higher Order Specializations
""""""""""""""""""""""""""""

Functions and lemma procedures with parameters of an anonymous
access-to-function type can be annotated with ``Higher_Order_Specialization``.
They can be called on references to the ``Access`` attribute of functions which
might have a precondition or a non-null global contract. This usage cannot be
handled using the normal translation of access-to-subprogram types, as the
generated ``__call`` function would not have the appropriate parameters.
Instead, alternative `specialized` versions of the functions annotated with
``Higher_Order_Specialization`` are generated these calls.
A specialized version of a subprogram is identified by the
name of the subprogram plus a sequence of specializations for its parameters
(see ``Get_Specialization_Theory_Name``).  For each such specialized version
of a subprogram, we generate specific function declarations in Why3.
These generation is done using the same mechanism as the normal translation of
a subprogram, but the specialized parameters are handled specifically and their
global inputs are considered additional reads of the specialization (see
``Create_Theory_For_HO_Specialization_If_Needed``). As an example, consider
the Ada function ``My_Call`` defined below. It simply calls its function
parameter and returns the result:

.. code-block:: ada

   function My_Call
     (F : not null access function return Integer) return Integer
   with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Always_Return),
     Post => My_Call'Result = F.all;

The normal translation of ``My_Call`` uses the ``__call`` function of
``Profile__Return__Standard__integer`` which takes a function pointer
and returns an integer standing for the result of the call to the pointer
dereference:

.. code-block:: whyml

  val function my_call (param__f: Subprogram_Pointer_Rep.__rep) : int

  val my_call (param__f: Subprogram_Pointer_Rep.__rep) : int
    ensures { result = my_call param__f /\
              result =
	         Profile__Return__Standard__integer.__call
                    param__f.__pointer_value () }

  axiom my_call__post_axiom:
    forall param__f : Subprogram_Pointer_Rep.__rep [my_call param__f].
       not param__f.__is_null_pointer ->
          let result = my_call param__f in
            result =
	       Profile__Return__Standard__integer.__call
	          param__f.__pointer_value ()

Let us now consider the function ``Read_V`` which accesses the value of the
global variable ``V``. A call to this function cannot be represented as a
call to the ``__call`` function of ``Profile__Return__Standard__integer``, as
it should take ``V`` as an additional read effect (or an additional input
parameter for the logic function).

.. code-block:: ada

   V : Integer := 0;
   function Read_V return Integer is (V);

   I : Integer := My_Call (Read_V'Access);

Instead, we generate alternative declarations for ``My_Call`` in specialization
modules called ``Higher_order_spec__Main__call__Main__read_v`` and
``Higher_order_spec__Main__call__Main__read_v___axiom``. They call ``Read_V``
directly and have ``V`` as an additional input parameter:

.. code-block:: whyml

  val function my_call (f__void_param: unit) (v: int) : int

  val my_call (f__void_param: unit) : int
    reads   { Main.v }
    ensures { result = my_call f__void_param Main.v.int__content /\
              result = read_v Main.v.int__content }

  axiom call__post_axiom:
    forall f__void_param : unit.
    forall v : int [my_call f__void_param v].
       let result = call f__void_param v in
         result = read_v v

This specialized translation of contracts is implemented using a global map
``Specialized_Call_Params`` which maps formal parameters of specialized calls
to their actuals. This mapping is used to query the called entity when
translating subprogram calls (see ``Get_Called_Entity_For_Proof``). Note that
the specialized parameters are replaced by dummy parameters of type unit and
not simply erased. When translating specialized calls, these parameters might
contain checks in the program domain. This occurs when the ``Access`` attribute
is used on a type with a precondition, as checks are needed to ensure that the
precondition holds at the point of call (see ``Compute_Call_Args``).

Modules for Checks
==================

Declare program ‘let’ functions for which Why3 will generate
verification conditions. They are not meant to execute as the Ada
program but rather to encode all the runtime checks and assertions of
the Ada program.

All start with “assumptions”: Initial_Condition, value of constants, bounds of
inputs.

For Types
---------

For Subprograms
---------------

For Packages
------------

For Concurrent Types
--------------------

Translation of Statements and Expressions
=========================================

Translation is parametrized by a ‘domain’ value (program, term,
predicate, or program term (program but no checks are needed)) which
adapts the generated code to Why3 context where it is used. Checks are
only emitted in the ‘program’ domain. As a result, logic code
(assertions for example) are translated twice, once in the program
domain to generate the checks and one in the term or predicate domain
to have the actual translation.

Statements and Declarations
---------------------------

Declarations
^^^^^^^^^^^^

Why entities are not declared here (see Modules for Entities) but checks are generated for them and assumptions are added.

Assignments
^^^^^^^^^^^

Local Borrows
^^^^^^^^^^^^^

On borrows (declaration of local borrowers), the value of the borrowed
expression and the value of the borrower at the end of the borrow need to
be linked together through an assumption, so the value of the borrowed
expression can be reconstructed at the end of the borrow.
In the same way, on re-borrows (assignment at
top-level inside a local borrower), the value of the structure designated by
the borrower at the end of the borrow changes, and the old value needs to
be related to the new one through an assumption (see
``New_Update_For_Borrow_At_End``).
We try to generate these assumptions in the most precise way.
To understand how it works, let us look at some examples.

First, let us consider the simplest possible case: a borrow of a complete
object.

.. code-block:: ada

   type Int_Acc is access Integer;

   Y : Int_Acc ;
   B : access Integer := Y;

Here is the statements introduced for this declaration:

.. code-block:: whyml

   b__brower_at_end.t2b__content <-
      any (result : t2b)
         ensures { y.is_null_pointer = result.is_null_pointer } in
   assume { b__borrowed_at_end = b__brower_at_end.t2b__content };

So here we have indeed the most precise relation possible, that is, that the
borrowed object ``Y`` and the borrower ``B`` are always equal.

At the end of the scope of ``B``, or when this scope is exited prematurely
through a return or exit statement, the value of ``b__brower_at_end``
is set to ``B`` through an assumption and the borrowed object
``Y`` is reconstructed from ``b__borrowed_at_end``:

.. code-block:: whyml

  assume { b__brower_at_end.t2b__content = b }
  y__pointer_value.integer__content <- b__borrowed_at_end.pointer_value;

Let us now consider a case where we only borrow part of an object:

.. code-block:: ada

   type Two_Acc is record
      F, G : Int_Acc;
   end record;

   Y : Two_Acc ;
   B : access Integer := Y.F;

Here the borrowed expression is ``Y.F``, so ``b__borrowed_at_end`` stands for
the value of ``Y.F`` at the end of the borrow, and the assumption generated
to link it to the borrower is similar to the one in the previous example:

.. code-block:: whyml

   b__brower_at_end.t1b__content <-
       any (result : t1b)
         ensures { y.rec__f.is_null_pointer = result.is_null_pointer } in
   assume { b__borrowed_at_end = b__brower_at_end.t1b__content)) });

During the reconstruction, only the ``F`` component of ``Y`` is taken from
``b__borrowed_at_end``. The rest comes from the current value of ``Y``.
Indeed, only ``Y.F`` is considered to be borrowed, and it is still
possible to modify ``Y.G`` within the scope of ``B``:

.. code-block:: whyml

   assume { b__brower_at_end = b };
   y <- { y with __split_fields =
           { y.__split_fields with acc__f = b__borrowed_at_end } };

It is possible to assign at top-level inside a borrower when the assigned
expression is rooted at the borrower (it is called a reborrow). When such
an assignment occurs, the value of the borrower at end object needs to be
updated to represent the value of the substructure only. A new imprecise
value is declared for it, and the value of the old structure at the end of
the borrow is computed from it and specified through an assumption.

Let's see what happens on an example. Here we have a list ``X``
(reborrows can only happen on recursive data structures), that we borrow inside
``Y``. We then update ``Y`` so that it now points to the next element:

.. code-block:: ada

   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   X : List_Acc;
   Y : access List := X;

   if Y /= null then
      Y := Y.N;
   end if;

As for borrows, we only assume that the new value of
``y__brower_at_end`` has the same ``is_null`` field as
``Y.N``. The old value of ``y__brower_at_end`` on the other hand is
entirely determined by the previous value of ``Y`` and the new value
of ``y__brower_at_end``:

.. code-block:: whyml

   let temp___brower =
      any (result : t3b)
        ensures { y.pointer_value.__split_fields.n.is_null_pointer
                  = result.is_null_pointer } in
   assume { y__brower_at_end.t3b__content
            = { y with pointer_value =
                { y.pointer_value with __split_fields =
                  { y.pointer_value.__split_fields with n = temp___brower } } } };
   y__brower_at_end.t3b__content <- temp___brower;

The value of the sublist designated by ``Y`` before the update at the end of
the borrow is defined to be the current value of ``Y`` (that is, before the
update), but whose ``N`` component is updated by the value of the borrower at
the end of the borrow (since after the update the borrower will only hold the
``N`` component of ``Y``). This is correct because the components of ``Y``
which are not in the reborrowed part, here ``Y.V``, are frozen by the reborrow,
so they keep the value they have at the time where the pledge is computed.

When the expression used inside a borrow or a reborrow involves calls
to traversal functions, the assumption uses the additional function
symbol introduced for borrowing traversal function to reconstruct the
borrowed parameter from the value of the borrower at the end of the
borrow. Let us look at an example:

.. code-block:: ada

   function F (X : Int_Acc_Arr_Acc; I : Integer) return access Integer;

   X : Int_Acc_Arr_Acc := new Int_Acc_Arr'(1 => null, 2 => null);
   Y : access Integer := F (X, 1);

The module generated for ``F`` includes a function
``f__borrowed_at_end``. It takes the usual parameters of ``F`` plus the
value at end of the result of the call (here stored in ``Y``) and
reconstruct the value of the borrowed parameter (here ``X``) at the end
of the borrow from it:

.. code-block:: whyml

    y__brower_at_end.t7b__content <-
        any (result : t7b)
          ensures { (f x 1).is_null_pointer = result.is_null_pointer } in
    assume { dynamic_invariant y__borrowed_at_end /\
             y__borrowed_at_end
             = f__borrowed_at_end x 1 y__brower_at_end.t7b__content };

Note that in this examples, the expression which is actually borrowed by the
declaration of ``Y`` is not really the expression supplied as the initial value
of ``Y`` but ``X`` entirely, as a call to a borrowing traversal
function borrows its first parameter. As a result, at the end of the borrow,
``X`` will be updated entirely.

Traversal functions return local borrowers, so the return statement of a
traversal function really is handled like a borrow: we update the
variable introduced for the result of the call at the end of the borrow
like in the declaration of a borrower.

For example, let us consider the following definition of ``F``:

.. code-block:: ada

   function F (X : access List) return access List is
   begin
      if X /= null then
         return X.N;
      else
         return null;
      end if;
   end F;

Here is the why3 code generated for the update of the
``result_at_end`` value in the first return statement:

.. code-block:: whyml

   f__result_at_end.t6b__content <-
        any (result : t6b)
           ensures { x.pointer_value.__split_fields.n.is_null_pointer
                     = result.is_null_pointer } in
   assume { f__borrowed_at_end =
               { x with pointer_value =
                   { x.pointer_value with __split_fields =
                       { x.pointer_value.__split_fields with n =
                           f__result_at_end.t6b__content } } } };

We can see that it is different from the translation of a regular borrow of
``X.N``. Here, ``X`` is entirely frozen by the borrow,
so ``f__borrowed_at_end`` represents the entire value of ``X`` and not only
the part which is effectively returned. Indeed, we can safely assume that
the value of ``X`` at the end of the borrow will
be the current value of ``X``, updated with the value of the borrower at the end
of the borrow. There cannot be any simultaneous change in ``X.V`` for example.

In the else branch of the if statement, we return null. Initializing a local
borrower to null is in general not allowed, but there is an exception for the
return value of a traversal function. In this case we know that the borrowed
object will never be modified:

.. code-block:: whyml

   assume { f__borrowed_at_end = x }

Another particularity of borrowing traversal functions, is that the returned
expression can be rooted not at the first parameter, but at one of its borrower
(what the RM calls indirectly rooted at the first parameter):

.. code-block:: ada

   function F (X : access List) return access List is
      B1 : access List := X;
   begin
      if X /= null then
         declare
            B2 : access List := B1.N;
         begin
            return B2;
         end;
      else
         return null;
      end if;
   end F;

Here the expression returned by ``F`` in the first branch is rooted at ``B2``
which is itself a borrower of ``B1`` which borrows ``X``. So if we computed
the new assumption only from the returned statement, it would not relate the
result to the borrowed parameter ``X`` but to a local variable ``B_2``.
We need to go up the sequence of local borrowers until we reach the borrowed
parameter and generate assumptions along the way:

.. code-block:: whyml

   f__result_at_end.t6b__content <-
      any (result : t6b)
        ensures { b2.pointer_value.is_null_pointer
                  = result.is_null_pointer } in
   assume { b2__brower_at_end.t10b__content = f__result_at_end.t6b__content };
   assume { b2__borrowed_at_end = b1__brower_at_end.t9b__content };
   assume { b1__borrowed_at_end = f__borrowed_at_end };

Loops
^^^^^

Loop invariants behave differently in Ada and Why. To preserve the Ada
semantics, loops are cut in parts and reassembled to follow the Ada
semantics. Some parts of the loop are duplicated, leading to internal
duplication of checks, whose results are combined to generate a unique check
result for a given location and check kind.

The entry point for loop translation is :code:`Transform_Loop_Statement` in
:file:`gnat2why-expr-loops.adb`. Depending on the kind of loop and the presence
of a loop (in)variant, among other criteria, the loop may be unrolled, in which
case its body is simply repeated up to 20 times (the current internal limit for
unrolling) in Why3. If the loop is not unrolled, it is translated into a
suitable loop node in the shared AST.

The shared AST is described in :file:`why-sinfo.ads` (and in
:file:`gnat_ast.ml` for the OCaml side). The loop node variant :code:`Loop`
differs from the Why3 loop in that:

- its invariant and variants are located inside the loop (like in SPARK) with
  preceding and following statements;

- it has no condition (an infinite loop similar to the plain :code:`loop` in
  SPARK).

Thus, the translation of a loop in SPARK is done in two steps, from a SPARK
loop to a loop in the shared AST, and from this representation to a Why3
loop. Function :code:`Wrap_Loop` does the bulk of the translation from SPARK to
the shared AST, by taking in argument the pieces that correspond to an
equivalent :code:`while` loop in SPARK. Its caller
:code:`Transform_Loop_Statement` takes care of computing these pieces for each
of the different kinds of loops. In particular, :code:`Wrap_Loop` does the
following:

- it wraps the loop in a conditional, in order to test whether the loop
  condition holds before executing the loop. This is because the loop invariant
  in SPARK needs not hold if the loop is not entered, while Why3 uses the
  traditional Hoare loop invariant which should hold when reaching the loop.

- it wraps the loop in a try-catch block, in order to translate loop exit
  statements as raising and catching an exception in Why3.

- it adds checks for RTE in invariants and variants.

- it extracts exit paths, that is, sequences of statements leading to a return
  or exit statement, so that they can be hoisted outside of the Why3 loop. This
  allows to get more precise computed frame conditions for the loop in Why3,
  which do not contain variables only modified on the exit paths. This
  extraction uses a nested try-catch block.

The translation from the shared AST to Why3 occurs as part of the general
translation from one representation to the other in :code:`mk_of_expr` in
:file:`gnat_ast_to_ptree.ml`. In particular, it does the following:

- it extracts the part of the loop before the loop (in)variants and repeats it
  before the loop proper, whose body executes the part of the loop after and
  then before the loop (in)variants.

- it expands the loop variant checking as a suitable assertion of the correct
  kind.

In order for the above reordering of statements to work, while the loop
(in)variants in SPARK may be located in more nested declare blocks, all declare
blocks are first `flattened` to obtain a flat list of instructions
(declarations and statements) that form the body of the loop. Block statements
are nonetheless preserved in this flattening, as markers of the end of block,
so that treatments that should occur at the end of a block can be applied. This
is the case for havocking borrowed objects and checking for memory leaks, see
:code:`Transform_Loop_Body_Statements`.

Part of the loop invariant is automatically generated in
:code:`Generate_Frame_Condition` in :file:`gnat2why-expr-loops-inv.adb`, and
added as assumption in :code:`Transform_Loop_Statement`:

- the dynamic invariant of variables modified in the loop;

- the value of constants declared before the loop (in)variant;

- the preservation of the value of record components not modified in the loop;

- the preservation up to the current iteration of the value of parts of arrays
  that have not been modified yet in the loop.


Procedure Calls
^^^^^^^^^^^^^^^
Parameter Passing
"""""""""""""""""
Computing actual parameters to be passed to a procedure call can be relatively
complex, in particular if the paremeters are mutable (`out` or `in out`).
Indeed, the callee will expect a reference, while the parameter might be
a part of a bigger object, itself stored in a reference, or a view conversion.
When computing the parameters of a call, we try, as much as possible to reuse
the reference of the actual object if it is possible (basically, if it is
a simple object, and if the types match). This is done in ``Get_Item_From_Var``
from ``Gnat2Why.Expr``. If the reference (or references if the object is split)
of the actual cannot be reused, a new one is created and is initialized to the
actual value (see ``Get_Item_From_Expr``). In this case, additional instructions
need to be inserted after the call to store the value back inside the initial
data structure. This is done in ``Compute_Store``.
If the formal and the actual have different subtypes, checks need to be
inserted either before or after the call. This is done while computing the
parameter for checks on input, and while computing the store for checks on
output.

Indices and slice bounds in mutable actuals are captured before the call.
Copy-back uses these captured values both to read enclosing objects and to
update their components (see ``Transform_Target``). This preserves the other
components of the selected object even when the call changes variables used
in its indices or slice bounds.

When several mutable actuals update parts of the same object, predicates on
enclosing objects are checked after all copy-back stores. This allows the
intermediate states of the copy-back to violate these predicates, provided the
completed update restores them. Checks on the actuals themselves remain part of
their individual copy-back operations.

Additional Checks
"""""""""""""""""
When a subprogram call is translated in the program domain, the precondition is
checked as part of calling the Why3 translation of the callee. Other checks
may need to be generated depending on the call (checks for recursive
subprogram variants or for the invariant of inputs on calls to boundary
subprograms). Those are introduced calling specific Why3 program functions.
These functions have no
effects, only a precondition which contains the check (see
``WNE_Check_Invariants_On_Call`` and ``WNE_Check_Subprogram_Variants``). For
example, let us consider the following definition of the ``Fibonacci``
function:

.. code-block:: ada

   function Fibonacci (N : Nat) return Nat is
     (if N = 0 then 0
      elsif N = 1 then 1
      else Fibonacci (N - 1) + Fibonacci (N - 2))
   with Subprogram_Variant => (Decreases => N);

The first recursive call in ``Fibonacci`` is translated as follows:

.. code-block:: whyml

  let temp_for_n_param = n - 1 in
  let temp_call_result =
        fibonacci__check_subprogram_variants
            recursive_subprograms__fibonacci__variant temp_for_n_param;
        fibonacci temp_for_n_param

Where the call to ``fibonacci__check_subprogram_variants`` is used to insert
the variant check. This function is defined in the axiom module for
``Fibonacci`` as follows:

.. code-block:: whyml

  val fibonacci__check_subprogram_variants (variant: int) (n: int) : unit
    requires { n < variant }

As we can see, in addition to the parameters of the call which are used to
compute the value
of the variant at the time of call, the function for variant checks takes as a
parameter the values of the variant at the beginning of the enclosing scope.
If the enclosing scope is a subprogram, then these values are computed and
stored at the beginning of the subprogram. In our example,
``recursive_subprograms__fibonacci__variant`` is a constant introduced at the
beginning of the program function used to check absence of runtime errors in
``Fibonacci``:

.. code-block:: whyml

     let recursive_subprograms__fibonacci__variant =
        Recursive_subprograms__fibonacci__n.n in

If the enclosing scope is a nested
package, no such copies can be introduced. For packages declared in the
initial declarations of a subprogram, the initial values of the variant can be
computed from the variant expression of the enclosing subprogram as the
variables it might contain cannot have been modified since the beginning of the
subprogram. Recursive calls in nested packages declared anywhere else in the
subprogram are not supported, and an unprovable check is generated instead.

Exceptions
^^^^^^^^^^
All Ada exceptions are translated into a single Why3 exception called
``Ada__exc`` and declared in ``Main``. This exception takes a mathematical
integer as a parameter. The module ``Standard__ada_exceptions`` introduces
a constant with a disctinct integer value per Ada exception visible form the
analyzed unit (see ``SPARK_Util.Register_Exception`` and
``Gnat2why.Decls.Translate_Exceptions``).  This constant which will be
used to raise a particular Ada exception. As opposed to defining a Why3
exception per Ada exception, this schema has the advantage of making it easy
to translate a handler or an expectional case with the ``others`` choice
(Why3 does not have an equivalent construct, so all the possible exceptions
should be listed). As an example, consider the following Ada program:

.. code-block:: ada

   E : exception;

   procedure Raise_E (B : Boolean) with
     Exceptional_Cases => (others => B);

   procedure Raise_E (B : Boolean) is
   begin
      if B then
         raise E;
      end if;
   end Raise_E;

The module ``Standard__ada_exceptions`` introduces a constant for the exception
``E``. The raise statement in ``Raise_E`` is translated of a raise of the
Why3 exception ``Ada__exc`` with the value ``main__e``. To check the exceptional
cases, the body of ``Raise_E`` is enclosed in a try block. It catches
``Ada__exc`` and checks that the specific postcondition holds before reraising
the exception.

.. code-block:: whyml

  module Standard__ada_exceptions
    val function main__e : int
      ensures { result = (1 : int) }
  end

  (* Body of Raise_E *)
  let def (_ : unit)
    raises { Ada__exc }
  =
    try
      try
        if Main__raise_e__b.b then
          raise Ada__exc Standard__ada_exceptions.main__e
        else ();
        raise Return__exc
      with Return__exc -> ()
      end;
    with Ada__exc exc ->
      assert { Main__raise_e__b.b = True };
      raise Ada__exc exc
    end

Exception handlers are translated in a similar way. Unexpected exceptions,
that is, exceptions which are neither handled in a handler nor mentioned in
the Exceptional_Cases aspect of the enclosing procedure if any, are not
translated as raises in Why3 but as ``absurd``, in order to prove that they
never occur. For example, here is how the body of ``Raise_E`` would be
translated if we removed the exceptional cases from its declaration:

.. code-block:: whyml

  (* Body of Raise_E *)
  let def (_ : unit)
  =
    try
      if Main__raise_e__b.b then
        absurd
      else ();
      raise Return__exc
    with Return__exc -> ()
    end

Calling a procedure annotated with exceptional cases can also raise an
exception. The program function generated for such procedures uses the
exceptional contracts of Why3 to specify the cases where an Ada exception
might be raised. Here is the program function generated for ``Raise_E``:

.. code-block:: whyml

  val raise_e (param__b: bool) : unit
    raises { Ada__exc exc -> param__b = True }

When such a procedure is called, the exception ``Ada__exc`` is caught. If the
Ada exception is expected, then the exception is raised again. Otherwise, an
``absurd`` is generated to make sure that the path is never reached. As an
example, consider the following procedure which calls ``Raise_E``:

.. code-block:: ada

   procedure Call_Raise_E (B : Boolean) is
   begin
      Raise_E (B);
   exception
      when E =>
         pragma Assert (B);
   end Call_Raise_E;

Here is how it is translated into WhyMl. As the exceptional contract of
``Raise_E`` does not specify which exception is raised, the use of ``absurd``
in the else branch of the conditional will result in a failed verification
condition. If post processing is required after the call to store the parameters
back in particular, the post processing will be introduced before the exception
is reraised after the call. Note that by-copy parameters are not copied back on
exceptional exits. Parameters which are neither by-copy nor by-reference are
simply havoc'ed. They should not be considered as initialized.

.. code-block:: whyml

  (* Body of Call_Raise_E *)
  let def (_ : unit)
  =
    try
      try
        try
          Main__raise_e___axiom.raise_e Main__call_raise_e__b.b
        with Ada__exc exc ->
          if exc = Standard__ada_exceptions.main__e then
            raise Ada__exc exc
          else absurd
        end
      with Ada__exc exc ->
        if exc = Standard__ada_exceptions.main__e then
          assert { Main__call_raise_e__b.b }
        else ()
      end;
      raise Return__exc
    with Return__exc -> ()
    end

This example also demonstrates the translation of exception handlers. Note that
all Ada exceptions are caught independently of the actual choices in the Ada
handler. If there are some expected Ada exceptions which should not have been
caught, they are reraised in the else branch. It is not the case in this example
as there are no other expected exceptions in ``Call_Raise_E``.

Expressions
-----------

Aggregates
^^^^^^^^^^

Array aggregates are translated in two parts. First we generate a logic
symbol for the aggregate and we give its definition in an axiom, then we
call this symbol at the place of use and add the necessary checks.
Since the values of the aggregate might depend on local symbols, we give them
as parameters to the logic function. For example, let us consider the two
aggregates below:

.. code-block:: ada

   X : Int_Array := (1 | 5 => F (0), 2 .. 4 => F (1));
   Y : Int_Array (1 .. 4) := (others => 0);

The logic function for the initial value of ``X`` takes two parameters, one
for each component value supplied in the aggregate. Its defining axiom gives
the value of the aggregate for each valid index in the array:

.. code-block:: whyml

   module Test_aggregates__x__aggregate_def
     use  Array__Int__Standard__integer

     val function test_aggregates__x__aggregate_def (v_1: int) (v_2: int) : map
   end

   module Test_aggregates__x__aggregate_def___axiom
     use  Array__Int__Standard__integer
     use  Test_aggregates__x__aggregate_def

     axiom def_axiom:
       forall v_1 v_2 : int.
         let result = test_aggregates__x__aggregate_def v_1 v_2 in
           forall i : int.
                if 2 <= i <= 4 then
		  (if dynamic_invariant v_1 then
                     to_rep (get result i) = v_1
		   else true)
                else if i = 1 \/ i = (5 : int))) then
		  (if dynamic_invariant v_2 then
                     to_rep (get result i) = v_2
		   else true)
                else true
   end

We see that each component association is protected by a guard checking that
the value supplied for the parameter is in the bounds of the type. Indeed, this
is necessary for the axiom to be sound when the parameters are of the base Why3
type (like here).

The logic function generated for the aggregate used as the initial value of
``Y`` has only one parameter. It stands for the value of the ``others`` case. As
this value is a statically known integer value of a statically constrained
subtype, its type is translated as a range type in Why and we can give its value
directly using a literal. In this case we do not need the guard as the axiom
cannot be unsound.

.. code-block:: whyml

   module Test_aggregates__y__aggregate_def
     use  Array__Int__Standard__integer

     val function test_aggregates__y__aggregate_def (v: int) : map
   end

   module Test_aggregates__y__aggregate_def___axiom
     use  Array__Int__Standard__integer
     use  Test_aggregates__y__aggregate_def

     axiom def_axiom:
       forall v : int.
         let result = test_aggregates__y__aggregate_def v in
           forall i : int.
                get result i = 0
   end

Note that when the aggregate has an ``others`` case, the supplied value is used
as a default value in Why3. In particular, we also give the definition for
indexes out of the array bound. Also note that, even if the value ``v`` is not
used in the axiom, we still give it as a parameter to the logic function. This
is probably not needed since there should be no checks necessary for static
values of statically constrained integer types.

The logic functions above are used to intialize the Why3 objects introduced
for ``X`` and ``Y`` (see ``Complete_Translation``):

.. code-block:: whyml

    (let test_aggregates__x__assume =
          test_aggregates__x__aggregate_def (f 0) (f 1) in
       x.map__content <- test_aggregates__x__assume);
    (let test_aggregates__y__assume = test_aggregates__y__aggregate_def 0 in
       y.map__content <- test_aggregates__y__assume);

Run-time checks for aggregate values are introduced automatically as the
argument of the logic function are computed in the expected domain. For example,
if ``F`` has a precondition, it will be checked as part of the computation of
the parameters of ``test_aggregates__x__aggregate_def``. In some cases,
additional checks are necessary to make sure that the aggregate is well formed.
In particular, we need to check that the aggregate subtype is compatible with
its expected type, as the bounds of the aggregate
subtype might be computed from the choices, and not from the context. These
checks are computed in ``Insert_Check_For_Choices``. For example, the type of
the aggregate below will range from ``2`` to ``15``, and so, even if ``15`` is
strictly more than ``F (10)``:

.. code-block:: ada

   subtype Small_Pos is Positive range 1 .. F (10);
   type Small_Array is array (Small_Pos range <>) of Integer;

   Z : Small_Array := (2 .. 15 => 0);

The necessary range check is emitted at the point of use as follows:

.. code-block:: whyml

    (let test_aggregates__z__assume =
         (let _f = any (result : unit)
                     requires { 2 >= Small_pos.first /\ 15  <= Small_pos.last }
                     ensures  { true } in
            _f);
	  test_aggregates__z__aggregate_def 0 in
        z.map__content <- test_aggregates__z__assume)

As opposed to component values, the choice values can in general be used
directly in the axiom, as they are necessarily static. There are two exceptions
to this rule: aggregates with a single choice and delta aggregates. For example,
the following aggregate is valid Ada, even though its single choice does not
have static bounds:

.. code-block:: ada

   W : Int_Array := (F (1) .. F (10) => 0);

Here is the logic function generated for the initial value of ``W``:

.. code-block:: whyml

   module Test_aggregates__w__aggregate_def
     use  Test_aggregates__T15b

     val function test_aggregates__w__aggregate_def (v: int) (v_first: int) (v_last: int) : t15b
   end

As the bounds of the aggregate are not static, they are given
to the logic function as additional parameters. Their value is then used in the
defining axiom to provide the bounds of the returned array. Note that here
again, to avoid soundness issues, we need to guard the assumption with the
dynamic property of the array.

.. code-block:: whyml

    module Test_aggregates__w__aggregate_def___axiom
      use  Test_aggregates__w__aggregate_def

      axiom def_axiom:
        forall v : int, v_first : int, v_last : int.
          let result = test_aggregates__w__aggregate_def v first last in
              (if dynamic_property Positive.first Positive.last v_first v_last
	       then
                 first result = v_first /\
                 last result = v_last
               else true) /\
               (forall i : int. get (to_array result) i = 0)
    end

We see on this example, that the choice of an aggregate association is not
translated in the axiom if it might not be static. This amounts to translating
single choices as if the ``others`` keyword was used.
Checks for dynamic bounds are introduced while translating the
constants created by the frontend for them.

For delta aggregates, the expressions used inside choices (index values, bounds
of ranges ...) are given as additional parameters to the logic function.
Checks for them are introduced as part of the computation of the parameters at
the point of call. For example, let's consider the following aggregate:

.. code-block:: ada

   V : Int_Array := (X with delta 2 .. 4 => 2, F (3) => 3);

Its logic function has a parameter for the expression of the aggregate, here
``X``, for its component values ``2`` and ``3`` and for values occurring in
its choices, here ``2``, ``4``, and ``F (3)``. We do not need parameters for the
bounds as they are retrieved from the parameter for ``X``:

.. code-block:: whyml

   module Test_aggregates__v__aggregate_def
     use  Test_aggregates__int_array

     val function test_aggregates__v__aggregate_def (arr: int_array)
       (v_1: int) (v_2: int) (v_3: int) (v_4: int) (v_5: int) : int_array
   end

   module Test_aggregates__v__aggregate_def___axiom
     use  Test_aggregates__v__aggregate_def

     axiom def_axiom:
       forall arr : int_array.
       forall v_1 v_2 v_3 v_4 v_5 : int.
         let result =
	    test_aggregates__v__aggregate_def arr v_1 v_2 v_3 v_4 v_5 in
               first result = first arr /\
               last result = last arr /\
               (forall i : int.
                   if i = v_4 then
                      get (to_array result) i = 3
                   else if v_2 <= i <= v_3 then
                      get (to_array result) i = 2
                   else
                      get (to_array result) i = get (to_array arr) i)
   end

As we are in a delta aggregate, the defining axiom uses components from the
parameter for ``X`` as the default choice in the aggregate.
Note that the component associations are translated
in reverse order with respect to the Ada code. It does not change anything for
regular aggregates as choices must be distinct. However, delta aggregates allow
dynamic choices which might overlap. In this case, the last value given for
an index is the right one. For example, in the aggregate above, if ``F (3)``
happens to be in the range ``2 .. 4`` then we want its value to be set to ``3``
not ``2``.

Component expressions occuring inside iterated component associations are
handled specifically. Indeed, as they might refer to the index parameter,
they cannot be given as parameters to the function call. So we need to
give their values inside the defining axiom of the logic function. To be able to
do that, we abstract away global input (both variable and constant) and
contextual parts (see ``Collect_Contextual_Nodes`` in ``Gnat2why.Util``) and
give them as parameters to the logic function. For example, let us consider
the aggregate used in the following declaration:

.. code-block:: ada

   U : Int_Array (1 .. 6) :=
     (declare
      C : constant Integer := F (1);
      begin
        (for I in 1 | 5  => V (I),
         for I in 2 .. 4 => I + C,
         for I in others => I));

It references the global variable ``V`` and it mentions the
local constant ``C`` which depends on the context. Both need to be given as
parameters to the logic function generated for the aggregate.

.. code-block:: whyml

    module Temp_____aggregate_def_264
      use  Array__Int__Standard__integer

      val function temp_____aggregate_def_264
          (v : map) (v__first: integer) (v__last: integer) (c: int) : map
    end

    module Temp_____aggregate_def_264___axiom
      use  Temp_____aggregate_def_264

      axiom def_axiom:
        forall v : map.
        forall v__first v__last : integer.
        forall c : int.
          let result = temp_____aggregate_def_264 v v__first v__last c in
            forall i : int.
               if 2 <= i <= 4 then
                 let value = i + c in
                    (if dynamic_invariant value then
                       to_rep (get result i) = value
                     else true)
               else if i = 1 \/ i = 5 then
                 let value = to_rep (get v i) in
                    (if dynamic_invariant value then
                       to_rep (get result i) = value
                     else true)
              else
                 let value = i in
                    (if dynamic_invariant value then
                       to_rep (get result i) = value
                     else true)
    end

We see that, just like for normal aggregates, we need to use the dynamic
invariant of the component values as guards to avoid generating unsound
axioms.
At the point of use, we generate checks for absence of run-time errors
in expressions occuring inside iterated component associations as they are
not given as parameters to the call. This is done in
``Insert_Check_For_Choices``. These checks are handled like checks for
quantified expression. A local object is created for the index parameter, and
its exact value is not given, so that checks are done for any value of the
parameter which fits its constraints.

.. code-block:: whyml

     u.map__content <-
        let c = f 1 in
          (let i = any (result : int)
             ensures { result = 1 \/ result = 5 } in
             begin
               ensures { true }
               let _ = to_rep
	         (get v.map__content
	             (assert { to_rep v__first <= i <= to_rep v__last };
                      i)) in ()
             end);
          (let i = any (result : int)
             ensures { 2 <= result <= 4 } in
             begin
               ensures { true }
               let _ = range_check_ (i + c) in ()
             end);
          (let i = any (result : int)
             ensures { 1 <= result <= 6 /\
                       not (result = 1 \/ result = 5) /\
                       not (2 <= result <= 4) } in
             ());
           temp_____aggregate_def_264 v.map__content v__first v__last c;

Access Attribute on Subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If the ``'Access`` attribute of a subprogram is used somewhere in the code,
a defining module and a completion module are created for the object it
designates (see ``Declare_Theory_For_Access_If_Needed`` in
:file:`src/why/gnat2why-subprograms-pointers.adb`). Repeated occurrences for the
same subprogram reuse the same symbol.
The defining module simply declares a symbol of the built-in type
``__subprogram``. The completion module is empty for procedures. For functions,
it contains two axioms giving the precise values of the ``__call`` and
``pred_call`` functions of the profile on the symbol introduced for the access.
For example, let us consider the function ``F`` below:

.. code-block:: ada

  function F (X1 : T1; ...) return T;

If ``F'Access`` is used somewhere, we will generate the following declaration
and axioms:

.. code-block:: whyml

  val function attr__access : __subprogram

  axiom def_axiom:
    forall x1 : t1 ... .
      f x1 ... = __call attr__access x1 ...

  axiom def_axiom__function_guard:
    forall temp___result: t, x1: t1 ... .
      f__function_guard temp___result x1 ... <->
        pred_call temp___result attr__access x1 ...

These axioms let calls through ``F'Access`` use the information available about
``F``, including after conversions between access types with the same profile.
In the program domain, taking ``F'Access`` also checks that ``F`` satisfies the
contract of the access type, using the same checks as
:ref:`Access-To-Subprogram Conversions`.

SPARK also requires designated functions to terminate. Indirect calls can hide
recursion from the call graph, so taking a function's ``Access`` introduces a
termination check if the function or its callees make indirect calls. Flow
analysis relies on this check for termination of calls through access-to-function
values.

Operators
^^^^^^^^^

Quantifiers
^^^^^^^^^^^

Function Calls
^^^^^^^^^^^^^^
In the program domain, function calls are translated in a similar way as
:ref:`Procedure Calls`.

At_End_Borrow Function Calls
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
A function can be annotated with a ``pragma (Annotate, GNATprove, At_End_Borrow)``
under certain conditions (see ``Check_At_End_Borrow_Annotation``). It must be a
ghost expression function with a parameter of an
anonymous access-to-constant type. The body
of the expression function must return its parameter:

.. code-block:: ada

   function At_End_Borrow
     (B : access constant Integer) return access constant Integer
   is (B)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

This subprogram can only be called on local borrowers, the result
attribute of a borrowing traversal function (this is checked in marking),
or borrowed paths (this is checked in the borrow checker).
When such a call is encountered, it is translated as a reference to the
value of its parameter at the end of the borrow (see
``Transform_At_End_Borrow_Call``). Since this value is imprecisely known
while in the scope of the borrower, the property should hold
at any time during the borrow.

For example, let's consider a local borrower ``Y`` borrowing the component
``F`` of a variable ``X``:

.. code-block:: ada

   type Int_Acc is not null access Integer;
   type Two_Acc is record
      F, G : Int_Acc;
   end record;

   X : Two_Acc := ...;
   Y : access Integer := X.F;

The following assertion states that, at any time during the borrow, the value
designated by ``Y`` will be the value designated by ``X.F``:

.. code-block:: ada

   pragma Assert (At_End_Borrow (X.F).all = At_End_Borrow (Y).all);

In the translation to Why3, we use the objects introduced for the value at
the end of the borrow of borrowers and borrowed expressions:

.. code-block:: whyml

   assert { to_rep
               (let temp___x =
                    { x with __split_fields =
                        { x.__split_fields with f = y__borrowed_at_end } } in
                temp___x.__split_fields.f.pointer_value)
               = to_rep y__brower_at_end.t5b__content.pointer_value };

Conversions
^^^^^^^^^^^
Access-To-Subprogram Conversions
""""""""""""""""""""""""""""""""

Access-to-subprogram types can be annotated with a contract. When converting
between two access-to-subprogram types, checks are introduced in order to
ensure that the Liskov Substitution Principle is respected (see
``Gnat2why.Subprograms.Pointers.Checks_For_Subp_Conversion``). Unlike LSP
checks introduced for tagged derivation, these checks are not located in
a separate module (because they are linked to an expression, not a declaration).

Let's assume that we want to convert an expression ``Expr``
from the access-to-function type ``S`` to ``T`` below:

.. code-block:: ada

  type S is access function (X1 : S1; ...) return R with
    Pre  => S_Pre (X1, ...),
    Post => S_Post (S'Result, X1, ...);

  type T is access function (Y1 : S1; ...) return R with
    Pre  => T_Pre (Y1, ...),
    Post => T_Post (T'Result, Y1, ...);

The idea is to generate the following code:

.. code-block:: whyml

  let x1 = any s1 in
  ...
  assume { t_pre x1 ... };
  (* Check that the precondition of T is strong enough to safely call S *)
  assert { s_pre x1 ... };
  (* Set result to the result of calling Expr on X1 ... *)
  let result = __call expr x1 ... in
  assume { pred_call result expr x1 ... };
  (* Assume the post of S, this should be redundant *)
  assume { s_post result x1 ... };
  (* Check that the postcondition of T is implied by the postcondition of S *)
  assert { t_post result x1 ... }

For procedures, it is similar, except that we don't generate the let binding
for the result identifier. Since procedures can modify their parameters, we
generate a havoc statement between the checks for the precondition and the
postcondition to simulate the execution of ``Expr``.

In all cases, these checks are conditioned to the fact that ``Expr`` is not
``null`` and wrapped in an ignore block so as to not impact the rest of the
verification if these checks happen to fail. This is important as these
Liskov checks are really mandated by SPARK and not Ada, so they do not
correspond to a check at execution and users could choose to justify them.

***********************
gnat2why Implementation
***********************

This section should describe the design of ``gnat2why``, so that
developers can enter into the code base more easily.

Design
======

Circularity Avoidance (aka buckets)
-----------------------------------

Translation Phases
------------------

Additional Information Computation
----------------------------------

Declaration of Entities
-----------------------

Completion of Entities
----------------------

Generation of Checks
--------------------

Warnings by Proof
^^^^^^^^^^^^^^^^^

When the switch ``--proof-warnings`` is used, GNATprove attempts to issue
warnings about various suspicious conditions in the code, like unreachable
branches, using the capability of provers. To that end, it generates VCs of
special kinds denoted as ``VC_Warning_Kind``, so that proof of these VCs
triggers a warning, and absence of proof is ignored. To control the cost of
this feature, proof is attempted with only one prover (the first prover passed
currently), and with a very short timeout (1 sec currently). The control of
these conditions is done in :file:`gnat_config.ml`, see the use of
``opt_warn_prover`` and ``opt_warn_timeout``.

At the location where a warning could be issued, ``gnat2why`` generates an
assertion of the suitable kind, checking for the bad condition against which we
want to defend. For example, it's checking ``False`` for the warning on
unreachable branches. The assertion is isolated in an ignore block (see
``Warn_On_Dead_Branch`` in :file:`gnat2why-expr.adb`).

The decision to ignore unproved VCs that correspond to warnings is done in
``Emit_Proof_Result`` in :file:`gnat2why-error_messages.adb`. Otherwise, the
proper classification of this message as a warning is done in
``Error_Msg_Proof`` in :file:`gnat2why-flow_error_messages.adb`.

Handling of Imports
-------------------

Apart for specific standalone theories, the handling of inclusion of
modules is handled automatically in ``Why.Inter.Close_Theory``. This
generation of imports is done in two parts. First, the Why3 AST for the
module that is being closed is traversed and the referenced modules are
collected (see ``Why.Inter.Compute_Module_Set``) and included. This is
enough except for modules used to generate VCs. Indeed, in this case, we
also need the axioms for the used symbols which might be in different
completion or axiom modules to avoid issue with ordering of entities and
recursivity. This is done using a specific ``Module_Dependencies`` map
which stores dependencies between a "definition" module and a set of
"axiom" modules. This map is populated automatically when closing an
axiom module with a specific definined entity. Otherwise, it is updated
manually using the ``Why.Inter.Record_Extra_Dependency`` function.
When closing a module used to generate VCs, the closure of the initial
module set through the ``Module_Dependencies`` map is computed and the
modules are imported in the module being closed. At this point, it is
important to take into account the potential mutal recursivity between
entities to avoid including the axioms of entities ``A`` when verifying
entity ``B`` and the axioms of entity ``B`` when verifying entity ``A``.
To that end, a set of modules that should not be included for a given
entity is computed using ``Why.Atree.Modules.Mutually_Recursive_Modules``.
These modules are filtered when computing the closure.

Global Structures
=================

Annotate Pragmas
----------------

Component information
---------------------

Names for Entity Symbols (E_Symb, filled during declaration phase)
------------------------------------------------------------------

Mutable Global Structures
=========================

Symbol Map for Variables (Symbol_Table)
---------------------------------------

Name for Old
------------

Global Self Reference of Protected Objects
------------------------------------------

Architecture
============

Why syntax tree (why-atree)
---------------------------

Low level generation routines (why-gen)
---------------------------------------

High level entry points (gnat2why)
----------------------------------

Interface with Why3
-------------------

VC labels
^^^^^^^^^

Labels (now called attributes in Why3) are strings added to identifiers, terms,
formulas, program expressions etc. They are kept by WP generation and can be
used to give names to goals or identifiers, give a location to a term etc. Some
of them are used by transformations: for example, "stop_split" stops Why3's
split transformation (do not work for gnatwhy3).
The list of labels that are used by gnat2why can be found in vc_kinds.ads and
the exhaustive list is the following:

``GP_Sloc:<l>`` with l a location is used to define a location. It is not to be
confused with the # notation of Why3 for locations. l is of the form
file:line:column. In case of instantiated or inlined VC, the location is also
contained file:line:column:instantiated:file:line:column.

``GP_Check:<n>:<reason_name>:<l>`` with n a natural, reason_name a string that defines
the kind of a vc: ``OVERFLOW_CHECK``, ``RANGE_CHECK`` etc, and l a location
list as for ``GP_Sloc``. This label identifies as check uniquely as a location
and a reason (VC kind). The natural ``n`` is the ID of the VC, which is used to
simplify identifying a VC. For example, gnatwhy3's answer will typically contain
``{GP_ID:"1", proved:true}``, gnat2why will make the correspondence with the
real SPARK check which gives ``overflow check proved``.  The VC kind is also
used e.g. in debug mode and for coq proofs, and to create appropriate filename
for .smt2 or .v files. It is also used to recognize a goal in prove check mode.
The exhaustive list of kinds can be found in type ``VC_Kind`` in vc_kinds.ads.

``GP_Pretty_Ada:<n>``, with n an integer representation. When a VC is a
conjunction of several parts, gnat2why adds such a flag to each part, and this
information is extracted by gnatwhy3 from an unproved VC and passed back to
gnat2why. In this way, the (first) unproved part of a VC with multiple parts
can be identified. In practice this info is used to generate "cannot prove ..."
messages which provide this information to the user. If the integer is zero,
the information is absent. A positive integer corresponds to Node_Id and
usually identifies a subpart of an assertion. If it is negative, it is either
-1 or -2, and identifies the lower or upper bound, respectively, of a range or
overflow check.

``GP_Inline`` indicates that the corresponding symbol should be inlined to
  increase splitting of VCs. This attribute is generated in gnat2why.

``GP_Inlined`` indicates that this part of the VC was obtained by inlining a
symbol. This attribute is mostly generated in gnatwhy3 generally, but gnat2why
also sometimes uses it when it inlines definitions of predicates.

``keep_on_simp`` prevents Why3 from simplifying inside a term that has this
label. For example, ``a /\ "keep_on_simp" true`` cannot be simplified to
``a``. We use this label to make sure we get a result for *all* VCs given even
the most trivial ones.

``comment:<e>`` with e a string containing a carriage is used in manual proof
with Coq. It is intended to show where exactly the check was located *inside*
the generated .v files. In debug mode, this comment is ***not*** generated.

``model``: Counterexample label

``model_trace:<n>`` where n is the number representing a node of Ada
AST. Counterexample label

``model_projected``: Counterexample label

``model_vc``: Counterexample label

``model_vc_post``: Counterexample label

identifying subparts of formulas to be reported to user (“cannot prove ‘bla’”)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When a complex assertion cannot be proved, likely some parts of it actually
*have* been proved, and it is worthwhile to show the user (one of) the unproved
part(s). This is done as follows:

- gnat2why adds special markers to the subparts of the translation of an
  assertion, this is done in ``gnat2why-expr.Transform_Expr`` if the
  Transformation_Params enable this functionality. These markers contain the
  location of the subpart (using a regular ``GP_Sloc`` attribute) and the
  Node_Id of the corresponding node of the GNAT tree (using a ``GP_Pretty_Ada``
  attribute).
- gnatwhy3 attempts proof of these parts individually. It stops at the first
  unproved part, and returns the node of the ``GP_Pretty_Ada`` attribute as an
  ``extra_info`` (name of the JSON field) of the VC.
- gnat2why uses the ``extra_info`` to produce a message part of the form
  "cannot prove <subpart>".  Usually, we also want to update the sloc of the
  message to point to the subpart. This latter part is not done for types of
  checks where the part to be proved is in some other location of the code:
  precondition checks and Liskov-related checks.
