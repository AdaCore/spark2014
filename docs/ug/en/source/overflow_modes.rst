.. _Overflow Modes:

Overflow Modes
==============

Annotations such as preconditions, postconditions, assertions, loop invariants,
are analyzed by |GNATprove| with the exact same meaning that they have during
execution. In particular, evaluating the expressions in an annotation may raise
a run-time error, in which case |GNATprove| will attempt to prove that this
error cannot occur, and report a warning otherwise.

Integer overflows are a kind of run-time error that occurs when the result of
an arithmetic computation does not fit in the bounds of the machine type used
to hold the result. In some cases, it is convenient to express properties in
annotations as they would be expressed in mathematics, where quantities are
unbounded. This is best achieved using the :ref:`Big Numbers Library`, which
defines types for unbounded integers and rational numbers, operations on these
and conversions from/to machine integers and reals.

Alternatively, |GNATprove| supports different overflow modes, so that the usual
signed arithmetic operations are interpreted differently from their standard
interpretation. For example:

.. code-block:: ada
   :linenos:

    function Add (X, Y : Integer) return Integer with
      Pre  => X + Y in Integer,
      Post => Add'Result = X + Y;

The precondition of ``Add`` states that the result of adding its two parameters
should fit in type ``Integer``. In the default mode, evaluating this expression
will fail an overflow check, because the result of ``X + Y`` is stored in a
temporary of type ``Integer``. If the compilation switch ``-gnato13`` is used,
then annotations are compiled specially, so that arithmetic operations use
unbounded intermediate results. In this mode, |GNATprove| does not generate a
check for the addition of ``X`` and ``Y`` in the precondition of ``Add``, as
there is no possible overflow here.

There are three overflow modes:

* Use base type for intermediate operations (STRICT): in this mode, all
  intermediate results for predefined arithmetic operators are computed using
  the base type, and the result must be in range of the base type.
* Most intermediate overflows avoided (MINIMIZED): in this mode, the compiler
  attempts to avoid intermediate overflows by using a larger integer type,
  typically Long_Long_Integer, as the type in which arithmetic is performed
  for predefined arithmetic operators.
* All intermediate overflows avoided (ELIMINATED): in this mode, the compiler
  avoids all intermediate overflows by using arbitrary precision arithmetic as
  required.

The desired mode for handling intermediate overflow can be specified using
either the Overflow_Mode pragma or an equivalent compiler switch. The pragma
has the form::

    pragma Overflow_Mode ([General =>] MODE [, [Assertions =>] MODE]);

where MODE is one of

* STRICT: intermediate overflows checked (using base type)
* MINIMIZED: minimize intermediate overflows
* ELIMINATED: eliminate intermediate overflows

For example:

.. code-block:: ada

   pragma Overflow_Mode (General => Strict, Assertions => Eliminated);

specifies that general expressions outside assertions be evaluated in the usual
strict mode, and expressions within assertions be evaluated in "eliminate
intermediate overflows" mode. Currently, |GNATprove| only supports pragma
``Overflow_Mode`` being specified as a configuration pragma, either in a
configuration pragma file or directly in a unit.

Additionally, a compiler switch ``-gnato??`` can be used to control the
checking mode default. Here `?` is one of the digits `1` through `3`:

#. use base type for intermediate operations (STRICT)
#. minimize intermediate overflows (MINIMIZED)
#. eliminate intermediate overflows (ELIMINATED)

The switch ``-gnato13``, like the ``Overflow_Mode`` pragma above, specifies that
general expressions outside assertions be evaluated in the usual strict mode,
and expressions within assertions be evaluated in "eliminate intermediate
overflows" mode.

Note that these modes apply only to the evaluation of predefined arithmetic,
membership, and comparison operators for signed integer arithmetic.

For further details of the meaning of these modes, and for further information
about the treatment of overflows for fixed-point and floating-point arithmetic
please refer to the "Overflow Check Handling in GNAT" appendix in the |GNAT Pro|
User's Guide.
