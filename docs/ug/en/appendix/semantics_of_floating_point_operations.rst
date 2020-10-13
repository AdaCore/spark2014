Semantics of Floating Point Operations
======================================

SPARK assumes that floating point operations are carried out in single
precision (binary32) or double precision (binary64) as defined in the IEEE-754
standard for floating point arithmetic. You should make sure that this is the
case on your platform. For example, on x86 platforms, by default some
intermediate computations may be carried out in extended precision, leading to
unexpected results. With GNAT/GCC, you can specify the use of SSE arithmetic by
using the compilation switches ``-msse2 -mfpmath=sse`` which cause all
arithmetic to be done using the SSE instruction set which only provides 32-bit
and 64-bit IEEE types, and does not provide extended precision. SSE arithmetic
is also more efficient. Note that the ABI allows free mixing of units using the
two types of floating-point, so it is not necessary to force all units in a
program to use SSE arithmetic.

Several architectures also have fused-multiple-add (FMA) instructions, either
in the base set (PowerPC, Aarch64) or in extensions (SPARC, x86). You should
make sure that your compiler is instructed not to use such instructions, whose
effect on the program semantics cannot be taken into account by SPARK source
code analysis. On x86, such instructions are enabled in GNAT/GCC by means of an
explicit switch like ``-fma/-fma4`` or by architecture switches like
``-msse4.1`` or ``-mavx512f``, so make sure you're not using these. With
GNAT/GCC, it is recommended to use switch ``-ffp-contract=off`` to disable all
floating-point expression contractions, including FMA.

SPARK considers the floating point values which represent positive, negative
infinity or NaN as invalid. Proof obligations are generated that such values
cannot occur.

SPARK considers rounding on floating point arithmetic operations to follow
Round-Nearest-Even (RNE) mode, where a real result is rounded to the nearest
floating point value, and ties are resolved to the floating-point with a zero
in the last place. This mode of rounding (the default in GNAT) should be forced
if needed on the hardware to be able to rely on the results of GNATprove
regarding floating point arithmetic.
