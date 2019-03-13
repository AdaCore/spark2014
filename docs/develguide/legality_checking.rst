#################
Legality Checking
#################

Legality checking is concerned with the sections labelled `Legality Rules` in
the SPARK Reference Manual. It is mostly implemented in the frontend and in the
so-called marking phase of ``gnat2why``.

When running GNATprove with switch ``--mode=check``, partial legality checking
is performed which does not require flow analysis to run. When running
GNATprove with switch ``--mode=check_all``, full legality checking is performed
which does require flow analysis to run.

**************************
Frontend in GNATprove Mode
**************************

When used as part of ``gnat2why``, the frontend operates in so-called GNATprove
mode, in which variable ``Opt.GNATprove_Mode`` is set to True. This mode is set
directly in ``Back_End.Scan_Compiler_Arguments`` inside ``gnat2why``, and it
can be set by using debug switch ``-gnatd.F`` when calling directly
``gcc``/``gnat1`` in debug/test.

Other debug flags are used in GNATprove, and get set directly in
``Back_End.Scan_Compiler_Arguments`` inside ``gnat2why`` or on the command-line
in debug/test:
 - switch ``-gnatdm`` is used to disable inlining (for ``gnatprove`` switch
   ``--no-inlining``)
 - switch ``-gnatd_f`` is used to enable information messages (for
   ``gnatprove`` switch ``--info``)

GNATprove mode should not be confused with SPARK mode. The former is activated
when the frontend is called as part of ``gnat2why``. The latter is activated
when entering a part of the code under ``SPARK_Mode => On``
aspect/pragma. Thus, both modes can be activated as part of ``gnat2why``, but
only SPARK mode is activated as part of compilation.

SPARK Mode
==========

During frontend analysis, ``Opt.SPARK_Mode`` is set to the current value of
SPARK mode, which can be ``Off`` or ``On`` inside a block of code subject to a
``SPARK_Mode`` aspect/pragma, or ``None`` otherwise. In the former case,
``Opt.SPARK_Mode_Pragma`` points to the applicable pragma (which was possibly
generated from the corresponding aspect).

When ``SPARK_Mode`` is ``On``, the frontend is set up to issue errors on
certain violations of language contraints which would lead to an exception at
runtime. Thus, the error will be raised by both GNAT during compilation and
GNATprove during analysis. Outside of SPARK code, the same constructs would
lead to warnings only as they are not violations of Ada legality rules, and
thus must be accepted by the compiler.

When ``SPARK_Mode`` is ``On``, the frontend also checks a fair number of SPARK
legality rules that restrict the use of Ada features. It checks in particular:
 - restrictions on effectively volatile objects (SPARK RM 7.1.3)
 - restrictions on tagged types derivations (SPARK RM 3.4)
 - restrictions on modes of function parameters (SPARK RM 6.1)
 - restrictions on elaboration order (SPARK RM 7.7)

Whenever ``SPARK_Mode`` is ``On`` or ``Off`` for the analysis of a
subprogram/package spec or body, the frontend attaches the applicable pragma to
the entity through field ``SPARK_Pragma`` of the entity node (see
``einfo.ads``). When the SPARK pragma is inherited from the enclosing scope,
the flag ``SPARK_Pragma_Inherited`` is additionally set to True. These are used
later during the marking phase in ``gnat2why`` to decide what code to analyze
and when to issue errors.

Further information about SPARK mode is available in a section of comment
entitled `SPARK Mode` in ``sinfo.ads``.

GNATprove Mode
==============

In GNATprove mode, the frontend does not perform expansion like it does for
compilation (so ``Opt.Expander_Active`` is False) but only a light expansion
defined in ``exp_spark.adb``.

Special sections of cross references are generated in ALI files, as described
in ``spark_xrefs.adb``. They are the basis for the computation of data
dependencies in flow analysis inside ``gnat2why``, for both subprograms not in
SPARK and SPARK subprograms without user-specified data dependencies.

Further information about GNATprove mode is available in a section of comment
entitled `GNATprove Mode` in ``sinfo.ads``.

*************************
Marking Phase in gnat2why
*************************
