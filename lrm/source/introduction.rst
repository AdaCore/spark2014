Introduction
============

|SPARK| is a major overhaul of SPARK 2005 based on Ada 2012. This
document describes the language features of |SPARK|, that either
restrict or extend those of Ada 2012.

This introduction will mention the design goals of |SPARK|.

Language Subset
---------------

|SPARK| is a subset of Ada 2012 which may be used to prove the absence
of run-time exceptions and, if suitable postconditions are provided,
program correctness .  |SPARK| introduces a number of new aspect marks
to use in aspect specifications to provide:

* more detailed and concise subprogram specifications;
* support for static analyses;
* facilities for constructive, modular proof and analysis - proof and
  static analyses may be performed on partial and incomplete programs;
  and
* higher levels of abstraction for data and modelling.

A number of selectable restrictions specific to |SPARK| have been
introduced to provide language profiles tailored to particular
domains, but the restrictions may be applied individually using the
**pragma** ``Restrictions`` or, conversely, a restriction that is in
place, possibly due to a particular profile being active, may be
overridden locally using the same pragma.

.. todo :: Should |SPARK| itself be a restriction?  It actually adds
  new features so I am not sure.  I am not entirely happy with the
  next paragraph, which is why I raise this question.  I think there
  should also be a command line switch or some way of stating that the
  whole program has to be in |SPARK| unless a deliberate escape is
  made. Alternatively, do e need the pragma/aspect |SPARK| at all.
  Could we assume that the program is |SPARK| unless we step outside
  the subset when a warning is given, and perhaps we could have a
  restriction in |SPARK| called Ada => 2012, Ada => 95, etc. which
  indicates that this part of the program is not in |SPARK| and
  therefore will not raise the warnings?

An Ada program may contain units in |SPARK| and units not in
|SPARK|. An Ada unit may contain packages and subprograms in |SPARK|
and others not in |SPARK|. The user can specify that a unit should be
in |SPARK| by using the pragma |SPARK|. Likewise, the user can specify
that a package or a subprogram should be in |SPARK| by using the
aspect |SPARK| on the entity declaration, or the pragma ``SPARK_2014``
in the body of the package or subprogram.

To perform proofs and some of the deeper static analyses of a unit the
code must be in SPARK, and depending on the type of analysis may
require some further restrictions to be applied.

.. todo:: I think we need to mention here in outline how we deal with
  the dichotomy between proven, non proven and tested and resolve
  these different parts into a coherent whole.

.. todo:: Need to describe the difference between two modes of
  working, constructive-modular and generative.
