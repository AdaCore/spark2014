Language Subset
===============

.. |SPARK| replace:: SPARK 2014

An Ada program may contain units in |SPARK| and units not in |SPARK|. An Ada
unit may contain packages and subprograms in |SPARK| and others not in
|SPARK|. The user can specify that a unit should be in |SPARK| by using the
pragma ``SPARK_2014``. Likewise, the user can specify that a package or a
subprogram should be in |SPARK| by using the aspect ``SPARK_2014`` on the
entity declaration, or the pragma ``SPARK_2014`` in the body of the package or
subprogram.

