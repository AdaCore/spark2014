.. index:: SPARK_Mode; usage

.. _Identifying SPARK Code:

************************
Identifying |SPARK| Code
************************

In general a program can have some parts that are in |SPARK| (and follow all
the rules in the |SPARK| Reference Manual), and some parts that are full
Ada. Pragma or aspect ``SPARK_Mode`` is used to identify which parts are
in |SPARK| (by default programs are in full Ada).

This section contains a simple description of pragma and aspect
``SPARK_Mode``. See :ref:`Pragma_SPARK_Mode` for the complete description.

Note that |GNATprove| only analyzes parts of the code that are identified as
being in |SPARK| using pragma or aspect ``SPARK_Mode``.

Mixing |SPARK| Code and Ada Code
================================

An Ada program unit or other construct is said to be "in |SPARK|"
if it complies with the restrictions required to permit formal verification
given  in the |SPARK| Reference Manual.
Conversely, an Ada program unit or other construct is "not in |SPARK|" if
it does not meet these requirements, and so is not amenable to formal
verification.

Within a single Ada unit, constructs which are "in" and "not in" |SPARK| may be
mixed at a fine level in accordance with the following two general principles:

* |SPARK| code shall only reference |SPARK| declarations, but a |SPARK|
  declaration which requires a completion may have a non-|SPARK| completion.

* |SPARK| code may enclose non-|SPARK| code.

* non-|SPARK| code may enclose |SPARK| code only at library level. A subprogram
  body which is not in |SPARK| cannot contain |SPARK| code.

More specifically, non-|SPARK| completions of |SPARK| declarations are
allowed for subprogram declarations, package declarations, task type
declarations, protected type declarations, private type declarations,
private extension declarations, and deferred constant declarations.
[Strictly speaking, the private part of a package, a task type or a
protected type is considered to be part of its completion for purposes
of the above rules; this is described in more detail below].

When a non-|SPARK| completion is provided for a |SPARK| declaration, the
user has an obligation to ensure that the non-|SPARK| completion is
consistent (with respect to the semantics of |SPARK|) with its |SPARK|
declaration. For example, |SPARK| requires that a function call has no
side effects. If the body of a given function is in |SPARK|, then this
rule is enforced via various language rules; otherwise, it is the
responsibility of the user to ensure that the function body does not
violate this rule. As with other such constructs (notably pragma
Assume), failure to meet this obligation can invalidate any or all
analysis (proofs and/or flow analysis) associated with the |SPARK|
portion of a program. A non-|SPARK| completion meets this obligation if
it is semantically equivalent (with respect to dynamic semantics) to
some notional completion that could have been written in |SPARK|.

When a non-|SPARK| package declaration or body is included in a |SPARK|
subprogram or package, the user has an obligation to ensure that the
non-|SPARK| declaration is consistent (with respect to the semantics of
|SPARK|) with a hypothetical equivalent |SPARK| declaration. For example,
|SPARK| requires that package elaboration code cannot modify variables defined
outside of the package.

The |SPARK| semantics (specifically including flow analysis and
proof) of a "mixed" program which meets the aforementioned
requirement are well defined - they are the semantics of the
equivalent 100% |SPARK| program. For the semantics of other "mixed"
programs refer to the Ada Reference Manual.

In the case of a package, a task type, or a protected type, the
specification/completion division described above is a simplification
of the true situation. For instance, a package is divided into 4
sections, not just 2: its visible part, its private part, the
declarations of its body, and the statement list of its body. For a
given package and any number N in the range 0 .. 4, the first N
sections of the package might be in |SPARK| while the remainder is
not.

For example, the following combinations may be typical:

- Package specification in |SPARK|. Package body not in |SPARK|.

- Visible part of package specification in |SPARK|. Private part and body not
  in |SPARK|.

- Package specification in |SPARK|. Package body almost entirely in |SPARK|,
  with a small number of subprogram bodies not in |SPARK|.

- Package specification in |SPARK|, with all subprogram bodies imported
  from another language.

- Package specification contains a mixture of declarations which are in |SPARK|
  and not in |SPARK|.  The latter declarations are only visible and usable from
  client units which are not in |SPARK|.

Task types and protected types are similar to packages but only have 3
sections instead of 4. The statement list section of the body is
missing.

Another typical use is to exempt part of a subprogram from analysis by
isolating it in a local subprogram whose body is not in |SPARK|.

Such patterns are intended to allow for application of formal verification to a
subset of a program, and the combination of formal verification with more
traditional testing (see :ref:`Applying SPARK in Practice`).

.. index:: project file; and SPARK_Mode

Project File Setup
==================

The project file is used to identify coarsely which parts of a program are in
|SPARK|. To get more details on project file setup, see section :ref:`Setting
Up a Project File`.

.. _Setting the Default SPARK_Mode:

Setting the Default SPARK_Mode
------------------------------

There are two possible defaults:

#. No value of ``SPARK_Mode`` is specified as a configuration pragma. In that
   case, only the parts of the program explicitly marked with ``SPARK_Mode =>
   On`` are in |SPARK|. This default is recommended if only a small number of
   units or subprograms are in |SPARK|.

#. A value of ``SPARK_Mode => On`` is specified as a configuration pragma. In
   that case, all the program should be in |SPARK|, except for those parts
   explicitly marked with ``SPARK_Mode => Off``. This mode is recommended if
   most of the program is in |SPARK|.

Here is how to specify a value of ``SPARK_Mode => On`` as a configuration
pragma:

.. code-block:: gpr

  project My_Project is
     package Builder is
        for Global_Configuration_Pragmas use "spark.adc";
     end Builder;
  end My_Project;

where ``spark.adc`` is a configuration file containing at least the following
line:

.. code-block:: ada

  pragma SPARK_Mode (On);

.. _Specifying Files To Analyze:

Specifying Files To Analyze
---------------------------

By default, all files from a project are analyzed by |GNATprove|. It may be
useful to restrict the set of files to analyze to speedup analysis if only a
subset of the files contain |SPARK| code.

The set of files to analyze can be identified by specifying a different value
of various project attributes in the mode used for formal verification:

 * ``Source_Dirs``: list of source directory names
 * ``Source_Files``: list of source file names
 * ``Source_List_File``: name of a file listing source file names

For example:

.. code-block:: gpr

  project My_Project is

    type Modes is ("Compile", "Analyze");
    Mode : Modes := External ("MODE", "Compile");

    case Mode is
       when "Compile" =>
          for Source_Dirs use (...);
       when "Analyze" =>
          for Source_Dirs use ("dir1", "dir2");
          for Source_Files use ("file1.ads", "file2.ads", "file1.adb", "file2.adb");
    end case;

  end My_Project;

Then, |GNATprove| should be called by specifying the value of the ``MODE``
external variable as follows::

  gnatprove -P my_project -XMODE=Analyze

.. _Excluding Files From Analysis:

Excluding Files From Analysis
-----------------------------

When choosing a default value of ``SPARK_Mode => On``, it may be needed to
exclude some files from analysis (for example, because they contain non-|SPARK|
code, or code that does not need to be formally analyzed).

The set of files to exclude can be identified by specifying a different value
of various project attributes in the mode used for formal verification:

 * ``Excluded_Source_Dirs``: list of excluded source directory names
 * ``Excluded_Source_Files``: list of excluded source file names
 * ``Excluded_Source_List_File``: name of a file listing excluded source file names

For example:

.. code-block:: gpr

  project My_Project is
     package Builder is
        for Global_Configuration_Pragmas use "spark.adc";
     end Builder;

    type Modes is ("Compile", "Analyze");
    Mode : Modes := External ("MODE", "Compile");

    case Mode is
       when "Compile" =>
          null;
       when "Analyze" =>
          for Excluded_Source_Files use ("file1.ads", "file1.adb", "file2.adb");
    end case;

  end My_Project;

Then, |GNATprove| should be called by specifying the value of the ``MODE``
external variable as follows::

  gnatprove -P my_project -XMODE=Analyze

Using Multiple Projects
-----------------------

Sometimes, it is more convenient to analyze a subset of the source files with
the default ``SPARK_Mode => On`` and the rest of the source files with no
setting for ``SPARK_Mode``. In that case, one can use two project files with
different defaults, with each source file in one of the projects only. Files in
one project can still refer to files in the other project by using a ``limited
with`` clause between projects, as follows:

.. code-block:: gpr

  limited with "project_b"
  project My_Project_A is
     package Compiler is
        for Local_Configuration_Pragmas use "spark.adc";
     end Compiler;
     for Source_Files use ("file1.ads", "file2.ads", "file1.adb", "file2.adb");
  end My_Project_A;

.. code-block:: gpr

  limited with "project_a"
  project My_Project_B is
     for Source_Files use ("file3.ads", "file4.ads", "file3.adb", "file4.adb");
  end My_Project_B;

where ``spark.adc`` is a configuration file containing at least the following
line:

.. code-block:: ada

  pragma SPARK_Mode (On);

.. _Using SPARK_Mode in Code:

Using ``SPARK_Mode`` in Code
============================

The pragma or aspect ``SPARK_Mode`` can be used in the code to identify
precisely which parts of a program are in |SPARK|.

Basic Usage
-----------

The form of a pragma SPARK_Mode is as follows:

.. code-block:: ada

   pragma SPARK_Mode [ (On | Off) ]

For example:

.. code-block:: ada

   pragma SPARK_Mode (On);
   package P is

The form of an aspect SPARK_Mode is as follows:

.. code-block:: ada

   with SPARK_Mode => [ On | Off ]

For example:

.. code-block:: ada

   package P with
     SPARK_Mode => On
   is

A default argument of On is assumed for any SPARK_Mode pragma or
aspect for which no argument is explicitly specified.

For example:

.. code-block:: ada

   package P is
      pragma SPARK_Mode;  --  On is implicit here

or

.. code-block:: ada

   package P with
     SPARK_Mode  --  On is implicit here
   is

We say that a package or a subprogram is library-level if it is either
top-level or defined in a library-level package. The ``SPARK_Mode`` pragma can
be used in the following places in the code:

* as a configuration pragma at unit level (even before with-clauses) in
  particular for unit-level generic instantiations

* immediately within a library-level package spec

* immediately within a library-level package body

* immediately following the ``private`` keyword of a library-level package spec

* immediately following the ``begin`` keyword of a library-level package body

* immediately following a library-level subprogram spec

* immediately within a library-level subprogram body

* immediately within a library-level task spec

* immediately within a library-level task body

* immediately following the ``private`` keyword of a library-level task spec

* immediately within a library-level protected spec

* immediately within a library-level protected body

* immediately following the ``private`` keyword of a library-level
  protected spec

The ``SPARK_Mode`` aspect can be used in the following places in the code:

* on a library-level package spec or body

* on a library-level subprogram spec or body

* on a library-level task spec or body

* on a library-level protected spec or body

If a ``SPARK_Mode`` pragma or aspect is not specified for a
subprogram, package, task or protected spec/body, then its
value is inherited from the current mode that is active at the point
where the declaration occurs.

Note that a generic package instance is considered to be declared
at its instantiation point. For example, a generic package
cannot be both marked ``SPARK_Mode`` and instantiated in
a subprogram body.

Consistency Rules
-----------------

The basic rule is that you cannot turn ``SPARK_Mode`` back On, once you have
explicitly turned if Off. So the following rules apply:

If a subprogram spec has ``SPARK_Mode`` Off, then the body cannot have
``SPARK_Mode`` On.

For a package, we have four parts:

#. the package public declarations
#. the package private part
#. the body of the package
#. the elaboration code after ``begin``

For a package, the rule is that if you explicitly turn ``SPARK_Mode`` Off for
any part, then all the following parts cannot have ``SPARK_Mode`` On. Note that
this may require repeating a pragma ``SPARK_Mode (Off)`` in the body. For
example, if we have a configuration pragma ``SPARK_Mode (On)`` that turns the
mode On by default everywhere, and one particular package spec has pragma
``SPARK_Mode (Off)``, then that pragma will need to be repeated in the package
body.

Task types and protected types are handled similarly. If ``SPARK_Mode`` is set
to Off on one part, it cannot be set to On on the following parts, among the
three parts:

#. the spec
#. the private part
#. the body

There is an exception to this rule, when ``SPARK_Mode`` occurs in the code of a
generic instantiated in code where ``SPARK_Mode`` is Off. In that case,
occurrences of ``SPARK_Mode`` in the generic are ignored for this instance.

Examples of Use
---------------

.. _Verifying Selected Subprograms:

Verifying Selected Subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If only a few selected subprograms are in |SPARK|, then it makes sense to set no
default for ``SPARK_Mode``, and instead set ``SPARK_Mode => On`` directly on
the subprograms of interest. For example:

.. literalinclude:: /examples/tests/selected_subprograms/selected_subprograms.ads
   :language: ada
   :linenos:

Note that, although the bodies of procedures ``Sub_Action`` and
``Non_Critical_Action`` are not analyzed, it is valid to call ``Sub_Action`` in
the body of procedure ``Critical_Action``, even without specifying ``SPARK_Mode
=> On`` on the spec of ``Sub_Action``. Indeed, |GNATprove| checks in that case
that the spec of ``Sub_Action`` is in |SPARK|.

.. literalinclude:: /examples/tests/selected_subprograms/selected_subprograms.adb
   :language: ada
   :linenos:

.. _Verifying Selected Units:

Verifying Selected Units
^^^^^^^^^^^^^^^^^^^^^^^^

If only a few selected units are in |SPARK|, then it makes sense to set no
default for ``SPARK_Mode``, and instead set ``SPARK_Mode => On`` directly on
the units of interest. For example:

.. literalinclude:: /examples/tests/selected_units/selected_units.ads
   :language: ada
   :linenos:

Note that procedure ``Sub_Action`` can be called inside |SPARK| code, because
its spec is in |SPARK|, even though its body is marked ``SPARK_Mode =>
Off``. On the contrary, procedure ``Non_Critical_Action`` whose spec is marked
``SPARK_Mode => Off`` cannot be called inside |SPARK| code.

.. literalinclude:: /examples/tests/selected_units/selected_units.adb
   :language: ada
   :linenos:

.. _Excluding Selected Unit Bodies:

Excluding Selected Unit Bodies
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If a unit spec is in |SPARK|, but its body is not in |SPARK|, the spec can be
marked with ``SPARK_Mode => On`` and the body with ``SPARK_Mode => Off``. This
allows client code in |SPARK| to use this unit. If ``SPARK_Mode`` is On by
default, then it need not be repeated on the unit spec.

.. literalinclude:: /examples/tests/exclude_unit_body/exclude_unit_body.ads
   :language: ada
   :linenos:

Note that the private part of the spec (which is physically in the spec file,
but is logically part of the implementation) can be excluded as well, by using
a pragma ``SPARK_Mode (Off)`` at the start of the private part.

.. literalinclude:: /examples/tests/exclude_unit_body/exclude_unit_body.adb
   :language: ada
   :linenos:

This scheme also works on generic units, which can then be instantiated both in
code where ``SPARK_Mode`` is On, in which case only the body of the
instantiated generic is excluded, or in code where ``SPARK_Mode`` is Off, in
which case both the spec and the body of the instantiated generic are excluded.

.. literalinclude:: /examples/tests/use_generic/exclude_generic_unit_body.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/tests/use_generic/exclude_generic_unit_body.adb
   :language: ada
   :linenos:

.. literalinclude:: /examples/tests/use_generic/use_generic.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/tests/use_generic/use_generic.adb
   :language: ada
   :linenos:

.. _Excluding Selected Parts of a Unit:

Excluding Selected Parts of a Unit
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If most units are in |SPARK| except from some subprograms and packages, it
makes sense to set the default to ``SPARK_Mode (On)``, and set ``SPARK_Mode =>
Off`` on non-|SPARK| declarations. We assume here that a value of ``SPARK_Mode
=> On`` is specified as a configuration pragma.

.. literalinclude:: /examples/tests/exclude_selected_parts/exclude_selected_parts.ads
   :language: ada
   :linenos:

Note that procedure ``Non_Critical_Action`` can be called inside |SPARK| code,
because its spec is in |SPARK|, even though its body is marked ``SPARK_Mode =>
Off``.

Note also that the local package ``Non_Critical_Data`` can contain any
non-|SPARK| types, variables and subprograms, as it is marked ``SPARK_Mode =>
Off``. It may be convenient to define such a local package to gather
non-|SPARK| declarations, which allows to mark globally the unit
``Exclude_Selected_Parts`` with ``SPARK_Mode => On``.

.. literalinclude:: /examples/tests/exclude_selected_parts/exclude_selected_parts.adb
   :language: ada
   :linenos:
