.. index:: project file; project attributes

Project Attributes
==================

|GNATprove| reads the package ``Prove`` in the given project file. This package
is allowed to contain the following attributes:

* ``Proof_Switches``, which defines additional command line switches that are used
  for the invocation of |GNATprove|. This attribute can be used in two
  different settings:

  * to define switches that should apply to all files in the project.  As an
    example, the following package in the project file sets the proof level for
    all units in the project to 2::

      package Prove is
         for Proof_Switches ("Ada") use ("--level=2");
      end Prove;

  * to define switches that should apply only to one file. The following
    example sets the timeout for provers run by |GNATprove| to 10 seconds for
    ``file.adb``::

      package Prove is
         for Proof_Switches ("file.adb") use ("--timeout=10");
      end Prove;

    Note that, if a unit has both a body and specification file, the body file
    should be used for this attribute.

  Switches given on the command line have priority over switches given in the
  project file, and file-specific switches have priority over switches that
  apply to all files. A special case is the ``--level`` switch: the values for
  ``--timeout`` etc implied by the ``--level`` switch are always overridden by
  more specific switches, regardless of where they appear. For example,
  the timeout for the analysis of ``file.adb`` is set to 10 seconds below,
  despite the ``--level=0`` switch (which implies a lower timeout) specified
  for this file::

    package Prove is
       for Proof_Switches ("Ada") use ("--timeout=10");
       for Proof_Switches ("file.adb") use ("--level=0");
    end Prove;

  The following switches cannot be used inside project files at all: ``-P``,
  ``-aP``, ``--subdirs``, ``--clean``, ``--list-categories``, ``--version``,
  ``-X``, ``-v``, ``-q``, ``--explain``, ``--help``, ``--print-gpr-registry``.

  In the Proof_Switches attribute for specific files, and in the Proof_Switches
  attribute of project files other than the one that was passed to |GNATprove|
  on the command-line, only the following switches are allowed for file-specific
  switches:
  ``--steps``, ``--timeout``, ``--memlimit``, ``--proof``, ``--prover``,
  ``--level``, ``--mode``, ``--counterexamples``, ``--no-inlining``,
  ``--no-loop-unrolling``, ``--proof-warnings``, ``--pedantic``, ``--info``,
  ``-W``, ``-A``, ``-D``.

  The remaining switches can be used only in the ``Proof_Switches ("Ada")``
  attribute of the root project.

* ``Switches``. This deprecated attribute is the same as ``Proof_Switches
  ("Ada")``.


* ``Proof_Dir``, which defines the directory where the files concerning the
  state of the proof of a project are stored. This directory contains a
  sub-directory ``sessions`` with one directory per source package analyzed for
  proof. Each of these package directories contains a Why3 session file. If a
  manual prover is used to prove some VCs, then a sub-directory called by the
  name of the prover is created next to ``sessions``, with the same
  organization of sub-directories. Each of these package directories contains
  manual proof files. Common proof files to be used across various proofs can
  be stored at the toplevel of the prover-specific directory.

.. index:: project file; compilation switches

Compilation Switches
--------------------

The package ``Prove`` holds switches of |GNATprove| itself. As |GNATprove| also
compiles the sources that it analyzes, it takes into account the attributes
that describe how these sources should be compiled:

* the ``Switches`` and ``Default_Switches`` attributes of the ``Compiler``
  package, for Ada;

* the ``Global_Compilation_Switches`` attribute of the ``Builder`` package, for
  Ada. This is in particular where the ``-gnateT`` switch is
  specified, see :ref:`Target Parameterization`. As the name of the attribute
  indicates, these switches apply globally: they are read from the root project
  and passed to the compilation of every source of the project tree. A
  declaration of this attribute in an imported project has no effect, which is
  also how builders handle it. Use the ``Compiler`` package for switches that
  should only apply to the sources of one project;

* the configuration pragmas designated by the
  ``Builder.Global_Configuration_Pragmas`` and
  ``Compiler.Local_Configuration_Pragmas`` attributes. The global one is read
  from the root project, like the global switches above;

* the switches given after ``-cargs`` on the command line. These are passed
  last, so they take precedence over the switches of the project file.

The other attributes of the ``Builder`` package, in particular ``Switches`` and
``Default_Switches``, are not taken into account. They hold switches of the
builder itself, which describe how to build an executable, a notion that has no
equivalent in |GNATprove|. If your project passes compilation switches such as
``-gnat2022`` through them, move these switches to the ``Compiler`` package, so
that both the builder and |GNATprove| take them into account. Use a scenario
variable if the switches should differ between compilation and verification, as
described in :ref:`Having Different Switches for Compilation and Verification`.
