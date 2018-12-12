.. _Project Attributes:

Project Attributes
==================

|GNATprove| reads the package ``Prove`` in the given project file. This package
is allowed to contain the following attributes:

* ``Proof_Switches``, which defines additional command line switches that are used
  for the invokation of |GNATprove|. This attribute can be used in two
  different settings:

  * to define switches that should apply to all files in the project.  As an
    example, the following package in the project file sets the default report
    mode of |GNATprove| to ``all``::

      package Prove is
         for Proof_Switches ("Ada") use ("--report=all");
      end Prove;

  * to define switches that should apply only to one file. The following
    example sets timeout for provers run by |GNATprove| to 10 seconds for
    ``file.adb``::

      package Prove is
         for Proof_Switches ("file.adb") use ("--timeout=10");
      end Prove;

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

  The following switches cannot be used inside project files: ``-P``, ``-aP``,
  ``--subdirs``, ``--clean``, ``--list-categories``, ``--version``.

  Only the following switches are allowed for file-specific switches:
  ``--steps``, ``--timeout``, ``--memlimit``, ``--proof``, ``--prover``,
  ``--level``, ``--no-counterexample``, ``--no-inlining``,
  ``--no-loop-unrolling``.

* ``Switches``. This deprecated attribute is the same as ``Proof_Switches
  ("Ada")``.


* ``Proof_Dir``, which defines the directory where are stored the files
  concerning the state of the proof of a project. This directory contains a
  sub-directory ``sessions`` with one directory per source package analyzed for
  proof. Each of these package directories contains a Why3 session file. If a
  manual prover is used to prove some VCs, then a sub-directory called by the
  name of the prover is created next to ``sessions``, with the same
  organization of sub-directories. Each of these package directories contains
  manual proof files. Common proof files to be used across various proofs can
  be stored at the toplevel of the prover-specific directory.

  ..
     COMMENTED OUT BECAUSE NOT WORKING YET
     These common
     files may need to be preprocessed by the proof tool, which can be achieved by
     setting fields ``configure_build`` and ``build_commands`` of the
     corresponding prover section in your ``.why3.conf`` file:

     * ``configure_build`` is the name of a configuration command to run prior to the build commands
     * ``build_commands`` is a list of names of build commands to execute in turn


