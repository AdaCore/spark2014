.. _Project Attributes:

Project Attributes
==================

|GNATprove| reads the package ``Prove`` in the given project file. This package
is allowed to contain the following attributes:

* ``Switches``, which defines additional command line switches that are used
  for the invokation of |GNATprove|. As an example, the following package in
  the project file sets the default report mode of |GNATprove| to ``all``::

    package Prove is
       for Switches use ("--report=all");
    end Prove;

  Switches given on the command line have priority over switches given in the
  project file.

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


