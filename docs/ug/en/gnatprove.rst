.. _Formal Verification with GNATprove:

************************************
Formal Verification with |GNATprove|
************************************

The |GNATprove| tool is packaged as an executable called ``gnatprove``. Like
other tools in |GNAT Pro| toolsuite, |GNATprove| is based on the structure of
GNAT projects, defined in ``.gpr`` files.

A crucial feature of |GNATprove| is that it interprets annotations exactly like
they are interpreted at run time during tests. In particular, their executable
semantics includes the verification of run-time checks, which can be verified
statically with |GNATprove|. |GNATprove| also performs additional verifications
on the specification of the expected behavior itself, and its correspondence to
the code.

.. only : : core

   .. toctree::
      :maxdepth: 2

      source/how_to_run_gnatprove
      source/how_to_view_gnatprove_output
      source/how_to_use_gnatprove_in_a_team
      source/how_to_investigate_unproved_checks

.. only:: full

   .. toctree::
      :maxdepth: 2

      source/how_to_run_gnatprove
      source/how_to_view_gnatprove_output
      source/how_to_use_gnatprove_in_a_team
      source/how_to_write_subprogram_contracts
      source/how_to_write_object_oriented_contracts
      source/how_to_write_package_contracts
      source/how_to_write_loop_invariants
      source/how_to_investigate_unproved_checks
      source/gnatprove_by_example
      source/examples_in_the_toolset_distribution
