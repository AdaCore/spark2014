Usage
=====

The GNATprove tool is packaged as an executable called "gnatprove". Like other
tools in GNAT Pro Toolsuite, GNATprove is based on the structure of GNAT
projects, defined in ``.gpr`` files.

Command-line Usage
------------------

GNATprove is executed with the following command line::

      gnatprove -P <project_file>.gpr

GNATprove accepts the following options::

      --alfa-report    Disable generation of VCs, only output Alfa information
      --report         Print messages for all generated VCs
      --force-alfa     Output errors on non-Alfa constructs, and warnings on
                       unimplemented ones


Integration in GPS
------------------

The current version is not integrated with GPS.

Integration in GNATbench
------------------------

The current version is not integrated with GNATbench.

Current Limitations
-------------------

If the option --alfa-report is not given, the current version has the following
limitations:

   * It only accepts projects with a single object directory; it will stop
     with an error message if run on projects with more than one object
     directory.
   * All units in the project must compile. We recommend to rename files that
     do not compile (such as alternate bodies) to names that do not constitute
     a valid Ada file name, for example using "__".
