Usage
=====

The GNATprove tool is packaged as an executable called "gnatprove". Like other
tools in GNAT Pro Toolsuite, GNATprove is based on the structure of GNAT
projects, defined in ``.gpr`` files.

Command-line Usage
------------------

GNATprove is executed with the following command line::

      gnatprove -P <project_file>.gpr


Integration in GPS
------------------

The current version is not integrated with GPS.

Integration in GNATbench
------------------------

The current version is not integrated with GNATbench.

Current Limitations
-------------------

The current version only accepts projects with a single object directory; it
will stop with an error message if run on projects with more than one object
directory.
