Usage
=====

The gnatprove tool is packaged as an executable called "gnatprove".

Command-line Usage
------------------

Gnatprove is executed with the following command line::

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
