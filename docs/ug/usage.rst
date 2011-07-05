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

   --mode=       Main mode
       detect      Detect and output Alfa information (default)
       force       Output errors for violations of Alfa (warn unimplemented)
       check       Check consistency of contracts

   --report=     Control reporting
       fail        Report failures to prove VCs (default)
       all         Report all results of proving VCs

..   prove       Prove subprogram contracts and absence of run-time errors

In modes ``detect`` and ``force``, GNATprove does not read the ALI files to
compute an accurate set of global variables read and written in each
subprogram. Hence, its detection of subprograms in Alfa may be slightly more
optimistic than the reality. When generating VCs, on the contrary, the
detection is accurate.

Although reporting is only triggered in mode ``check``, all combinations of
options are allowed.

Output
------

In mode ``detect``, GNATprove prints on the standard output the :ref:`project statistics`.

In mode ``force``, GNATprove prints on the standard output error messages for
violations of Alfa, and warning messages for unimplemented features. 

In mode ``check`` and report ``fail``, GNATprove prints on the standard output
error messages for unproved VCs.

In mode ``check`` and report ``all``, GNATprove prints on the standard output
error messages for unproved VCs, and information messages for proved VCs.

GNATprove always generates :ref:`project statistics` in file ``gnatprove.out``.

For each unit ``<name>``, GNATprove generates a :ref:`summary file`
``<name>.alfa`` in the sub-directory ``gnatprove`` of the corresponding 
object directory.

Integration in GPS
------------------

The current version is not integrated with GPS.

Integration in GNATbench
------------------------

The current version is not integrated with GNATbench.

Current Limitations
-------------------

In mode ``check``, the current version has the following limitations:

   * It only accepts projects with a single object directory; it will stop
     with an error message if run on projects with more than one object
     directory.
   * All units in the project must compile. We recommend to rename files that
     do not compile (such as alternate bodies) to names that do not constitute
     a valid Ada file name, for example using "__".

Using the option ``-gnatec=pragmas.adc`` as Default_Switch in a project file is
not supported. Instead, use ``for Local_Configuration_Pragmas use
"pragmas.adc";``.

Defining multiple units in the same file is not supported. Instead, define each
unit in a separate file.
