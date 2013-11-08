.. _usage scenarios for spark:

***************************
Usage Scenarios for |SPARK|
***************************

This section discusses in more detail the various types of verification that
|GNATprove| may be used for, ranging from flow analysis to formal verification
of correctness properties.

This section discusses some of the common usage scenarios (or use cases) in
which |SPARK| may be used. It is illustrative, and is certainly not intended
to be an exhaustive list.

.. _develop new code from scratch:

Develop New Code from Scratch
-----------------------------

This is the 'green field' development scenario where new software is
being written and there are no constraints imposed in terms of having
to base the development on pre-existing code. |SPARK| may be used for
all software components or (more likely) the software may be developed
in a mixture of |SPARK|, full Ada and other languages. For example, Ada
may be employed in modules where it is deemed essential to make use of
language features that are not currently in the |SPARK| subset, or in
a safety-related project |SPARK| might be used for all of the
safety-related software components.

A typical development process for this scenario might be:

#. Produce the high level (architectural) design in terms of package
   specifications. Determine which packages will be in |SPARK| and add
   contracts to those packages. The package contracts identify the
   key elements of abstract state, and the subprogram global contracts
   show which subprograms read and write that state. Optionally, dependency
   contracts can be added to specify information flow relations, and
   postconditions can be added to specify high-level properties such
   as safety requiremensts that must be satisfied.
   
#. Identify the |SPARK| packages by adding pragma SPARK_Mode to them. At
   this stage the high-level package structure can be analysed with the tools
   (using the 'Examine' command in GPS) before any executable code is implemented.

#. Begin implementing the package bodies. One typical method of doing this
   is to use a process of top-down decomposition, starting with a top-level
   subprogram specification and implementing the body by breaking it down
   into further (nested) subprograms which are themselves specified but not
   yet implemented, and to iterate until a level is reached where it is
   appropriate to start writing executable code. However the exact process
   is not mandated and will depend on other factors such as the design
   methodology being employed.

#. As each subprogram is implemented it can be verified (against its contract,
   and to show absence of run-time errors) by proof, testing (with assertion
   checking enabled) or both.

   - Users may opt to try proving first then, if a particular proof is
     tricky to discharge, execute test cases to either give confidence that
     the code and contract is correct or to help diagnose why it is failing. 

   - Alternatively, users may prefer to execute the code with suitable
     test cases during development, then use proof to verify it once they
     believe it to be correct.

#. Once verification is complete the executable can be compiled with
   assertion checks either enabled or disabled depending on the policy chosen
   by the project.

.. _convert SPARK 2005 to SPARK 2014:

Convert existing SPARK 2005 software to SPARK 2014
--------------------------------------------------

If an existing piece of software has been developed in SPARK 2005 and is
still undergoing active development/maintenance then it may be advantageous
to upgrade to using SPARK 2014 in order to make use of the larger language
subset and the new tools and environment. The |SPARK| Language Reference Manual
has an appendix containing a SPARK 2005 to |SPARK| Mapping Specification which
can be used to guide the conversion process. As the |SPARK| subset is larger
then the SPARK 2005 subset, and the mapping of features between the two languages
is defined, the translation should be relatively straightforward. There are two
main options for the conversion process:

#. All of the software is converted from SPARK 2005 to |SPARK| at the same time.
   The |SPARK| tools should be used to analyse the work in progress throughout
   the conversion process (which implies that a bottom-up approach may work best)
   and any errors corrected as they are found. Once the conversion is complete,
   development and maintenance can continue in |SPARK|.

#. A more gradual approach could be employed, where code is only converted to
   |SPARK| when it needs to be changed. (The granularity of how much code needs
   to be converted when a module is touched should be considered, and is likely to
   be at the level of the whole package.) The |SPARK| tools can then be used to
   analyse the new/changed code, and will attempt to analyse any dependent units,
   which may or may not be in |SPARK|. It is not necessary for dependent units to
   be fully in |SPARK| but any declarations from them that are used in |SPARK|
   packages must be in |SPARK|. 

.. _analse legacy Ada software:

Analyse legacy Ada software
---------------------------

If a legacy system has been developed in Ada then analysing it with the |SPARK|
tools may be a good first step in order to assess the quality of the code prior
to performing a full or partial conversion to |SPARK|. The suggested workflow is:

#. Identify units which are highest priority for conversion to |SPARK|. These may
   already be known, or potential candidates could be identified by:

   - putting pragma SPARK_Mode in a global configuration file so that all code is
     analysed as if it were intended to be |SPARK|;

   - running the 'Examine' command on all code;

   - use the errors in the summary report to guide the selection process - files
     with fewer errors are likely to be easier to convert and would be a good
     starting point;

   - remove the global configuration pragma SPARK_Mode before proceeding.

#. For each unit to be converted to |SPARK|:

   - Identify the specification as |SPARK| (SPARK_Mode => On) but identify the body
     as not in |SPARK| (SPARK_Mode => Off).

   - Analyse (Examine) the specification and correct any errors that are reported
     by the tools, iterating until no errors remain.

   - Mark the body as |SPARK| (change SPARK_Mode from Off to On).

   - Analyse (Examine) the body and correct any errors that are reported
     by the tools, iterating until no errors remain.

   - Each subprogram can then be verified to show absence of run-time errors by proof,
     testing (with assertion checking enabled) or both.

     - Users may opt to try proving first then, if a particular proof is
       tricky to discharge, execute test cases to either give confidence that
       the code is correct or to help diagnose why it is failing. 

     - Alternatively, users may prefer to execute the code with suitable
       test cases first, then use proof to verify it once they believe it
       to be correct.

#. Once conversion and verification is complete, the executable can be compiled with
   assertion checks either enabled or disabled depending on the policy chosen
   by the project. At this point users might begin adding contracts to the code in
   order to perform verification of functional properties.

