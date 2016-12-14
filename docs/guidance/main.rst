Objectives and Contents
=======================

This document was written to facilitate the adoption of SPARK. It targets team leaders and technology experts, who will find a description of the various assurance levels at which the technology can be used, with the associated costs and benefits. It targets software developers (with some knowledge of Ada language and AdaCore technology), who will find detailed guidance of how to adopt SPARK at every assurance level.


Section :ref:`Assurance Levels` presents the four assurance levels considered in this document. It starts with a brief introduction of the Ada programming language and its SPARK subset. It then presents the levels Stone, Bronze, Silver and Gold that can be achieved with the use of SPARK language and toolset, from simply applying the language subset up to using the most powerful analyses. The lowest levels are the simplest to adopt and already bring significant benefits. The highest levels require more effort to adopt and bring the most guarantees. This section is particularly suited for team leaders and technology experts who want to understand how SPARK could be useful in their context.


Sections :ref:`Stone Level` to :ref:`Gold Level` present in details the four assurance levels. Each section starts with a short description of three key aspects to adopt SPARK at that level:


* Benefits - What is gained from adopting SPARK?
* Impact on Process - How should the process be adapted to use SPARK?
* Costs and Limitations - What are the main costs and limitations for adopting SPARK?


In the rest of each section, we consider how to progressively adopt SPARK at that level in an Ada project. Section :ref:`Example` shows an example of application for all four levels. These sections are particularly suited for software developers who need to use SPARK at a given level.


Although this document is about adopting SPARK on existing Ada code, the same guidelines can be used for adopting SPARK from the start of a project. The main difference in that case is that one would not want to start at the lowest level but already take into account the final targeted level since the initial design phase.


This version of the document uses the tool versions SPARK Pro 17 and GPS 17. Further references are given at the end of this document.

.. _Assurance Levels:

Assurance Levels
================

Ada
---

Ada is a language for long-lived critical systems. Programming in Ada makes it easier to prevent the introduction of errors in programs, thanks to the stronger language rules than in many comparative languages (C and C++ in particular, including their safer variants like MISRA C and MISRA C++), which makes it possible for the compiler to reject erroneous programs. Programming in Ada also makes it easier to detect the presence of errors in programs, thanks to the language rules mandating run-time checking of type safety and memory safety conditions which cannot be checked at compile time, so that violating these conditions during testing leads to exceptions rather than undefined behavior.


A lesser known advantage of programming in Ada is its greater number of language features for embedding program specifications inside the program, starting from mundane properties of data like ranges of values to rich data invariants expressed with arbitrary boolean expressions. An important addition to this list of features is the ability to state contracts on subprograms, consisting in preconditions and postconditions, which was a central part of the Ada 2012 version of the language.


Preconditions are properties that should hold when a subprogram is called. In typical software development in Ada or other languages, preconditions are stated in the program as comments accompanying subprogram declarations, or as defensive code inside subprograms to detect improper calling contexts. When using the latest version of Ada, developers can express preconditions as boolean properties which should hold when a subprogram is called, and the compiler can insert run-time checks that preconditions hold when the subprogram is called.


Postconditions are properties that should hold when a subprogram returns. In typical software development in Ada or other languages, postconditions are stated in the program as comments accompanying subprogram declarations, as assertions inside subprograms to detect implementation errors, or as defensive code to detect improper values returned at the call site. When using the latest version of Ada, developers can express postconditions as boolean properties which should hold when a subprogram returns, and the compiler can insert run-time checks that postconditions hold when the subprogram returns.


The main use of preconditions and postconditions, like other language features in Ada for embedding program specifications inside the program, is to allow the detection of violations of these program specifications during testing. Another increasingly important use of these language features is to facilitate the detection of errors by static analyzers, which analyze the source code of programs without actually executing them. Without such specifications in the program, static analyzers can only detect violations of language dynamic constraints (e.g. division by zero or buffer overflow). The presence of such specifications in the program allows static analyzers to target the verification of higher level properties. Specifications also constrain the state space that the static analyzer has to consider during analysis, which leads to faster running time and better precision.


SPARK
-----

Static analyzers fall into two broad categories: bug finders and verifiers. Bug finders detect violations of properties. Verifiers guarantee the absence of violations of properties. Because they target opposite goals, bug finders and verifiers have usually different architectures, they are based on different technologies, and they require different methodologies. Typically, bug finders require little upfront work, but may generate many false alarms which need to be manually triaged and addressed. Typically, verifiers require some upfront work, but generate fewer false alarms thanks to the use of more powerful techniques. AdaCore develops and distributes one bug finder (CodePeer) and one verifier (SPARK).


SPARK is a verifier co-developed by AdaCore and Altran and distributed by AdaCore. The main webpage for the SPARK Pro product is http://www.adacore.com/sparkpro/. SPARK analysis can give strong guarantees that a program:


* does not read uninitialized data,
* accesses global data as intended,
* does not contain concurrency errors (deadlocks and data races),
* does not contain run-time errors (e.g. division by zero or buffer overflow),
* respects key integrity properties (e.g. interaction between components or global invariants),
* is a correct implementation of software requirements expressed as contracts.


SPARK analysis can be applied to the complete program or only parts of it. SPARK analysis can only be applied to parts of the program that do not explicitly use pointers (but references and addresses are allowed) and that do not catch exceptions. Pointers and exceptions are both features that make formal verification as done in SPARK infeasible, either because of limitations of state-of-the-art technology or because of the disproportionate effort required from users to apply formal verification in such cases. The large subset of Ada that is analyzed by SPARK is also called the SPARK language subset. SPARK builds on the strengths of Ada to provide even more guarantees statically rather than dynamically. As summarized in the following table, Ada provides strict clear syntax and strong typing at compile time, plus dynamic checking of runtime errors and program contracts. SPARK allows to perform such checking statically. In addition, it enforces the use of a safer language subset and detects data flow errors statically.

.. csv-table::
   :header: "", "Ada", "SPARK"
   :widths: 1, 1, 1

   "Contract programming", "dynamic", "dynamic / static"
   "Runtime errors",       "dynamic", "dynamic / static"
   "Data flow errors",     "--",       "static"
   "Strong typing",        "static",  "static"
   "Safer language subset","--",       "static"
   "Strict clear syntax",  "static",  "static"


The main benefit of formal program verification, as proposed in SPARK and similarly with Frama-C for C code, is that they allow verifying properties that are difficult or very costly to verify by other methods, like testing or reviews. The difficulty may originate in the complexity of the software, the complexity of the requirement, or the unknown capabilities of attackers. Formal verification allows to give guarantees that some properties are always verified, however complex the context. The latest versions of international certification standards for avionics (DO-178C) and railway (CENELEC 20128:2011) have recognized these benefits by augmenting the role that formal methods can play in the development of critical software.

Levels of SPARK Use
-------------------

The scope and level of SPARK analysis depend on the objectives being pursued by the adoption of SPARK. The scope of analysis may be the totality of a project, only some units, or only parts of units. The level of analysis may range from simple guarantees provided by flow analysis to complex properties being proved, that can be divided in five easily remembered levels:


#. Stone level - valid SPARK
#. Bronze level - initialization and correct data flow
#. Silver level - absence of run-time errors (AoRTE)
#. Gold level - proof of key integrity properties
#. Platinum level - full functional proof of requirements


Platinum level is defined here for completeness, but it is not further elaborated in this document, as it is not advised during adoption of SPARK. Each level builds on the previous one, so that the code subject to Gold level should be a subset of the code subject to Silver level, itself a subset of the code subject to Bronze level, which is in general the same as the code subject to Stone level. We advise to use:


* Stone level only as an intermediate level during adoption,
* Bronze level for the largest part of the code as possible,
* Silver level as the default target for critical software (subject to costs and limitations),
* Gold level only for a subset of the code subject to specific key integrity (safety/security) properties.


Our starting point is a program in Ada, which could be thought of as the Brick level: thanks to the use of Ada programming language, this level already provides some confidence. It is the highest level in The Three Little Pigs fable! And indeed languages with weaker semantics could be thought of as Straw and Sticks levels. However, the adoption of SPARK allows us to get stronger guarantees, should the wolf in the fable adopt more aggressive means of attack than blowing.


In the following, we will use SPARK to denote the SPARK language, and GNATprove to denote the formal verification tool in SPARK product.


.. _Stone Level:

Stone Level - Valid SPARK
=========================

The goal of reaching this level is to identify as much code as possible as belonging to the SPARK subset. The user is responsible for identifying candidate SPARK code by applying the marker “SPARK_Mode” to signal SPARK code to GNATprove. GNATprove is responsible for checking that the code marked with “SPARK_Mode” is indeed valid SPARK code. Note that valid SPARK code may still be wrong in many ways, such as raising run-time exceptions. Being valid means that this code respects the legality rules which define the SPARK subset in SPARK Reference Manual (see http://docs.adacore.com/spark2014-docs/html/lrm/). The number of lines of SPARK code in a program can be computed (along with other metrics such as the total number of lines of code) by the tool being developed at AdaCore as a future replacement for GNATmetric.

.. rubric:: Benefits

The stricter SPARK rules are enforced on a possibly large part of the program, which leads to better quality and maintainability, as error-prone features like side-effects in functions and aliasing between parameters are avoided, and others like use of pointers are isolated in non-SPARK parts of the program. Personal and peer review processes can be lightened on parts of the program in SPARK, as analysis automatically eliminates some categories of defects. Parts of the program that do not respect the SPARK rules are carefully isolated and can be more thoroughly reviewed and tested.

.. rubric:: Impact on Process

After the initial pass to apply SPARK rules to the program, evolutive maintenance of SPARK code is similar to evolutive maintenance of Ada code, with a few additional rules to avoid side-effects in functions and aliasing between parameters for example. These additional rules are checked automatically by running GNATprove on the modified program, which can be done both by the developer before pushing her changes, and by the automatic system (continuous builder, regression testsuite, etc.)

.. rubric:: Costs and Limitations

Pointer-heavy code needs to be rewritten to remove the use of pointers or to hide pointers from SPARK analysis, which may be difficult. The initial pass may require large (but shallow) rewrites in order to transform the code, in particular to rewrite functions with side-effects into procedures.

Initial Setup
-------------

GNATprove can only be applied to the sources of a GNAT project (a file with extension “gpr” describing source files and switches to GNAT compiler and other tools in the GNAT tool suite). As an installation check, we should start by applying GNATprove to the project with no “SPARK_Mode” at all::

  > gnatprove -P my_project.gpr --mode=check -j0


Switch -j0 is used to analyze files from the project in parallel, using as many cores there are on the machine, and switch --mode=check runs GNATprove in fast checking mode. GNATprove should output the following messages::


  Phase 1 of 2: generation of Global contracts ...
  Phase 2 of 2: fast partial checking of SPARK legality rules ...


If you installed SPARK in a different repository from GNAT, you may get errors about project files not found if your project depends on XML/Ada or GNATCOLL or any other project distributed with GNAT. In that case, you should update environment variable GPR_PROJECT_PATH as indicated in the SPARK User’s Guide:
http://docs.adacore.com/spark2014-docs/html/ug/install.html


After you manage to run GNATprove without errors, pick a simple unit in the project, preferably a leaf unit that does not depend on other units, and apply the “SPARK_Mode” marker to it, by adding the following pragma at the start of the spec file (typically a file with extension “ads”) and the body file (typically a file with extension “adb”) for this unit:

.. code-block:: ada

   pragma SPARK_Mode;


Then apply GNATprove to the project again::

  > gnatprove -P my_project.gpr --mode=check -j0


GNATprove should output the following messages, stating that SPARK legality rules were checked on the unit marked, possibly followed by a number of error messages pointing to locations in the code where SPARK rules are violated::

  Phase 1 of 2: generation of Global contracts ...
  Phase 2 of 2: checking of SPARK legality rules ...

If you applied SPARK_Mode to a spec file without body (e.g. a unit defining only constants), then GNATprove will notify you that no body was really analyzed::


  Phase 1 of 2: generation of Global contracts ...
  Phase 2 of 2: flow analysis and proof ...
  warning: no bodies have been analyzed by GNATprove
  enable analysis of a body using SPARK_Mode


At this point, you should switch to using GNAT Pro Studio (GPS), the integrated development environment provided with GNAT, in order to more easily interact with GNATprove. GPS provides in particular basic facilities for code navigation and error location that facilitate the adoption of SPARK. Open GPS on your project::


  > gps -P my_project.gpr


There should be a SPARK menu available. Repeat the previous action within GPS by selecting menu SPARK → Examine All, then select the “check fast” mode in the popup window that opens, and click on “Execute”. The following snapshot shows the popup window from GPS with these settings:

.. image:: _static/check_fast.png
   :align: center
   :alt: Popup window from GPS for "check fast" mode




GNATprove should output the same messages as before. If some error messages are generated, they should now be located on the code that violates SPARK rules.


At this point, you managed to run GNATprove successfully on your project. The next step is to evaluate how much code can be identified as SPARK code. The easiest way to do that is to start by applying the marker “SPARK_Mode” to all files, using a script like the following shell script:

.. code-block:: shell

  # mark.sh
  for file in $@; do
     echo 'pragma SPARK_Mode;' > temp
     cat $file >> temp
     mv temp $file
  done


or the following python script:

.. code-block:: python

  # mark.py
  import sys
  for filename in sys.argv[1:]:
      with open(filename, 'r+') as f:
          content = f.read()
          f.seek(0, 0)
          f.write('pragma SPARK_Mode;\n' + content)


These scripts, when called on a list of files as command-line arguments, simply insert a line with the pragma SPARK_Mode at the beginning of each file. The list of files from a project can be obtained by calling GPRls when the project has main files (that is, it generates executables instead of libraries)::


  > gprls -P my_project.gpr --closure


or else GPRbuild with suitable arguments as follows::


  > gprbuild -q -f -c -P my_project.gpr -gnatd.n | grep -v adainclude | sort | uniq


One you have obtained the list of Ada source files in the project, by one of the two methods mentioned previously, you can systematically apply the “SPARK_Mode” marker to all these files with the small shell or python script that we saw before::


  > cat list_of_sources.txt | mark.sh

or::

  > cat list_of_sources.txt | python mark.py


Then open GPS on your project, and rerun SPARK validity checker by selecting menu SPARK → Examine All, then select the “check fast” mode in the popup window that opens, and click on “Execute”. This mode does not issue all possible violations of SPARK rules, but it runs much faster, thus it is in general beneficial to run it first. GNATprove should output error messages located on code that violates SPARK rules. The section on “Dealing with SPARK Violations” explains how to address these violations by either modifying the code or excluding it from analysis.


After all the messages have been addressed, you should rerun SPARK validity checker in a mode where all possible violations are issued by selecting menu SPARK → Examine All, then select the “check all” mode in the popup window that opens, and click on “Execute”.  Again, GNATprove should output error messages located on code that violates SPARK rules, which should be addressed as detailed in section “Dealing with SPARK Violations”.


A usual warning that is issued by GNATprove at this stage is the following::


  warning: no Global contract available for "F"
  warning: assuming "F" has no effect on global items


This warning simply informs you that GNATprove could not compute a summary of the global variables read and written by subprogram F, either because it comes from an externally built library (such as the GNAT standard library, or XML/Ada, etc.) or because the implementation for F is not available to the analysis (for example if the code was not yet developed, or the subprogram is imported, or the file with F’s implementation is excluded from analysis). You can provide this information to GNATprove by adding a Global contract to F’s declaration (see the section on Global Contract). Alternatively, you can silence this specific warning by adding the following pragma in the files that raise this warning, or in a global configuration pragma file:

.. code-block:: ada

   pragma Warnings (Off, "no Global Contract available",
                    Reason => "External subprograms have no effect on globals");


Note that - if required - you can silence all warnings from GNATprove with the switch --warnings=off.

Dealing with SPARK Violations
-----------------------------

For each violation reported by GNATprove, you should decide whether to modify the code to make it respect the constraints of the SPARK subset or to exclude the code from analysis. In the first case, GNATprove will be able to analyze the modified code; in the second case, the code will be ignored during the analysis. It is thus preferable to modify the code whenever possible, and to resort to excluding code from analysis only as a last option.

Excluding Code From Analysis
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

There are multiple ways to exclude code from analysis. Depending on the location of the violation, it may be more appropriate to exclude the enclosing subprogram or package or the complete enclosing unit.

.. rubric:: Excluding a Subprogram From Analysis

When a violation occurs in a subprogram body, this specific subprogram body can be excluded from analysis by annotating it with aspect SPARK_Mode with value Off as follows:

.. code-block:: ada

   procedure Proc_To_Exclude (..) with SPARK_Mode => Off is ...
   function Func_To_Exclude (..) return T with SPARK_Mode => Off is ...


When the violation occurs in the subprogram spec, then both the spec and body must be excluded from analysis by annotating them both with aspect SPARK_Mode with value Off. The annotation on the subprogram body is given above, and the annotation on the subprogram spec is similar:


.. code-block:: ada

   procedure Proc_To_Exclude (..) with SPARK_Mode => Off;
   function Func_To_Exclude (..) return T with SPARK_Mode => Off;


Note that only top-level subprograms can be excluded from analysis, i.e. subprogram units or subprograms declared inside package units, but not nested subprograms declared inside other subprograms. If a violation occurs inside a nested subprogram, then the enclosing top-level subprogram needs to be excluded from analysis.


When only the subprogram body is excluded from analysis, then the subprogram can still be called in SPARK code. When both the subprogram spec and body are excluded from analysis, then all the code that calls the subprogram must also be excluded from analysis.

.. rubric:: Excluding a Package From Analysis

Like subprograms, only top-level packages can be excluded from analysis, i.e. package units or packages declared inside package units, but not nested packages declared inside subprograms. If a violation occurs inside a nested package, then the enclosing top-level subprogram needs to be excluded from analysis. The case of local packages declared inside packages is similar to the case of subprograms, so in the following we only consider package units.


When a violation occurs in a package body, either it occurs inside a subprogram/package in this package body, in which case the local subprogram/package alone can be excluded from analysis, or otherwise the complete package body can be excluded from analysis by removing the pragma SPARK_Mode that was inserted at the start of the file. In that mode, it is still possible to analyse subprograms/packages declared inside the package body, by annotating them with aspect SPARK_Mode with value On as follows:

.. code-block:: ada

   --  no pragma SPARK_Mode here
   package body Pack_To_Exclude is ...
      procedure Proc_To_Analyze (..) with SPARK_Mode => On is ...
      package body Pack_To_Analyze with SPARK_Mode => On is ...
   end Pack_To_Exclude;


When the violation occurs in the package spec, three cases are possible:
The violation occurs inside the declaration of a subprogram/package in this package spec. In that case, the local subprogram/package alone can be excluded from analysis, by excluding both the local subprogram/package spec and the corresponding local subprogram/package body from analysis, by annotating them with aspect SPARK_Mode with value Off as follows:

.. code-block:: ada

   pragma SPARK_Mode;
   package Pack_To_Analyze is
      procedure Proc_To_Exclude (..) with SPARK_Mode => Off;
      package Pack_To_Exclude with SPARK_Mode => Off is ...
   end Pack_To_Analyze;

   pragma SPARK_Mode;
   package body Pack_To_Analyze is ...
      procedure Proc_To_Exclude (..) with SPARK_Mode => Off is ...
      package body Pack_To_Exclude with SPARK_Mode => Off is ...
   end Pack_To_Analyze;


The violation occurs directly inside the private part of the package spec. In that case, the private of the package can be excluded from analysis by inserting pragma SPARK_Mode with value Off at the start of the private part and by removing the pragma SPARK_Mode that was inserted at the start of the file for the package body. In that mode, entities declared in the visible part of the package spec (types, variables, subprograms, etc.) can still be used in SPARK code in other units, provided these declarations do not violate SPARK rules. In that mode, it is also possible to analyse subprograms/packages declared inside the package, by annotating them with aspect SPARK_Mode with value On as follows:

.. code-block:: ada

   pragma SPARK_Mode;
   package Pack_To_Use is ...
      --  declarations that can be used in SPARK code
   private
      pragma SPARK_Mode (Off);
      --  declarations that cannot be used in SPARK code
   end Pack_To_Use;

   --  no pragma SPARK_Mode here
   package body Pack_To_Use is ...
      procedure Proc_To_Analyze (..) with SPARK_Mode => On is ...
      package body Pack_To_Analyze with SPARK_Mode => On is ...
   end Pack_To_Use;


The violation occurs directly inside the package spec. In that case, the complete package can be excluded from analysis by removing the pragma SPARK_Mode that was inserted at the start of both files for the package spec and the package body. In that mode, entities declared in the package spec (types, variables, subprograms, etc.) can still be used in SPARK code in other units, provided these declarations do not violate SPARK rules. In that mode, it is also possible to analyse subprograms/packages declared inside the package, by annotating them with aspect SPARK_Mode with value On as follows:

.. code-block:: ada

   --  no pragma SPARK_Mode here
   package Pack_To_Exclude is ...
      procedure Proc_To_Analyze (..) with SPARK_Mode => On;
      package Pack_To_Analyze with SPARK_Mode => On is ...
   end Pack_To_Exclude;

   --  no pragma SPARK_Mode here
   package body Pack_To_Exclude is ...
      procedure Proc_To_Analyze (..) with SPARK_Mode => On is ...
      package body Pack_To_Analyze with SPARK_Mode => On is ...
   end Pack_To_Exclude;


Note that cases 2 and 3 above are not exclusive, when a violation occurs inside the private part of the package spec. In case 2, all declarations in the visible part of the package are analyzed, as well as their bodies when explicitly marked with aspect SPARK_Mode. In case 3, only those declarations and bodies explicitly marked with aspect SPARK_Mode are analyzed.

Modifying Code To Remove SPARK Violations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In many cases, code can be modified so that either SPARK violations are removed completely, or violations can be moved to some part of the code that does not prevent most of the code from being analyzed. This is in general a good idea because SPARK violations point to features that can easily lead to code that is more difficult to maintain (like side effects in functions) or to understand (like pointers). In the following, we consider typical SPARK violations found in Ada code, and how to address these by modifying the code. When code modification is not possible or too complex/costly, the code with the violation should be excluded from analysis by following the recommendations of the previous section. The following table lists the main restrictions of SPARK leading to violations in Ada code, and how they are typically addressed, as detailed in the rest of this section.




.. csv-table::
   :header: "", "How to remove the violation?", "How to hide the violation?"
   :widths: 1, 1, 1

   "Use of access type", "Use references, addresses, or indexes in an array or a collection", "Use a private type, defined as access type in a private section marked SPARK_Mode Off"
   "Side-effect in function", "Transform function in procedure with additional parameter for result", "Mark function body with SPARK_Mode Off and function spec with Global => null to hide side-effect"
   "Exception handler", "Use result value to notify caller of error when recovery is required", "Split subprogram into functionality without exception handler, and wrapper with exception handler marked with SPARK_Mode Off"




In the following, we consider error messages that are issued in each case.

.. rubric:: access to "T" is not allowed in SPARK

See “access type is not allowed in SPARK”

.. rubric:: access type is not allowed in SPARK

These errors are issued on uses of access types (“pointers”). For example:

.. code-block:: ada

   Data1 : Integer;
   Data2 : Boolean;
   Data3 : access Integer;  << VIOLATION

   procedure Operate is
   begin
      Data1 := 42;
      Data2 := False;
      Data3.all := 42;  << VIOLATION
   end Operate;


In some cases, the uses of access types can be extracted from the subprogram and grouped in a helper subprogram which is excluded from analysis. For example, we can modify the code above as follows, where both the declaration of global variable Data3 of access type and the assignment to Data3.all are grouped in a package body Memory_Accesses that is excluded from analysis, while the package spec for Memory_Accesses can be used in SPARK code:

.. code-block:: ada

   Data1 : Integer;
   Data2 : Boolean;

   package Memory_Accesses is
      procedure Write_Data3 (V : Integer);
   end Memory_Accesses;

   package body Memory_Accesses
     with SPARK_Mode => Off
   is
      Data3 : access Integer;

      procedure Write_Data3 (V : Integer) is
      begin
             Data3.all := V;
      end Write_Data3;
   end Memory_Accesses;

   procedure Operate is
   begin
      Data1 := 42;
      Data2 := False;
      Memory_Accesses.Write_Data3 (42);
   end Operate;


In other cases, the access type needs to be visible from client code, but the fact that it is implemented as an access type needs not be visible to client code. Here is an example of such a case:

.. code-block:: ada

   type Ptr is access Integer;  << VIOLATION

   procedure Operate (Data1, Data2, Data3 : Ptr) is
   begin
      Data1.all := Data2.all;
      Data2.all := Data2.all + Data3.all;
      Data3.all := 42;
   end Operate;


In that case, the access type can be made a private type of a local package, or of a package defined in a different unit, whose private part (and possibly also its package body) is excluded from analysis. For example, we can modify the code above as follows, where the type Ptr together with accessors to query and update objects of type Ptr are grouped in package Ptr_Accesses:

.. code-block:: ada

   package Ptr_Accesses is
      type Ptr is private;
      function Get (X : Ptr) return Integer;
      procedure Set (X : Ptr; V : Integer);
   private
      pragma SPARK_Mode (Off);
      type Ptr is access Integer;
   end Ptr_Accesses;

   package body Ptr_Accesses
     with SPARK_Mode => Off
   is
      function Get (X : Ptr) return Integer is (X.all);
      procedure Set (X : Ptr; V : Integer) is
      begin
             X.all := V;
      end Set;
   end Ptr_Accesses;

   procedure Operate (Data1, Data2, Data3 : Ptr_Accesses.Ptr) is
      use Ptr_Accesses;
   begin
      Set (Data1, Get (Data2));
      Set (Data2, Get (Data2) + Get (Data3));
      Set (Data3, 42);
   end Operate;

.. rubric:: explicit dereference is not allowed in SPARK

See “access type is not allowed in SPARK”

.. rubric:: function with "in out" parameter is not allowed in SPARK

This error is issued on a function with an “in out” parameter. For example:

.. code-block:: ada

   function Increment_And_Add (X, Y : in out Integer) return Integer is  << VIOLATION
   begin
      X := X + 1;
      Y := Y + 1;
      return X + Y;
   end Increment_And_Add;


The function can be transformed into a procedure by adding an “out” parameter for the returned value, as follows:

.. code-block:: ada

   procedure Increment_And_Add (X, Y : in out Integer; Result : out Integer) is
   begin
      X := X + 1;
      Y := Y + 1;
      Result := X + Y;
   end Increment_And_Add;

.. rubric:: function with output global "X" is not allowed in SPARK

This error is issued on a function with a side-effect on variables in scope. For example:

.. code-block:: ada

   Count : Integer := 0;

   function Increment return Integer is
   begin
      Count := Count + 1;  << VIOLATION
      return Count;
   end Increment;


The function can be transformed into a procedure by adding an “out” parameter for the returned value, as follows:

.. code-block:: ada

   procedure Increment (Result : out Integer) is
   begin
      Count := Count + 1;
      Result := Count;
   end Increment;


Alternatively, when the side-effects have no influence on the properties to verify, they can be masked to the analysis. For example, consider a procedure Log which writes in global data, causing all of its callers to have side-effects:

.. code-block:: ada

   Last : Integer := 0;

   procedure Log (X : Integer) is
   begin
      Last := X;
   end Log;

   function Increment_And_Log (X : Integer) return Integer is
   begin
      Log (X);  << VIOLATION
      return X + 1;
   end Increment_And_Log;


A legitimate solution here is to mask the side-effects in procedure Log for the analysis, by annotating the spec of Log with an aspect Global with value “null” and by excluding the body of Log from analysis:

.. code-block:: ada

   procedure Log (X : Integer)
     with Global => null;

   Last : Integer := 0;

   procedure Log (X : Integer)
     with SPARK_Mode => Off
   is
   begin
      Last := X;
   end Log;

   function Increment_And_Log (X : Integer) return Integer is
   begin
      Log (X);
      return X + 1;
   end Increment_And_Log;

.. rubric:: handler is not allowed in SPARK

This error is issued on exception handlers. For example on the following code:

.. code-block:: ada

   Not_Found : exception;

   procedure Find_Before_Delim
     (S        : String;
      C, Delim : Character;
      Found    : out Boolean;
      Position : out Positive)
   is
   begin
      for J in S'Range loop
             if S(J) = Delim then
            raise Not_Found;
         elsif S(J) = C then
                Position := J;
                Found := True;
                    Return;
         end if;
      end loop;
      raise Not_Found;
   exception                            << VIOLATION
      when Not_Found =>
             Position := 1;
         Found := False;
   end Find_Before_Delim;


The subprogram with an exception handler can usually be split between a core functionality which may raise exceptions but does not contain an exception handler, which can be analyzed, and a wrapper calling the core functionality that contains the exception handler and is excluded from analysis. For example, we can modify the code above to perform the search for a character in function Find_Before_Delim, which raises an exception if the desired character is not found before the delimiter character or the end of the string, and a procedure Find_Before_Delim which wraps the call to function Find_Before_Delim, as follows:

.. code-block:: ada

   Not_Found : exception;

   function Find_Before_Delim (S : String; C, Delim : Character) return Positive is
   begin
      for J in S'Range loop
             if S(J) = Delim then
            raise Not_Found;
         elsif S(J) = C then
                    return J;
         end if;
      end loop;
      raise Not_Found;
   end Find_Before_Delim;

   procedure Find_Before_Delim
     (S        : String;
      C, Delim : Character;
      Found    : out Boolean;
      Position : out Positive)
     with SPARK_Mode => Off
   is
   begin
      Position := Find_Before_Delim (S, C, Delim);
      Found := True;
   exception
      when Not_Found =>
             Position := 1;
         Found := False;
   end Find_Before_Delim;


.. rubric:: side effects of function "F" are not modeled in SPARK

This error is issued on a call to a function with side-effects on variables in scopes. Note that a corresponding error “function with output global "X" is not allowed in SPARK” will also be output on function F if it is marked SPARK_Mode with value On (directly or in a region of code marked as such). For example on the following code calling the function Increment_And_Log seen previously:

.. code-block:: ada

   procedure Call_Increment_And_Log is
      X : Integer;
   begin
      X := Increment_And_Log (10);   << VIOLATION
   end Call_Increment_And_Log;


The called function may be transformed into a procedure as seen previously. If it is not marked SPARK_Mode with value On, then a legitimate solution might be to mask its side-effects for the analysis, by annotating its spec with an aspect Global with value “null”.

.. _Bronze Level:

Bronze Level - Initialization and Correct Data Flow
===================================================

The goal of reaching this level is to make sure no uninitialized data can ever be read and, optionally, to prevent unintended access to global variables. This also ensures that there is no possible interference between parameters and global variables, when the same variable is passed multiple times to a subprogram, both as a parameter or a global variable.

.. rubric:: Benefits

The SPARK code is guaranteed to be free from a number of defects: no reads of uninitialized variables, no possible interference between parameters and global variables, no unintended access to global variables.


When Global contracts are used to specify the global variables read and/or written by subprograms, maintenance is facilitated by a clear documentation of intent, which is checked automatically by running GNATprove, so that any mismatch between the implementation and the specification is reported.

.. rubric:: Impact on Process

An initial pass will be required where flow analysis is switched on and the resulting messages are resolved by either rewriting code or justifying any false alarms. Once this is complete, evolutive maintenance can maintain the same guarantees at low cost from developers. A few simple idioms can be used to avoid most false alarms, and remaining false alarms can be justified simply.

.. rubric:: Costs and Limitations

The initial pass may require a substantial effort to get rid of all false alarms, depending on the coding style adopted so far. The analysis may take a long time (up to an hour) on large programs (but it is guaranteed to terminate). Flow analysis is by construction limited to local understanding of the code, with no knowledge of values (only code paths), and handling of whole variables only through calls (not component by component), which may lead to false alarms.

Running GNATprove in Flow Analysis Mode
---------------------------------------

Two distinct static analyses are performed by GNATprove. Flow analysis is the fastest and requires no user written annotation. It tracks the flow of information between variables on a per subprogram basis. In particular, it allows to find every potential use of uninitialized data. The second analysis, proof, will be described in the sections on silver level and gold level.

To run GNATprove in flow analysis mode on your project, select menu SPARK → Examine All. In the GPS panel, select the “flow analysis” mode, check the box “Do not report warnings”, uncheck the box “Report checks proved”, and click on “Execute”. The following snapshot shows the popup window from GPS with these settings:

.. image:: _static/flow_analysis.png
   :align: center
   :alt: Popup window from GPS for "flow analysis" mode

GNATprove should output the following messages, potentially followed by a number of messages pointing to potential problems in your program::

  Phase 1 of 2: generation of Global contracts ...
  Phase 2 of 2: analysis of data and information flow ...

The following messages output by GNATprove are check messages and should have the form::

  medium: "V" might not be initialized

First comes the severity of the check. It is one of low/medium/high and reflects both the likelihood that the reported problem is indeed a bug and its criticality. After the colon is the kind of the check message, here a potential read of an uninitialized variable. They should be located in your code at the point where the error can occur, and the corresponding line in GPS editor should be highlighted in red.

Flow analysis can issue several kinds of check messages. In this document, we concentrate on the two most common ones. Initialization checks are about uses of uninitialized data. They are described in section “Initialization Checks”. Section “Aliasing” dwells on check messages relative to aliasing of subprogram parameters and global variables. Other specific check messages can also be issued when volatile variables or tasking constructs are used. More information about these additional checks can be found in
http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_view_gnatprove_output.html#description-of-messages.

Once every check message has been addressed, flow analysis can be run again with the box “Report checks proved” checked to see the verifications successfully performed by GNATprove. It should only issue “info” messages, highlighted in green in GPS, like the following::

  info: initialization of "V" proved

Flow analysis can also generate useful warnings about dead code, unused variables or wrong parameter mode. As part of this level, it may be interesting to look at these warnings. We explain how this can be done in section “Flow Analysis Warnings”.

As a further optional steps in this level, critical parts of the program can be annotated to make sure they do not make unintended accesses to global data. This activity is explained in “Global Annotations”.

Initialization Checks
---------------------

Initialization checks are the most common check messages issued by GNATprove in flow analysis mode. Indeed, every time a variable is read or returned by a subprogram, GNATprove performs a check to make sure it has been initialized. A failed initialization check message can have one of the two forms::

  high: "V" is not initialized

or::

  medium: "V" might not be initialized

Choose a unit in which GNATprove reports an unproved initialization check and open it in GPS. Flow analysis can be launched on this unit only by selecting menu SPARK → Examine File, select the “flow” mode in the GPS panel, check the box “Do not report warnings”, uncheck the box “Report checks proved”, and click on “Execute”. To investigate an unproved initialization check, click on the corresponding check message in the “Locations” tab. The editor should move to the corresponding location in your program.


Not all unproved initialization checks are actual reads of uninitialized variables as SPARK features a stronger initialization policy than Ada and the verification of initialization of variables in GNATprove suffers from shortcomings. Determining whether an initialization check issued by GNATprove is a real error or not is done by code review and is usually straightforward. While actual reads of uninitialized data must be corrected, illegitimate check messages (called “false alarms”) can be either justified, that is, annotated with a proper justification (see section 4.2.6), or worked around. In the rest of this section, we review the most common cases where GNATprove may emit unproved initialization checks. We then describe how the code can be changed to avoid false alarms and explain how they can be justified.

SPARK Strong Data Initialization Policy
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

GNATprove verifies data initialization modularly on a per subprogram basis. To allow this verification, the SPARK language requires stronger data initialization policy than standard Ada:
Every global variable that is read by a subprogram and every parameter of mode in or in out should be initialized on entry to the subprogram.

.. code-block:: ada

   procedure P (X : in out Integer) is
   begin
       X := X + 1;  <<<   ok
   end P;
   X : Integer;
   P (X);   <<<  high: "X" is not initialized


Parameters of mode out are considered to always be uninitialized on subprogram entry so their value should not be read prior to initialization.

.. code-block:: ada

   procedure P (X : out Integer) is
   begin
       X := X + 1;  <<<   high: "X" is not initialized
   end P;
   X : Integer;
   P (X);   <<<  ok


The returned expression of a function and the parameters of mode out of a procedure should be initialized on the subprogram return.

.. code-block:: ada

   procedure P (X : out Integer) is
               <<<   high: "X" is not initialized in P
   begin
       null;
   end P;


If a global variable is completely initialized by a subprogram, it is considered as an output of the subprogram and SPARK does not require it to be initialized at subprogram entry.

.. code-block:: ada

   G : Integer;
   procedure P is   <<<   info: initialization of "G" proved
   begin
       G := 0;
   end P;


More information about SPARK’s data initialization policy can be found in the SPARK User’s Guide: http://docs.adacore.com/spark2014-docs/html/ug/source/language_restrictions.html#data-initialization-policy.


This initialization policy may be too constraining in some cases. For example, consider the following “Search” procedure:

.. code-block:: ada

   procedure Search (A      : Nat_Array;
                     E      : Natural;
                     Found  : out Boolean;
                     Result : out Positive)
   is
   begin
      for I in A'Range loop
         if A (I) = E then
            Found := True;
            Result := I;
            return;
         end if;
      end loop;
      Found := False;
   end Search;


It is perfectly safe as long as the value of “Result” is only read when “Found” is True. Still, flow analysis issues an unproved check on check’s declaration::

  medium: "Result" might not be initialized in "Search"


This check message can be considered as a false alarm and can be easily justified (see section 4.2.6) or worked around, depending on what is more appropriate. A safer alternative however is to always initialize Result on all paths through Search.

Handling of Composite Objects as a Whole
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

From SPARK initialization policy, it follows that out parameters of a composite type must be completely defined by the subprogram. In particular, it makes it impossible to fully initialize a record object by successively initializing each component through procedure calls:

.. code-block:: ada

   type R is record
      F1 : Integer;
      F2 : Integer;
   end record;

   procedure Init_F1 (X : out R) is
                <<< high: "X.F2" is not initialized in "Init_F1"
   begin
      X.F1 := 0;
   end Init_F1;

   procedure Init_F2 (X : in out R) is
   begin
      X.F2 := 0;
   end Init_F2;

   X : R;
   Init_F1 (X);
   Init_F2 (X);

Imprecise Handling of Arrays
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Though record objects are treated as a whole for inter-procedural data initialization policy, the initialization status of each record component is tracked independently inside a single subprogram. For example, a record can be initialized by successive assignments into each of its components:

.. code-block:: ada

   X : R;
   X.F1 := 0;
   X.F2 := 0;
   P (X);   <<<  info: initialization of "Y.F1" proved
            <<<  info: initialization of "Y.F2" proved


The same is not true about arrays as checking that each index of an array has been initialized requires in general dynamic evaluation of expressions (to compute which indexes have been assigned to). As a consequence, GNATprove will consider an update of an array variable as a read of this variable and issue an unproved initialization check every time an assignment is done into a potentially uninitialized array. It will then assume that the whole array has been initialized for the rest of the analysis. In particular, initializing an array element by element will result in an unproved initialization check:

.. code-block:: ada

   A : Nat_Array (1 .. 3);
   A (1) := 1;   <<<  medium: "A" might not be initialized
   A (2) := 2;   <<<  info: initialization of "A" proved

Value Dependency
^^^^^^^^^^^^^^^^

Flow analysis is not value dependent, meaning that it is not influenced by the actual value of expressions. As a consequence, it is not able to determine that some paths of a program are infeasible and may issue unproved checks on such a path. For example, in the following program, GNATprove cannot make sure that “X1” is initialized in the assignment to “X2” even though the two if statements share the same condition:

.. code-block:: ada

   X1 : Integer;
   X2 : Integer;
   if X < C then
      X1 := 0;
   end if;
   if X < C then
      X2 := X1;   <<<  medium: "X1" might not be initialized
   end if;

Rewriting the Code to Avoid False Alarms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In the cases where the code can be modified, it can be a good idea to rewrite it so that GNATprove can successfully check data initialization. They are ordered from the least intrusive to the most intrusive.
Initialize variables at declaration. This is the recommended work-around whenever possible. It only requires modifying the variable declaration and is not very error-prone. However, it is impossible for variables of a private type. It may also be difficult for complex data and inefficient for big structures.

.. code-block:: ada

   A : Nat_Array (1 .. 3) := (others => 0);
   A (1) := 1;   <<<  info: initialization of "A" proved
   A (2) := 2;   <<<  info: initialization of "A" proved


Add a default to the variable type. This is more intrusive as it will impact every variable of this type that is initialized by default. For example, if the initializing expression takes some time to execute, and there are thousands of variables of this type which are default initialized, this may impact the overall running time of the application. It is especially interesting for private types, for which the previous work-around is not applicable. A default initial value can be defined for scalar types using Default_Value, for array types using Default_Component_Value, and for record types by introducing a default for each record component.

.. code-block:: ada

   type My_Int is new Integer with Default_Value => 0;
   type Nat_Array is array (Positive range <>) of Natural with
     Default_Component_Value => 0;
   type R is record
     F1 : Integer := 0;
     F2 : My_Int;
   end record;

Private types can also be annotated using the Default_Initial_Condition aspect. It allows to define a property which should hold whenever a variable of this type is default initialized. When no property is provided, it defaults to True and simply implies that the type can be safely default initialized. If the full view of the type is in SPARK, a single initialization check will be issued for such a type at the type’s declaration.

.. code-block:: ada

   type Stack is private with Default_Initial_Condition;
   type Stack is record
      Size    : Natural := 0;
      Content : Nat_Array (1 .. Max);
   end record;
       <<<   medium: type "Stack" is not fully initialized

   S : Stack;
   P (S);    <<<   info: initialization of "S.Size" proved
             <<<   info: initialization of "S.Content" proved


Refactor code to respect SPARK data initialization policy. In particular, initialize every components of a record object in a single procedure and always initialize subprogram outputs. Alternatively, partial initialization (only on some program paths) can be represented by a variant record.


.. code-block:: ada

   type Optional_Result (Found : Boolean) is record
      case Found is
         when False => null;
         when True  => Content : Positive;
      end case;
   end record;

   procedure Search (A      : Nat_Array;
                     E      : Natural;
                     Result : out Optional_Result)
   is
   begin
      for I in A'Range loop
         if A (I) = E then
            Result := (Found => True, Content => I);
            return;
         end if;
      end loop;
      Result := (Found => False);
   end Search;


Justifying Unproved Check Messages
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Check messages, like those emitted for data initialization, can be selectively accepted by users by supplying an appropriate justification. The tool will silently assume that the data concerned by the justified check has been initialized and will not warn again about its uses. To annotate a check, a pragma Annotate should be added in the source code on the line following the failed initialization check:

.. code-block:: ada

   pragma Annotate (GNATprove, Category, Pattern, Reason);


A pragma Annotate expects exactly 4 arguments. The first one is fixed and should always be GNATprove. The second argument, named Category, can be either False_Positive or Intentional. False_Positive should be used when the data is initialized by the program though GNATprove is unable to verify it, whereas Intentional should be used when the variable is not initialized, but for some reason this is not a problem; some examples will be given later. The third argument, named Pattern, should be a part of the check message. For initialization checks, ““X” might not be initialized” or “”X” is not initialized” depending on the message is appropriate. Finally, the last argument is the most important. It stores an explanation of why the check was accepted. It should allow to review the justification easily. A common rule applied in practice is that the reason should also identify the author of the justification, using the format “<initials> <reason>”, for example “YM variable cannot be zero here”.


A complete description of how checks can be justified can be found in the SPARK User’s Guide:
http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_use_gnatprove_in_a_team.html#justifying-check-messages.


On the code below, GNATprove is unable to verify that the array A is initialized by successive initialization of its elements:

.. code-block:: ada

   A : Nat_Array (1 .. 3);
   A (1) := 1;
   pragma Annotate
     (GNATprove, False_Positive, """A""might not be initialized",
      String'("A is properly initialized by these three successive"
        & " assignments"));
   A (2) := 2;
   A (3) := 3;


Since the array A is correctly initialized by the code above, the annotation falls in the category False_Positive. Note that the pragma Annotate must be located just after the line for which the check message is issued.


In particular because SPARK requires a stronger initialization policy than Ada, a user may want to justify a check message for a variable that may not be entirely initialized. In this case, the user should be especially careful to precisely state the reasons for the check message to be acceptable as the code may change later and SPARK would not spot any invalid usage of the annotated variable. For example, when we accept the check message stating that Result may not be initialized by Search, we must explain precisely what is required both from the implementation and from the callers to make the review valid:


.. code-block:: ada

   procedure Search (A      : Nat_Array;
                     E      : Natural;
                     Found  : out Boolean;
                     Result : out Positive);
   pragma Annotate
     (GNATprove, Intentional, """Result"" might not be initialized",
      String'("Result is always initialized when Found is True and never"
        & " read otherwise");


As another example, we can assume every instance of a stack is initialized by default only under some assumptions that should be recorded in the justification message:

.. code-block:: ada

   type Stack is private with Default_Initial_Condition;
   type Stack is record
      Size    : Natural := 0;
      Content : Nat_Array (1 .. Max);
   end record;
   pragma Annotate
     (GNATprove, Intentional, """Stack"" is not fully initialized",
      String'("The only indexes that can be accessed in a stack are"
        & " those smaller than Size. These indexes will always have been"
        & " initialized when Size is increased."));


On existing, thoroughly tested code, unconditional reads of uninitialized data are rather unlikely. Still, it can be the case that there is a path through the program where an uninitialized variable can be read. Before justifying an unproved initialization check, it is important to understand why it is not discharged and what are the assumptions conveyed to the tool when justifying it. The result of this analysis should then be stored inside the reason field of the Annotate pragma to ease later reviews.

Aliasing
--------

Detecting Possible Aliasing
^^^^^^^^^^^^^^^^^^^^^^^^^^^

In SPARK, an assignment to a variable cannot change the value of another variable. This is enforced by forbidding the use of access types (pointers) in SPARK, and by restricting aliasing between parameters and global variables so that only benign aliasing is accepted (i.e. aliasing that does not cause interference).


A check message concerning a possible aliasing has the form::

  high: formal parameter "X" and global "Y" are aliased (SPARK RM 6.4.2)


It warns that, for the call at the location of the check message, the variable Y supplied for the formal parameter X of the subprogram was already visible in the subprogram. As a result, assignments to Y in the subprogram will affect the value of X and the converse holds too. This is detected as an error by GNATprove which always assumes variables to be distinct.

As stated in the check message, the precise rules for aliasing are detailed in SPARK Reference Manual section 6.4.2. They can be summarized as follows:


Two output parameters should never be aliased. Notice that the trivial cases of parameter aliasing are already forbidden by Ada and reported as errors by the compiler, like in the following subprogram:

.. code-block:: ada

   procedure Swap (X, Y : in out Integer);

   Swap (Z, Z);
           <<< writable actual for "X" overlaps with actual for "Y"


An input and an output parameter should not be aliased.

.. code-block:: ada

   procedure Move_X_To_Y (X : in T; Y : out T);

   Move_X_To_Y (Z, Z);
      <<< high: formal parameters "X" and "Y" are aliased (SPARK RM 6.4.2)


As an exception, SPARK allows aliasing between an input and an output parameter if the input parameter is always passed by copy. For example, if we change T to Integer in the previous example so that the arguments are always passed by copy, GNATprove does not output any unproved check message anymore:

.. code-block:: ada

   procedure Move_X_To_Y (X : in Integer; Y : out Integer);

   Move_X_To_Y (Z, Z); <<< ok


An output parameter should never be aliased with a global variable referenced by the subprogram. This case is really the same as aliasing between output parameters but cannot be reported by the compiler because it does not track uses of global variables.

.. code-block:: ada

   procedure Swap_With_Y (X : in out Integer);

   Swap_With_Y (Y);
      <<< high: formal parameter "X" and global "Y" are aliased (SPARK RM 6.4.2)


Note that aliasing between an output parameter and a global variable is also forbidden if the global variable is never written:

.. code-block:: ada

   procedure Move_X_To_Y (Y : out Integer);

   Move_X_To_Y (X);
      <<< high: formal parameter "Y" and global "X" are aliased (SPARK RM 6.4.2)


An input parameter should not be aliased with a global variable referenced by the subprogram.

.. code-block:: ada

   procedure Move_X_To_Y (X : in T);

   Move_X_To_Y (Y);
      <<< high: formal parameter "X" and global "Y" are aliased (SPARK RM 6.4.2)


Like for aliasing between parameters, aliasing is allowed if the input parameter is always passed by copy:

.. code-block:: ada

   procedure Move_X_To_Y (X : in Integer);

   Move_X_To_Y (Y); <<< ok


Note that aliasing can also occur between parts of composite variables such as components of records or elements of arrays. More information about aliasing can be found in the SPARK User’s  Guide:
http://docs.adacore.com/spark2014-docs/html/ug/source/language_restrictions.html#absence-of-interferences.

Dealing with Unproved Aliasing Checks
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Complying with SPARK rules concerning aliasing usually requires refactoring the code. This is in general a good idea because aliasing can be the source of errors that are difficult to notice as they only occur in some cases. When calling a subprogram with aliased parameters there is a good chance of falling in a case the implementer of the subprogram has not considered and thus of triggering an inappropriate reaction. Furthermore, the behavior of a subprogram call when its parameter are aliased depends on how parameter are passed (by copy or by reference) and on the order in which the by-copy parameters are copied back if any. As these are not specified by the Ada language, it may introduce either compiler or platform dependences in the program behavior.


It can be the case that GNATprove analysis is not precise enough and that it raises an unproved check message in cases in which there really are no possible aliasing. It can be the case for example for aliasing between a subprogram input parameter and an output global variable referenced by the subprogram if the parameter is not of a by-copy type (a type mandated to be passed by value by the Ada Reference Manual) but for which the developer knows that, in her setup, the compiler indeed passes it by copy. In this case, the check message can be justified as described for Initialization checks:

.. code-block:: ada

   type T is record
      F : Integer;
   end record with
      Convention => C_Pass_By_Copy;

   procedure Move_X_To_Y (X : in T);

   Move_X_To_Y (Y);
   pragma Annotate
     (GNATprove, False_Positive,
      "formal parameter ""X"" and global ""Y"" are aliased",
      String'("My compiler follows Ada RM-B-3 68 implementation advice"
       & " and passes variables of type T by copy as it uses the"
       & " C_Pass_By_Copy convention"));


GNATprove restrictions explained in the section about initialization checks can also lead to false alarms, in particular for aliasing between parts of composite objects. In the following example, Only_Read_F2_Of_X only references the component F2 in X. But, as GNATprove handles composite global variables as a whole, it still emits an unproved aliasing check in this case:

.. code-block:: ada

   procedure Only_Read_F2_Of_X (Y : out Integer);

   Only_Read_F2_Of_X (X.F1);
   pragma Annotate
     (GNATprove, False_Positive,
      "formal parameter ""Y"" and global ""X"" are aliased",
      String'("Only_Read_F2_Of_X only references the component F2 in X"
        & " so no aliasing can be introduced with X.F1"));


In the same way, because it is not value dependent, flow analysis emits an unproved aliasing check when two (distinct) indices of an array are given as output parameters to a subprogram:

.. code-block:: ada

   pragma Assert (I = 2);
   Swap (A (1), A (I));
   pragma Annotate
     (GNATprove, False_Positive,
      "formal parameters ""X"" and ""Y"" might be aliased",
      String'("As I is equal to 2 prior to the call, A (1) and A (I) are"
        & " never aliased."));

Flow Analysis Warnings
----------------------

Apart from check messages, flow analysis can also issue warnings. They usually flag suspicious code which may be the sign of an error in the program. They should be inspected but can be suppressed when they are deemed spurious, without risk of missing a critical issue for the soundness of the analysis. To see these warnings, run the tool in flow analysis mode with warnings enabled. Select menu SPARK → Examine All, in the GPS panel, select the “flow” mode, uncheck the boxes “Do not report warnings” and “Report checks proved”, and click on “Execute”.


GNATprove warnings, just like regular compiler warnings, are associated with a source location and are prefixed with the word “warning”::

  warning: subprogram "Test" has no effect


GNATprove warnings can be suppressed globally by using the switch --warnings=off (or by checking the box “Do not report warnings” in GPS) or specifically using pragma Warnings. For example, the above warning can be suppressed by switching off specifically warnings with the above message around the declaration of the procedure Test as follows

.. code-block:: ada

   pragma Warnings
     (Off, "subprogram ""Test"" has no effect",
      Reason => "Written to demonstrate GNATprove's capabilities");

   procedure Test;

   pragma Warnings (On, "subprogram ""Test"" has no effect");


A common rule applied in practice is that the reason should also identify the author of the suppression, using the format “<initials> <reason>”, for example “CD subprogram is only a test”.


How warnings can be suppressed in GNATprove is described in the SPARK User’s Guide:
http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_use_gnatprove_in_a_team.html#suppressing-warnings.


The rest of this section lists warnings that may be emitted by GNATprove and explains their meaning.

.. rubric:: initialization of X has no effect

Flow analysis tracks flow of information between variables. While doing so, it can detect cases where the initial value of a variable is never used to compute the value of any object. It reports it with a warning.

.. code-block:: ada

   function Init_Result_Twice return Integer is
      Result : Integer := 0;
           <<<   warning initialization of Result has no effect
   begin
      Result := 1;
      return Result;
   end Init_Result_Twice;


.. rubric:: unused assignment

Flow analysis also detects assignments which store into a variable a value that will never be read afterward.

.. code-block:: ada

   procedure Write_X_Twice (X : out Integer) is
   begin
      X := 1; <<<  warning: unused assignment
      X := 2;
   end Write_X_Twice;


Note that flow analysis is not value dependent. As a consequence, it cannot detect cases when an assignment is useless because it stores the same value that was previously stored in the variable.

.. code-block:: ada

   procedure Write_X_To_Same (X : in out Integer) is
      Y : Integer;
   begin
      Y := X;
      X := Y;  <<<  no warning
   end Write_X_To_Same;

.. rubric:: “X” is not modified, could be IN

Flow analysis also checks the modes of subprogram parameters. It warns on in out parameters whose value is never modified.

.. code-block:: ada

   procedure Do_Not_Modify_X (X, Y : in out Integer) is
       <<<  warning: "X" is not modified, could be IN
   begin
      Y := Y + X;
   end Do_Not_Modify_X;

.. rubric:: unused initial value of “X”

Flow analysis also detects in and in out parameters whose initial value is never read in the program.

.. code-block:: ada

   procedure Initialize_X (X : in out Integer) is
       <<<  warning: unused initial value of "X"
   begin
      X := 1;
   end Initialize_X;

.. rubric:: statement has no effect

Flow analysis can detect a statement which has no effect on any output of the subprogram.

.. code-block:: ada

   procedure Initialize_X (X : out Integer) is
      Y : Integer;
   begin
      Set_To_One (Y);  <<<<  statement has no effect
      X := 1;
   end Initialize_X;

.. rubric:: subprogram “S” has no effect

When a subprogram as a whole has no output, it is also reported by GNATprove.

.. code-block:: ada

   procedure Do_Nothing is
      <<<  warning: subprogram "Do_Nothing" has no effect
   begin
      null;
   end Do_Nothing;

Global Annotations
------------------

Global Contract
^^^^^^^^^^^^^^^

In addition to what has been presented so far, a user may want to use flow analysis to verify specific data dependency relations. It can be done by providing the tool with additional Global contracts stating the set of global variables accessed by a subprogram. The user needs only to supply those contracts that she wants to verify. Other contracts will be automatically inferred by the tool. The simplest form of data dependency contract states that a subprogram is not allowed to either read or modify global variables

.. code-block:: ada

   procedure Increment (X : in out Integer) with
      Global => null;

This construction uses the Ada 2012 aspect syntax. It must be placed on the subprogram declaration if any, and on the subprogram body otherwise. An alternative notation can be used based on pragmas if compatibility with older versions of Ada is an issue:

.. code-block:: ada

   procedure Increment (X : in out Integer);
   pragma Global (null);

This annotation is in general the most common one as most subprograms do not use global state. In its more complete form, the Global contract allows to specify exactly the set of variables that are read, updated, and initialized by the subprogram

.. code-block:: ada

   procedure P with
      Global =>
         (Input  => (X1, X2, X3),
        --  variables read but not written by P (same as in parameters)
          In_Out => (Y1, Y2, Y3),
        --  variables read and written by P (same as in out parameters)
          Output => (Z1, Z2, Z3));
        --  variables initialized by P (same as out parameters)

No Global contracts are mandatory. However, whenever a contract is provided, it must be correct and complete, that is, it must mention every global variable accessed by the subprogram with the correct mode. Like for subprogram parameter modes, global contracts are checked by the tool in flow analysis mode and checks and warnings are emitted in case of non-conformance. To verify manually supplied global contracts, run GNATprove in flow analysis mode by selecting menu SPARK → Examine File, select the “flow” mode in the GPS panel, check the box “Do not report warnings”, uncheck the box “Report checks proved”, and click on “Execute”.

Global contracts are described more precisely in the SPARK User’s Guide:
http://docs.adacore.com/spark2014-docs/html/ug/source/subprogram_contracts.html#data-dependencies.

Constants with Variable Inputs
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When a subprogram accesses a constant whose value depends on variable inputs (that is, on the value of variables or of other constants with variable inputs), it must be listed in the Global contract of the subprogram if any. This may come as a surprise to users. However, this is required to properly verify every flow of information between variables of the program. As an example, on the following program, the dependency of Set_X_To_C on the value of Y is expressed by the constant with variable inputs C appearing in its Global contract

.. code-block:: ada

   Y : Integer := 0;
   procedure Set_X_To_Y (X : out Integer) with
      Global => (Input => Y) <<< Y is an input of Set_X_To_Y
   is
      C : constant Integer := Y;
      procedure Set_X_To_C with
         Global => (Input => C, Output => X)
         <<< the dependency on Y is visible through the dependency on C
      is
      begin
         X := C;
      end Set_X_To_C;
   begin
      Set_X_To_C;
   end Set_X_To_Y;

More information about constants with variable inputs can be found in the SPARK User’s Guide:
http://docs.adacore.com/spark2014-docs/html/ug/source/package_contracts.html#special-cases-of-state-abstraction.

Abstract State
^^^^^^^^^^^^^^

It can be the case that a user wants to annotate a subprogram that accesses a variable that is not visible from the subprogram declaration, because it is declared inside some package private part or body. In such a case, a name must be given to the variable through an abstract state declaration. This name can then be used to refer to the variable from within Global contracts (but not from within regular code or assertions). More precisely, an abstract state can be declared for the hidden state of a package using an Abstract_State aspect (or the equivalent pragma).

.. code-block:: ada

   package P with
      Abstract_State => State
   is
      V : Integer;  --  V is visible in P so cannot be part of State

      procedure Update_All with
        Global => (Output => (V, State));
      --  The Global contract mentions V explicitly but uses State to
      --  refer to H and B.

   private
      H : Integer with  --  H is hidden in P, it must be part of State
        Part_Of => State;
   end P;

   package body P with
      Refined_State => (State => (H, B))
   is
      B : Integer; --  B is hidden in P, it must be part of State

      procedure Update_All is
      begin
         V := 0;
         H := 0;
         B := 0;
      end Update_All;
   end P;

An Abstract_State annotation is not mandatory though it may be necessary to annotate some subprograms with Global contracts. However, when it is provided, it must be correct and complete, that is, it must list exactly all the hidden variable declared in the package. Several abstract states can be defined for the same package to allow more precise Global contracts on subprograms accessing only parts of the package hidden variables

.. code-block:: ada

   package P with
      Abstract_State => (State1, State2)
   is
      procedure Update_Only_H with
        Global => (Output => (State1));
      --  If only one abstract state was defined for B and H, the Global
      --  contract would be less precise.

   private
      H : Integer with
        Part_Of => State1;
   end P;

   package body P with
      Refined_State => (State1 => H, State2 => B)
   is
      B : Integer := 0;

      procedure Update_Only_H is
      begin
         H := 0;
      end Update_Only_H;
   end P;


When an abstract state is supplied, it must be refined into its constituents in the package body using the Refined_State aspect or pragma. Furthermore, to be able to analyze the package specification independently, every private variable must be linked to an abstract state using the Part_Of aspect. More information about state abstraction can be found in the SPARK User’s Guide: http://docs.adacore.com/spark2014-docs/html/ug/source/package_contracts.html#state-abstraction.

.. _Silver Level:

Silver Level - Absence of Run-time Errors (AoRTE)
=================================================

The goal of this level is to ensure that the program does not raise an exception at run time. This ensures in particular that the control flow of the program cannot be circumvented by exploiting a buffer overflow, possibly as a consequence of an integer overflow. This also ensures that the program cannot crash or behave erratically when compiled without support for run-time exceptions (compiler switch -gnatp), after an operation that would have triggered a run-time exception.


GNATprove can be used to prove the complete absence of possible run-time errors corresponding to:
all possible explicit raising of exceptions in the program,
raising exception Constraint_Error at run time, and
all possible failures of assertions corresponding to raising exception Assert_Error at run time.


A special kind of run-time errors that can be proved at this level is the absence of exceptions from defensive code. This requires users to add subprogram preconditions (see section 6.2 for details) that correspond to the conditions checked in defensive code. For example, defensive code that checks the range of inputs will translate into preconditions of the form “Input_X in Low_Bound .. High_Bound”. These conditions are then checked by GNATprove at each call.

.. rubric:: Benefits

The SPARK code is guaranteed to be free from run-time errors, plus all the defects already detected at bronze level: no reads of uninitialized variables, no possible interference between parameters and/or global variables, no unintended access to global variables. Thus, the quality of the program can be guaranteed to achieve higher levels of integrity than would be possible in another programming language.


All the messages about possible run-time errors can be carefully reviewed and justified (for example by relying on external system constraints such as the maximal time between resets), and these justifications can be later reviewed as part of the quality inspections.


The proof of AoRTE can be used to compile the final executable without run-time exceptions (compiler switch -gnatp), which allows to have a very efficient code comparable to what can be achieved in C or assembly.


The proof of AoRTE can be used to comply with the objectives of certification standards in various domains (DO-178 in avionics, EN 50128 in railway, IEC 61508 in all kind of safety related industry, ECSS-Q-ST-80C in space, IEC 60880 in nuclear, IEC 62304 in medical, ISO 26262 in automotive). To date, the use of SPARK has been qualified in EN 50128 context. Qualification material for DO-178 context should be available in 2018. Qualification material in any context can be developed by AdaCore as part of a contract.

.. rubric:: Impact on Process

An initial pass will be required where proof of AoRTE is applied to the program and the resulting messages are resolved by either rewriting code or justifying any false alarms. Once this is complete, evolutive maintenance can maintain the same guarantees at reasonable cost from developers. Using precise types and simple subprogram contracts (preconditions and postconditions) is sufficient to avoid most false alarms, and any remaining false alarms can be justified simply.


Special treatment is required for loops, which may need the addition of loop invariants to prove AoRTE inside and after the loop. The detailed process for doing so is described in the SPARK User’s Guide, as well as the common patterns of loops and their corresponding loop invariants.

.. rubric:: Costs and Limitations

The initial pass may require a substantial effort to get rid of all false alarms, depending on the coding style adopted so far. The analysis may take a long time (up to a few hours) on large programs (but it is guaranteed to terminate). Proof is, by construction, limited to local understanding of the code, which requires using sufficiently precise types of variables, and some preconditions and postconditions on subprograms to communicate relevant properties to their callers.


Even if a property is provable, automatic provers may fail to prove it, due to limitations of the heuristic techniques used in automatic provers. In practice, these limitations are mostly visible on non-linear integer arithmetic (such as division and modulo) and floating-point arithmetic.

Running GNATprove in Proof Mode
-------------------------------

Proof is the second static analysis performed by GNATprove, after flow analysis seen at bronze level. Contrary to flow analysis, proof may take more or less time to run, depending on the selected proof level. The higher the proof level, the more precise the results, and the longer the analysis.


Launch GNATprove in proof mode on your project by selecting menu SPARK → Prove All. In the GPS panel, select “0” as value for “Proof level”, check the box “Multiprocessing”, uncheck the box “Report checks proved”, and click on “Execute”. The following snapshot shows the popup window from GPS with these settings:

.. image:: _static/prove.png
   :align: center
   :alt: Popup window from GPS for "prove" mode




GNATprove should output the following messages, potentially followed by a number of messages pointing to potential problems in your program::

  Phase 1 of 2: generation of Global contracts …
  Phase 2 of 2: flow analysis and proof ..

The following messages output by GNATprove are check messages and should have the form::

  medium: overflow check might fail

First comes the severity of the check. It is one of low/medium/high and reflects both the likelihood of the reported problem indeed being a bug and its criticality. After the colon is the kind of the check message, here a potential arithmetic overflow. They should be located in your code at the point where the error can occur, and the corresponding line in GPS editor should be highlighted in red.

Proof can issue several kinds of check messages. In this document, we concentrate on the five most common ones: division by zero, array index, arithmetic overflow, value in range and correct discriminant. They are described in section “Run-time Checks”. Other specific check messages can also be issued when tagged types or tasking constructs are used. More information about these additional checks can be found in http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_view_gnatprove_output.html#description-of-messages.

Proving absence of run-time errors (AoRTE) requires interacting with GNATprove inside GPS, to either fix the code, add annotations, and finally succeed in proving the check or else justify the innocuity of the message. This process is explained in section “Investigating Unproved Run-time Checks”.


Once every unproved check message has been addressed, proof can be run again with the box “Report checks proved” checked to see the verifications successfully performed by GNATprove. It should only issue “info” messages, highlighted in green in GPS, like the following:

::
  info: overflow check proved


Run-time Checks
---------------

.. rubric:: divide by zero

This checks that the second operand of the division, mod or rem operation is different from zero. It is applicable to all integer and real types for division and to all integer types for mod and rem. Here is an example of such checks:

.. code-block:: ada

   type Oper is (D, M, R);
   type Unsigned is mod 2**32;
   Small : constant := 1.0 / 2.0**7;
   type Fixed is delta Small range -1.0 .. 1.0 - Small
     with Size => 8;

   procedure Oper_Integer (Op : Oper; X, Y : Integer; U : out Integer) is
   begin
      case Op is
         when D => U := X / Y;    <<<< medium: divide by zero might fail
         when M => U := X mod Y;  <<<< medium: divide by zero might fail
         when R => U := X rem Y;  <<<< medium: divide by zero might fail
      end case;
   end Oper_Integer;

   procedure Oper_Unsigned (Op : Oper; X, Y : Unsigned; U : out Unsigned) is
   begin
      case Op is
         when D => U := X / Y;    <<<< medium: divide by zero might fail
         when M => U := X mod Y;  <<<< medium: divide by zero might fail
         when R => U := X rem Y;  <<<< medium: divide by zero might fail
      end case;
   end Oper_Unsigned;

   procedure Div_Float (X, Y : Float; U : out Float) is
   begin
      U := X / Y;  <<<< medium: divide by zero might fail
   end Div_Float;

   procedure Div_Fixed (X, Y : Fixed; U : out Fixed) is
   begin
      U := X / Y;  <<<< medium: divide by zero might fail
   end Div_Fixed;


A special case of possible division by zero is the exponentiation of a float value of 0.0 by a negative exponent, as the result of this operation is defined as the inverse of the exponentiation of its argument (hence 0.0) by the absolute value of the exponent. Here is an example of such checks:

.. code-block:: ada

   procedure Exp_Float (X : Float; Y : Integer; U : out Float) is
   begin
      U := X ** Y;  <<<< medium: divide by zero might fail
   end Exp_Float;


.. rubric:: index check

This checks that a given index used to access inside an array is within the bounds of the array. This applies to both reads and writes to an array. Here is an example of such checks:

.. code-block:: ada

   function Get (S : String; J : Positive) return Character is
   begin
      return S(J);  <<<< medium: array index check might fail
   end Get;

   procedure Set (S : in out String; J : Positive; C : Character) is
   begin
      S(J) := C;  <<<< medium: array index check might fail
   end Set;


.. rubric:: overflow check

This checks that the result of a given arithmetic operation is within the bounds of its base type, which corresponds to the bounds of the underlying machine type. It is applicable to all signed integer types (but not modular integer types) and real types, and most arithmetic operations (unary negation, absolute value, addition, subtraction, multiplication, division, exponential). Here is an example of such checks:

.. code-block:: ada

   type Oper is (Minus, AbsVal, Add, Sub, Mult, Div, Exp);
   type Unsigned is mod 2**32;
   Small : constant := 1.0 / 2.0**7;
   type Fixed is delta Small range -1.0 .. 1.0 - Small
     with Size => 8;

   procedure Oper_Integer (Op : Oper; X, Y : Integer; E : Natural; U : out Integer) is
   begin
      case Op is
         when Minus  => U := -X;  <<<< medium: overflow check might fail
         when AbsVal => U := abs X;  <<<< medium: overflow check might fail
         when Add    => U := X + Y;  <<<< medium: overflow check might fail
         when Sub    => U := X - Y;  <<<< medium: overflow check might fail
         when Mult   => U := X * Y;  <<<< medium: overflow check might fail
         when Div    => U := X / Y;  <<<< medium: overflow check might fail
         when Exp    => U := X ** E;  <<<< medium: overflow check might fail
      end case;
   end Oper_Integer;

   procedure Oper_Float (Op : Oper; X, Y : Float; E : Natural; U : out Float) is
   begin
      case Op is
         when Minus  => U := -X;
         when AbsVal => U := abs X;
         when Add    => U := X + Y;  <<<< medium: overflow check might fail
         when Sub    => U := X - Y;  <<<< medium: overflow check might fail
         when Mult   => U := X * Y;  <<<< medium: overflow check might fail
         when Div    => U := X / Y;  <<<< medium: overflow check might fail
         when Exp    => U := X ** E;  <<<< medium: overflow check might fail
      end case;
   end Oper_Float;

   procedure Oper_Fixed (Op : Oper; X, Y : Fixed; E : Natural; U : out Fixed) is
   begin
      case Op is
         when Minus  => U := -X;  <<<< medium: overflow check might fail
         when AbsVal => U := abs X;  <<<< medium: overflow check might fail
         when Add    => U := X + Y;  <<<< medium: overflow check might fail
         when Sub    => U := X - Y;  <<<< medium: overflow check might fail
         when Mult   => U := X * Y;  <<<< medium: overflow check might fail
         when Div    => U := X / Y;  <<<< medium: overflow check might fail
         when Exp    => null;
      end case;
   end Oper_Fixed;


Note that there is no overflow check when negating a floating-point value or taking its absolute value, as floating-point base types (32 bits or 64 bits) are symmetric. On the contrary, negating a signed integer or taking its absolute value may result in an overflow, if the argument value is the minimal machine integer for this type, because signed machine integers are not symmetric (they have one less positive value compared to negative values). As fixed-point types are based in an machine integer representation, they can also lead to overflows on negation and absolute value.


.. rubric:: range check

This checks that a given value is within the bounds of its expected scalar subtype. It is applicable to all scalar types, including signed and modulo integers, enumerations and real types. Here is an example of such checks:

.. code-block:: ada

   type Enum is (A, B, C, D, E);
   subtype BCD is Enum range B .. D;

   type Unsigned is mod 2**32;
   subtype Small_Unsigned is Unsigned range 0 .. 10;

   Small : constant := 1.0 / 2.0**7;
   type Fixed is delta Small range -1.0 .. 1.0 - Small
     with Size => 8;
   subtype Natural_Fixed is Fixed range 0.0 .. Fixed'Last;

   subtype Natural_Float is Float range 0.0 .. Float'Last;

   procedure Convert_Enum (X : Enum; U : out BCD) is
   begin
      U := X;  <<<< medium: range check might fail
   end Convert_Enum;

   procedure Convert_Integer (X : Integer; U : out Natural) is
   begin
      U := X;  <<<< medium: range check might fail
   end Convert_Integer;

   procedure Convert_Unsigned (X : Unsigned; U : out Small_Unsigned) is
   begin
      U := X;  <<<< medium: range check might fail
   end Convert_Unsigned;

   procedure Convert_Float (X : Float; U : out Natural_Float) is
   begin
      U := X;  <<<< medium: range check might fail
   end Convert_Float;

   procedure Convert_Fixed (X : Fixed; U : out Natural_Fixed) is
   begin
      U := X;  <<<< medium: range check might fail
   end Convert_Fixed;

.. rubric:: discriminant check

This checks that the discriminant of the given discriminated record has the expected value. For variant records, this can happen for a simple access to a record component. This applies to both reads and writes to a record component. Here is an example of such checks:

.. code-block:: ada

   type Rec (B : Boolean) is record
      case B is
         when True =>
            X : Integer;
         when False =>
            Y : Float;
      end case;
   end record;

   function Get_X (R : Rec) return Integer is
   begin
      return R.X;  <<<< medium: discriminant check might fail
   end Get_X;

   procedure Set_X (R : in out Rec; V : Integer) is
   begin
      R.X := V;  <<<< medium: discriminant check might fail
   end Set_X;

Investigating Unproved Run-time Checks
--------------------------------------

It is expected that many messages about possible run-time errors are issued the first time a program is analyzed, for two main reasons:
The analysis done by GNATprove relies on the information provided in the program to compute possible values of variables. This information lies chiefly in the types and contracts added by programmers. If types are not precise enough, and necessary contracts are not inserted, then GNATprove cannot prove AoRTE.
The initial analysis performed at proof level 0 is the fastest but also the least precise. It is advised to start at this level, as initially many checks are not provable due to imprecise types and missing contracts. As precise types and contracts are added in the program, it is profitable to perform analysis at higher proof levels 1 and 2 to get more precise results.


Proving AoRTE requires interacting with GNATprove inside GPS. Thus, we suggest that you select a unit (preferably one with few dependences over other unproved units, ideally a leaf unit not depending on other unproved units) with some unproved checks. Open GPS on your project, display this unit inside GPS, and put the focus on this unit. Inside this unit, select a subprogram (preferably one with few calls to other unproved subprograms, ideally a leaf subprogram not calling other unproved subprograms) with some unproved checks. This is the first subprogram you will analyze at silver level.


For each unproved run-time check in this subprogram, you should follow the following steps:

#. Understand why the run-time check cannot fail at run time. If you do not understand why a run-time check never fails, GNATprove cannot understand it either. You may discover at this stage that indeed the run-time check may fail at run time, in which case you will need to first correct the program so that it is not possible.
#. Determine if the reasons for the check to always succeed are known locally. GNATprove analysis is modular, which means that it only looks at locally available information to determine whether a check succeeds or not. This information consists mostly in the types of parameters and global variables, the precondition of the subprogram, and the postconditions of the subprogram it calls. If the information is not locally available, you should change types and/or add contracts to make it locally available to the analysis. See the paragraphs below on “More Precise Types” and “Useful Contracts”.
#. If the run-time check depends on the value of a variable being modified in a loop, you may need to add a loop invariant, i.e. a specific annotation in the form of a pragma Loop_Invariant inside the loop, that summarizes the effect of the loop on the variable value. See the specific section of the SPARK User’s Guide on that topic: http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_write_loop_invariants.html.
#. Once you are confident this check should be provable, run SPARK in proof mode on the specific line with the check by right-clicking on this line in the editor panel inside GPS, and select SPARK → Prove Line from the contextual menu. In the GPS panel, select “2” as value for “Proof level”, check the box “Report checks proved”, and click on “Execute”. GNATprove should output either a message that confirms that the check is proved, or the same message as before. In the latter case, you will need to interact with GNATprove to investigate why the check is still not proved.
#. It may be difficult sometimes to distinguish cases where some information is missing for the provers to prove the check from cases where the provers are incapable of proving the check. Multiple actions may help distinguishing those cases, as documented in a specific section of the SPARK User’s Guide on that topic (see subsections on “Investigating Unprovable Properties” and “Investigating Prover Shortcomings”): http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_investigate_unproved_checks.html. The most generally useful action to narrow down the issue to its core is to insert assertions in the code that “test” whether the check can be proved at some specific point in the program. For example, if a check message is issued about a possible division by zero on expression X/Y, and the implementation contains many branches and paths before this program point, try adding assertions that Y /= 0 in the various branches. This may point to a specific path in the program which cause the issue. This may also help provers to manage to prove both the assertion and the check. In such a case, it is good practice to retain in the code only those essential assertions that help getting automatic proof, and to remove other intermediate assertions that were inserted during interaction.
#. If the check turns out to be unprovable due to limitations in the proving technology, you will have to justify its presence so that future runs of GNATprove will not report it again, by inserting a pragma Annotate after the line where the check message is reported. See SPARK User’s Guide at http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_investigate_unproved_checks.html.


In the following, we describe how you can change types to be more precise for analysis, and how you can add contracts that will make it possible to prove AoRTE.

.. rubric:: More Precise Types

GNATprove’s analysis depends crucially on the ranges of scalar types. If the program uses standard scalar types like Integer and Float, nothing is known about the range of the data manipulated, and as a result most arithmetic operations will lead to an overflow check message. In particular, data that is used to index into arrays or as the right-hand-side of division operations (which includes mod and rem operators) should be known to be respectively in range of the array and not null, generally just by looking at their type.


When standard types like Integer and Float are used, you will need to introduce more specific types like Temperature or Length, with suitable ranges. These may be either new types like

.. code-block:: ada

   type Temperature is digits 6 range -100.0 .. 300.0;
   type Length is range 0 .. 65_535;


or derived types like

.. code-block:: ada

   type Temperature is new Float range -100.0 .. 300.0;
   type Length is new Integer range 0 .. 65_535;


or subtypes like

.. code-block:: ada

   subtype Temperature is Float range -100.0 .. 300.0;
   subtype Length is Integer range 0 .. 65_535;


When user types are used, you may either add a suitable range to these types, or introduce derived types or subtypes with suitable range as above.


.. rubric:: Useful Contracts

Besides types, it might be important to specify in which context a subprogram may be called. This is known as the precondition of the subprogram. All the examples of check messages seen in section “Run-time Checks” could be proved if suitable preconditions are added to the enclosing subprogram. For example, consider procedure Convert_Integer, which assigns from an integer X to a natural U:

.. code-block:: ada

   procedure Convert_Integer (X : Integer; U : out Natural) is
   begin
      U := X;  <<<< medium: range check might fail
   end Convert_Integer;


In order for GNATprove to prove that the conversion cannot lead to a range check failure, we need to know that X is non-negative when calling Convert_Integer, which can be expressed as a precondition as follows:

.. code-block:: ada

   procedure Convert_Integer (X : Integer; U : out Natural)
     with Pre => X >= 0
   is
   begin
      U := X;
   end Convert_Integer;


With such a precondition, the range check inside Convert_Integer is proved by GNATprove. As a result of inserting preconditions to subprograms, GNATprove will check that the corresponding conditions hold when calling these subprograms. When these conditions cannot be proved, GNATprove issues check messages that need to be handled like run-time check messages. As a result, the same precondition may be pushed to multiple levels of callers up to a point where the condition is known to hold.


When a subprogram calls another subprogram, it may also be important to specify what can be guaranteed about the result of this call. For example, consider procedure Call_Convert_Integer, which calls the previously seen procedure Convert_Integer:

.. code-block:: ada

   procedure Call_Convert_Integer (Y : in out Natural) is
      Z : Natural;
   begin
      Convert_Integer (Y, Z);
      Y := Y - Z;  <<<< medium: range check might fail
   end Call_Convert_Integer;


When GNATprove analyzes Call_Convert_Integer, the only locally available information about the value of Z after the call to Convert_Integer is its type. This is not sufficient to guarantee that the subtraction on the following line will result in a non-negative result. Hence, GNATprove issues a message about a possible range check failure on this code. In order for GNATprove to prove that the subtraction cannot lead to a range check failure, we need to know that Z is equal to Y after calling Convert_Integer, which can be expressed as a postcondition as follows:

.. code-block:: ada

   procedure Convert_Integer (X : Integer; U : out Natural)
     with Pre  => X >= 0,
           Post => X = U
   is
   begin
      U := X;
   end Convert_Integer;


With such a postcondition, the range check inside Call_Convert_Integer is proved by GNATprove. As a result of inserting postconditions to subprograms, GNATprove will check that the corresponding conditions hold when returning with these subprograms. When these conditions cannot be proved, GNATprove issues check messages that need to be handled like run-time check messages.


.. _Gold Level:

Gold Level - Proof of Key Integrity Properties
==============================================

The goal of the gold level is to ensure key integrity properties such as maintaining critical data invariants throughout execution, and ensuring that transitions between states follow a specified safety automaton. Typically, these properties derive from software requirements. Together with the silver level, these goals ensure program integrity, that is, the program keeps running within safe boundaries: the control flow of the program is correctly programmed and cannot be circumvented through run-time errors, and data cannot be corrupted.


SPARK defines a number of useful features to specify both data invariants and control flow constraints:


* Type predicates state properties that should always be true of any object of the type.
* Preconditions state properties that should always hold on subprogram entry.
* Postcondition state properties that should always hold on subprogram exit.


These features can be verified statically by running GNATprove in “prove” mode, similarly to what was done at the silver level. At every program point where a violation of the property may occur, GNATprove issues either an “info” message that the property always holds, or a “check” message about a possible violation. Of course, a benefit of proving properties is that they do not need to be tested anymore, which can be used to reduce or remove completely unit testing.


These features can also be used to augment integration testing with dynamic verification that these key integrity properties are satisfied. To enable these additional verifications during execution, one can use either compilation switch -gnata (which enables verification of all invariants and contracts at run time) or pragma Assertion_Policy (which enables a subset of the verifications) either inside the code (so that it applies to the code that follows in the current unit) or in a pragma configuration file (so that it applies to all the program).

.. rubric:: Benefits

The SPARK code is guaranteed to respect key integrity properties, as well as being free from all the defects already detected at bronze and silver levels: no reads of uninitialized variables, no possible interference between parameters and global variables, no unintended access to global variables, no run-time errors. This is a unique feature of SPARK that is not found in other programming languages. In particular, such guarantees may be used in a safety case to claim dependability of the program.


The effort in achieving that level of confidence based on proof is relatively low compared to the effort required to achieve the same based on testing. Indeed, confidence based on testing has to rely on a nearly comprehensive testing strategy. In fact, certification standards define criteria for approaching comprehensive testing, such as Modified Condition/Decision Coverage (MC/DC), which are notoriously expensive to achieve. Many certification standards allow the use of proof as a replacement for testing, in particular DO-178C in avionics, EN 50128 in railway and IEC 61508 in process and military. Proof as done in SPARK can thus be used as cost effective alternative to unit testing.

.. rubric:: Impact on Process

In a certification context where proof replaces testing, if independence is required between development and verification activities, then subprogram contracts that express software requirements should not be created  by the developers implementing such requirements. This is similar to the independence that can be required between the developer and the tester of a module. Programmers can be expected to write intermediate assertions however, and to run GNATprove to check that their implementation satisfies the requirements.


Depending on the complexity of the property to prove, it may be more or less costly to add the necessary contracts on types and subprograms, and to achieve complete automatic proof by interacting with the tool. This typically requires some experience with the tool that can be accumulated by training and practice, which suggests that not all developers should be tasked with developing such contracts and proofs, but that a few developers should be designated for this task.


As with the proof of AoRTE at silver level, special treatment is required for loops, which may need the addition of loop invariants to prove properties inside and after the loop. The detailed process for doing so is described in SPARK User’s Guide, as well as the common patterns of loops and their corresponding loop invariants.

.. rubric:: Costs and Limitations

The analysis may take a long time (up to a few hours) on large programs (but it is guaranteed to terminate). It may also take more or less time depending on the proof strategy adopted (as indicated by the switches passed to GNATprove). Proof is, by construction, limited to local understanding of the code, which requires using sufficiently precise types of variables, and some preconditions and postconditions on subprograms to communicate relevant properties to their callers.


Even if a property is provable, automatic provers may fail to prove it, due to limitations of the heuristic techniques used in automatic provers. In practice, these limitations are mostly visible on non-linear integer arithmetic (such as division and modulo) and floating-point arithmetic.


Some properties may not be expressible easily in the form of data invariants and subprogram contracts, for example properties on execution traces or temporal properties. Other properties may require the use of non-intrusive instrumentation in the form of ghost code.

Type predicates
---------------

Type predicates are boolean expressions that constrain the value of objects of a given type. A type predicate can be attached to a scalar type or subtype:

.. code-block:: ada

   type Even is new Integer
     with Predicate => Even mod 2 = 0;


In the case above, the use of the type name Even in the predicate expression denotes the current object of type Even, which must be even for the expression to evaluate to True. Similarly, a type predicate can be attached to an array type or subtype:

.. code-block:: ada

   subtype Simple_String is String
     with Predicate => Simple_String'First = 1 and Simple_String'Last in Natural;

   type Sorted is array (1 .. 10) of Integer
     with Predicate => (for all J in 1 .. 9 => Sorted(J) <= Sorted(J+1));


The Simple_String is the same as standard String, except objects of this type always start at index 1 and have a unique representation for the null string, which ends at index 0. Type Sorted uses a more complex quantified expression to express that contiguous elements in the array are sorted in increasing order. Finally, a type predicate can also be attached to a record type or subtype:

.. code-block:: ada

   type Name (Size : Positive) is record
      Data : String(1 .. Size);
      Last : Positive;
   end record
     with Predicate => Last <= Size;


Discriminated record Name is a typical example of a variable-sized record, whose internal array Data is used up to the value of component Last. The predicate expresses an essential invariant to maintain about objects of type Name, that Last should always be no greater to Size, for accesses to Data(Last) to be in bounds.


Preconditions
-------------

Preconditions are boolean expressions that should hold each time a subprogram is called. Preconditions are typically used to express API constraints that ensure correct execution of the subprogram, and can thus replace or complement comments and/or defensive code that expresses/checks such constraints. Compare the following three styles of expressing that string Dest should be at least as long as string Src when copying Src into Dest. The first way is to express the constraint in a comment attached to the subprogram declaration:

.. code-block:: ada

   procedure Copy (Dest : out String; Src : in String);
   --  Copy Src into Dest. Require Dest length to be no less than Src length,
   --  otherwise an exception is raised.


While readable by humans, this constraint cannot be verified automatically. The second way is to express the constraint in defensive code inside the subprogram body:

.. code-block:: ada

   procedure Copy (Dest : out String; Src : in String) is
   begin
      if Dest'Length < Src'Length then
             raise Constraint_Error;
      end if;
      --  copies Src into Dest here
   end Copy;


While this constraint can be verified at run time, it is hidden inside the implementation of the subprogram, and it cannot be verified statically with GNATprove. The third way is to express the constraint as a precondition:

.. code-block:: ada

   procedure Copy (Dest : out String; Src : in String)
     with Pre => Dest'Length >= Src'Length;
   --  Copy Src into Dest.


This constraint is readable by humans, and it can be verified both at run time and statically with GNATprove.


Postconditions
--------------

Postconditions are boolean expressions that should hold each time a subprogram returns. Postconditions are similar to the usual assertions used by programmers to check properties at run time (with pragma Assert), but they are more powerful:

#. When a program has multiple returns, it is easy to forget to add a pragma Assert before one of the exit points. Postconditions avoid that pitfall.
#. Postconditions can express relations between values of variables at subprogram entry and at subprogram exit, using the attribute X’Old to denote the value of variable X at subprogram entry.


Postconditions can be used to express key transitions in the program performed by some subprograms. For example, some data collected from a network may need to be sanitized and then normalized before being fed to the main treatment of the program. This can be expressed with postconditions:

.. code-block:: ada

   type Status is (Raw, Sanitized, Normalized);
   type Chunk is record
      Data : String (1 .. 256);
      Stat : Status;
   end record;

   procedure Sanitize (C : in out Chunk)
     with Pre  => C.Stat = Raw,
          Post => C.Stat = Sanitized;

   procedure Normalize (C : in out Chunk)
     with Pre  => C.Stat = Sanitized,
          Post => C.Stat = Normalized;

   procedure Main_Treatment (C : in Chunk)
     with Pre => C.Stat = Normalized;


In the code snippet above, preconditions and postconditions are used to track the status of the data chunk C, so that we can guarantee that treatments are performed in the specified order.

Ghost Code
----------

Sometimes, the variables and functions that are present in a program are not sufficient to specify intended properties and to verify these properties with GNATprove. This is the case if the property that should be verified is never used explicitly in the code. For example, the property that a collection is sorted can be maintained for efficient modifications and queries on the collection, without the need to have an explicit function Is_Sorted. This function is essential however to state the property that the collection remains sorted.


In such a case, it is possible in SPARK to insert in the program additional code useful for specification and verification, specially identified with the aspect Ghost so that it can be discarded during compilation. So-called ghost code in SPARK are these parts of the code that are only meant for specification and verification, and have no effect on the functional behavior of the program.


Various kinds of ghost code are useful in different situations:
* Ghost functions are typically used to express properties used in contracts.
* Global ghost variables are typically used to keep track of the current state of a program, or to maintain a log of past events of some type. This information can then be referred to in contracts.


Typically, the current state of the program may be stored in a global ghost variable, whose value may be suitably constrained in preconditions and postconditions. For example, the program may need to circle through a number of steps, from sanitization through normalization to main treatment. A ghost variable Current_State may then be used to record the current status of the program, and its value may be used in contracts as follows:

.. code-block:: ada

   type Status is (Raw, Sanitized, Normalized) with Ghost;
   Current_State : Status with Ghost;

   procedure Sanitize
     with Pre  => Current_State = Raw,
          Post => Current_State = Sanitized;

   procedure Normalize
     with Pre  => Current_State = Sanitized,
          Post => Current_State = Normalized;

   procedure Main_Treatment
     with Pre => Current_State = Normalized;


See the SPARK User’s Guide for more examples of ghost code:
http://docs.adacore.com/spark2014-docs/html/ug/source/specification_features.html#ghost-code

Investigating Unproved Properties
---------------------------------

As seen at silver level in the section on Investigating Unproved Run-time Checks, it is also expected that many messages about possible violations of properties (assertions, contracts) are issued the first time a program is analyzed, for similar reasons:

#. The analysis done by GNATprove relies on the information provided in the program to compute possible relations between variables. For proving properties, this information lies chiefly in the contracts added by programmers. If contracts are not precise enough, then GNATprove cannot prove the desired properties.
#. The initial analysis performed at proof level 0 is the fastest but also the least precise. At the gold level, we rather advise to start at level 2, so that all provers are called with reasonable effort (steps). During the interaction with GNATprove, while contracts and assertions are added in the program, it is in general profitable to perform analysis with only CVC4 enabled (--prover=cvc4), no step limit (--steps=0) and a higher timeout for individual proof attempts (--timeout=30) to get both faster and more precise results. Note that using timeouts instead of steps is not portable between machines, hence it is better to reserve its use for interactive use. The following snapshot shows the popup window from GPS (using the Advanced User profile set through menu Preferences → SPARK) with these settings:

.. image:: _static/prove_more.png
   :align: center
   :alt: Popup window from GPS for "prove" mode




Proving properties requires interacting with GNATprove inside GPS. Thus, we suggest that you select a unit (preferably one with few dependences over other unproved units, ideally a leaf unit not depending on other unproved units) with some unproved checks. Open GPS on your project, display this unit inside GPS, and put the focus on this unit. Inside this unit, select a subprogram (preferably one with few calls to other unproved subprograms, ideally a leaf subprogram not calling other unproved subprograms) with some unproved checks. This is the first subprogram you will analyze at gold level.


For each unproved property in this subprogram, you should follow the following steps:

#. Understand why the property cannot fail at run time. If you do not understand why a property holds, GNATprove cannot understand it either. You may discover at this stage that indeed the property may fail at run time, in which case you will need to first correct the program so that it is not possible.
#. Determine if the reasons for the property to hold are known locally. GNATprove analysis is modular, which means that it only looks at locally available information to determine whether a check succeeds or not. This information consists mostly in the types of parameters and global variables, the precondition of the subprogram, and the postconditions of the subprogram it calls. If the information is not locally available, you should change types and/or add contracts to make it locally available to the analysis.
#. If the property depends on the value of a variable being modified in a loop, you may need to add a loop invariant, i.e. a specific annotation in the form of a pragma Loop_Invariant inside the loop, that summarizes the effect of the loop on the variable value. See the specific section of the SPARK User’s Guide on that topic: http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_write_loop_invariants.html.
#. Once you are confident this property should be provable, run SPARK in proof mode on the specific line with the check by right-clicking on this line in the editor panel inside GPS, and select SPARK → Prove Line from the contextual menu. In the GPS panel, select “2” as value for “Proof level” (and possibly set the switches --prover=cvc4 --steps=0 --timeout=30 in the textual box, as described above), check the box “Report checks proved”, and click on “Execute”. GNATprove should output either a message that confirms that the check is proved, or the same message as before. In the latter case, you will need to interact with GNATprove to investigate why the check is still not proved.
#. It may be difficult sometimes to distinguish cases where some information is missing for the provers to prove the property from cases where the provers are incapable of proving the property. Multiple actions may help distinguishing those cases, as documented in a specific section of the SPARK User’s Guide on that topic (see subsections on “Investigating Unprovable Properties” and “Investigating Prover Shortcomings”): http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_investigate_unproved_checks.html The most generally useful action to narrow down the issue to its core is to insert assertions in the code that “test” whether the property (or part of it) can be proved at some specific point in the program. For example, if a postcondition states a property (P or Q), and the implementation contains many branches and paths, try adding assertions that P holds or Q holds where they are expected to hold. This may point to a specific path in the program, and a specific part of the property, which cause the issue. This may also help provers to manage to prove both the assertion and the property. In such a case, it is good practice to retain in the code only those essential assertions that help getting automatic proof, and to remove other intermediate assertions that were inserted during interaction.
#. If the check turns out to be unprovable due to limitations in the proving technology, you will have to justify its presence so that future runs of GNATprove will not report it again, by inserting a pragma Annotate after the line where the check message is reported. See SPARK User’s Guide at http://docs.adacore.com/spark2014-docs/html/ug/source/how_to_investigate_unproved_checks.html.


.. _Example:

Example
=======

As an example, we applied the guidelines in this document to the top-level program in the GNATprove tool, called gnatprove, which handles the configuration switches, calls other executables to do the analysis and reports messages. We started by manually adding a pragma SPARK_Mode (On) to every file of the project. As gnatprove is small (26 units for a total of 4,500 sloc) we did not need any automation for this step. We then ran GNATprove in check mode. It appeared that no unit of the project was in SPARK, mostly because of string access types in configuration phase and because of uses of standard container packages for reporting, both of which are not in SPARK.


We chose to concentrate on the print_table package which display the results of a run of GNATprove as a table. It stores the results inside a two dimensional array and then prints them in the gnatprove.out file. It is rather small but exhibits possible run-time errors, for example when accessing inside the array or when computing the size required for the table.

Stone Level
-----------

We first ran GNATprove in check mode on the unit. A non-conformance was found due to the initializing function for the table having global outputs. Indeed, the unit was designed to construct a unique table, by storing elements line by line from right to left. The current position in the table was stored as a global variable in the package body. As the table array itself was of an unconstrained type (we do not know the number of lines and columns required a priori) it was not stored as a global variable, but carried explicitly as a parameter of the storage procedure. The initialization function both returned a new array, and initialized the value of the current position, thus having global outputs:

.. code-block:: ada

   function Create_Table (Lines, Cols : Natural) return Table is
      T : constant Table (1 .. Lines, 1 .. Cols) :=
        (others => (others => Cell'(Content => Null_Unbounded_String,
                                    Align   => Right_Align)));
   begin
      Cur_Line := 1;
      Cur_Col := 1;
      return T;
   end Create_Table;


To deal with a function with output globals, the guidelines advise to either hide the function body for analysis if the effect does not matter for proof, or to turn it into a procedure with an out parameter. None of these solutions was adequate here as the effects of this function do matter and the array cannot be given as an out parameter as it is unconstrained. In fact, the non-conformance here comes from a bad implementation choice which separated the table from its cursors, allowing for unexpected behaviors if two tables were to be initialized. We therefore chose to redesign the code and introduced a record with discriminants to hold both the array and the current position. As this record is of an unconstrained type, it is not stored in a global variable but rather passed explicitly as a parameter as the array used to be.

.. code-block:: ada

   type Table (L, C : Natural) is record
      Content  : Table_Content (1 .. L, 1 .. C);
      Cur_Line : Positive;
      Cur_Col  : Positive;
   end record;

   function Create_Table (Lines, Cols : Natural) return Table;


Apart from this non-conformance, GNATprove issued a dozen of warnings about assuming no effect of functions from the Ada.Strings.Unbounded and Ada.Text_IO libraries. This is fine as these functions indeed should have no effects on variables visible to GNATprove. It simply means that issues that may arise when using these libraries are outside of the scope of GNATprove and should be verified in a different way.


We ran GNATprove in mode check_all on the unit without further errors. We thus reached stone level on this unit.

Bronze Level
------------

We then ran GNATprove in flow analysis mode on the unit. No check message was emitted. We only got a new warning stating that the procedure Dump_Table which writes the value of the table to the gnatprove.out file had no effect. This is expected as the functions from the Ada.Text_IO library are assumed to have no effect.


As no global variables are accessed by the unit subprograms after the modification outlined earlier, we have added global contracts on every subprogram enforcing this:

.. code-block:: ada

   function Create_Table (Lines, Cols : Natural) return Table with
     Global => null;


These contracts are all verified by GNATprove. We thus reached bronze level on this unit.

Silver Level
------------

We then ran GNATprove in prove mode on the unit. 13 check messages were emitted:


* 3 array index checks when accessing at the current position in the table,
* 1 assertion used as defensive coding,
* 2 range checks on Natural, and
* 7 overflow checks when computing the maximal size of the array.


To be able to prove the array index checks, we needed to state that the position is valid in the array when storing a new element. For this, we put preconditions on the storing procedure:

.. code-block:: ada

   procedure Put_Cell
     (T     : in out Table;
      S     : String;
      Align : Alignment_Type := Right_Align)
   with
     Global => null,
     Pre    => T.Cur_Line <= T.L and then T.Cur_Col <= T.C;

Thanks to this precondition, GNATprove could successfully verify the index checks as well as two overflow checks located at the increment of the position cursors.

The assertion states that the procedure New_Line, which moves the current position to the beginning of the next line, can only be called if we are at the end of the current line. We transformed it into a precondition.

.. code-block:: ada

   procedure New_Line (T : in out Table)
   with
     Global => null,
     Pre    => T.Cur_Col = T.C + 1 and then T.Cur_Line <= T.L;

Avoiding run-time errors in the computation of the maximal size of the table was more complicated. It required bounding both the maximal number of elements in the table and the size of each element. For bounding the maximal number of elements in the table, we introduce a constrained subtype of Positive for the size of the table, as described in the guidelines:

.. code-block:: ada

   subtype Less_Than_Max_Size is Natural range 0 .. Max_Size;

   type Table (L, C : Less_Than_Max_Size) is record
      Content  : Table_Content (1 .. L, 1 .. C);
      Cur_Line : Positive;
      Cur_Col  : Positive;
   end record;

We could not introduce a range for the size of the elements stored in the table, as they are not scalars but unbounded strings. We thus resorted to a Dynamic_Predicate to express the constraint:

.. code-block:: ada

   type Cell is record
      Content : Unbounded_String;
      Align   : Alignment_Type;
   end record with
     Dynamic_Predicate => Length (Content) <= Max_Size;

We then needed to add an additional precondition to Put_Cell to appropriately constrain the strings that can be stored in the table. With these constraints, as well as some loop invariants to propagate the bound throughout the computation of the maximal size of the table, every check message were discharged but 3, which needed additional information on the subprograms from the unbounded strings library. We introduced an assumption for why the checks could not fail and justified it by quoting the Ada Reference Manual as it is easier to review a single assumption than try to understand what can cause a more complex check to fail.

.. code-block:: ada

   pragma Assume (Length (Null_Unbounded_String) = 0,
                  "Null_Unbounded_String represents the null String.");
   T.Content (T.Cur_Line, T.Cur_Col) :=
     Cell'(Content => To_Unbounded_String (S),
           Align   => Align);


There were not anymore unproved check messages when running GNATprove in prove mode on print_table. We thus reached silver level on this unit.

Gold Level
----------

The subprograms defined in Print_Table are annotated with precise comments describing their effects on the table. As an example, here is the comment associated to Put_Cell:

.. code-block:: ada

   procedure Put_Cell
     (T     : in out Table;
      S     : String;
      Align : Alignment_Type := Right_Align);
   --  Print a string into the current cell of the table, and move to the next
   --  cell. Note that this does not move to the next line,  you need to call
   --  New_Line below after printing to the last cell of a line.


We used these comments to come up with postconditions on the procedures used to create the table. So that the postcondition of Put_Cell is easier to read, we decided to introduce a ghost expression function Is_Set that relates the values of the content of the table before and after the update:

.. code-block:: ada

   function Is_Set
     (T    : Table_Content;
      L, C : Less_Than_Max_Size;
      S    : String;
      A    : Alignment_Type;
      R    : Table_Content) return Boolean
   --  Return True if R is S updated at position (L, C) with Cell (S, A)

   is

      --  T and R range over the same ranges

     (T'First (1) = R'First (1) and then T'Last (1) = R'Last (1)
      and then T'First (2) = R'First (2) and then T'Last (2) = R'Last (2)

      --  They contain the same values except at position L, C where R contains
      --  S and A.

      and then L in T'Range (1) and then C in T'Range (2)
      and then To_String (R (L, C).Content) = S
      and then R (L, C).Align = A
      and then (for all I in T'Range (1) =>
                  (for all J in T'Range (2) =>
                       (if I /= L and J /= C then R (I, J) = T (I, J)))))
   with Ghost;


Using this function, we can rephrase the comment of Put_Cell into a simple postcondition:

.. code-block:: ada

   procedure Put_Cell
     (T     : in out Table;
      S     : String;
      Align : Alignment_Type := Right_Align)
   with
     Global => null,
     Pre    => T.Cur_Line <= T.L and then T.Cur_Col <= T.C
     and then S'Length <= Max_Size,

     --  S has been printed inside the current cell with alignment Align

     Post   => Is_Set (T => T.Content'Old,
                       L => T.Cur_Line'Old,
                       C => T.Cur_Col'Old,
                       S => S,
                       A => Align,
                       R => T.Content)

     --  We have moved to the next cell, but not moved to the next line, even
     --  if needed.

      and T.Cur_Line = T.Cur_Line'Old and T.Cur_Col = T.Cur_Col'Old + 1;


For GNATprove to verify this postcondition, we had to introduce yet another assumption relating the result of To_String on an application of To_Unbounded_String to its input:

.. code-block:: ada

   pragma Assume (To_String (To_Unbounded_String (S)) = S,
                  String'("If S is a String, then "
                    & "To_String(To_Unbounded_String(S)) = S."));


We translated in the same way the comments provided on every subprogram dealing with the creation of the table. We did not supply any contract for the subprogram responsible for dumping the table into a file as it is modeled in SPARK as having no effect.


These contracts are all verified by GNATprove. We thus reached gold level on this unit.


.. _References:

References
==========

The e-learning website AdaCore University proposes a freely available course on SPARK in five lessons at http://university.adacore.com/courses/spark-2014/


The SPARK User’s Guide is available at http://docs.adacore.com/spark2014-docs/html/ug/


The SPARK Reference Manual is available at http://docs.adacore.com/spark2014-docs/html/lrm/


The official book on SPARK is “Building High Integrity Applications with SPARK” by McCormick and Chapin, edited by Cambridge University Press. It is sold online by Amazon and many others.






For a historical account of the evolution of SPARK technology and its use in industry, see the article “Are We There Yet? 20 Years of Industrial Theorem Proving with SPARK” by Chapman and Schanda, at http://proteancode.com/keynote.pdf


The website http://www.spark-2014.org/ is a portal for up-to-date information and resources on SPARK, including an active blog detailing the latest evolutions.


The document “AdaCore Technologies for CENELEC EN 50128:2011” presents the usage of AdaCore’s technology in conjunction with the CENELEC EN 50128:2011 standard. It describes in particular where the SPARK technology fits best and how it can best be used to meet various requirements of the standard. See:
http://www.adacore.com/knowledge/technical-papers/adacore-technologies-for-cenelec-en-501282011/


A similar document “AdaCore Technologies for DO-178C/ED-12C” will be available soon, presenting the usage of AdaCore’s technology in conjunction with the DO-178C/ED-12C standard, and describing in particular the use of SPARK in relation with the Formal Methods supplement DO-333/ED-216.
