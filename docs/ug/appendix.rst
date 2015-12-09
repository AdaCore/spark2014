.. _Appendix:

********
Appendix
********

.. _Command Line Invocation:

Command Line Invocation
=======================

|GNATprove| is executed with the following command line::

 Usage: gnatprove -Pproj [files] [switches] [-cargs switches]
 proj is a GNAT project file
 files is one or more file names
 -cargs switches are passed to gcc

 gnatprove basic switches:
  -aP=p               Add path p to project path
      --assumptions   Output assumptions information
      --clean         Remove GNATprove intermediate files, and exit
  -f                  Force recompilation/analysis of all units
  -h, --help          Display this usage information
  -jnnn               Use nnn parallel processes (default: 1)
  -k                  Do not stop analysis at the first error
      --level=n       Set the level of proof (0 = faster* to 4 = more powerful)
  -m                  Minimal reanalysis
      --mode=m        Set the mode of GNATprove (m=check, flow, prove, all*)
  -q, --quiet         Be quiet/terse
      --report=r      Set the report mode of GNATprove (r=fail*, all, statistics)
  -u                  Unique analysis. Only analyze the given units
  -U                  Analyze all units of all projects
  -v, --verbose       Output extra verbose information
      --version       Output version of the tool and exit
      --warnings=w    Set the warning mode of GNATprove (w=off, continue*, error)

  * Main mode values
    . all           - Activates all modes (default)
    . check         - Check SPARK restrictions for code where SPARK_Mode=On
    . flow          - Prove object initialization and flow contracts
    . prove         - Prove subprogram contracts and absence of run-time errors

  * Report mode values
    . all           - Report all results of proving checks
    . fail          - Report failures to prove checks (default)
    . statistics    - Same as all, plus timing and steps information

  * Warning mode values
    . continue      - Issue warnings and continue (default)
    . error         - Treat warnings as errors
    . off           - Do not issue warnings

 gnatprove advanced switches:
  --no-counterexample Do not generate a counterexample for unproved formulas
  -d, --debug         Debug mode
  --dbg-proof-only    Disable flow analysis (possibly unsound results)
  --flow-debug        Extra debugging for flow analysis (requires graphviz)
  --limit-line=s      Limit analysis to given file and line
  --limit-subp=s      Limit analysis to subprogram defined by file and line
  --pedantic          Use a strict interpretation of the Ada standard
  --proof=g[:l]       Set the proof modes for generation of formulas
                      (g=per_check*, per_path, progressive) (l=lazy*, all)
  --prover=s[,s]*     Use given provers (s=altergo, cvc4*, z3, ...)
  --RTS=dir           Specify the Ada runtime name/location
  --steps=nnn         Set the maximum number of proof steps (prover-specific)
  --timeout=s         Set the prover timeout in seconds (default: 1)
  --why3-conf=f       Specify a configuration file for why3

  * Proof mode values for generation
    . per_check     - Generate one formula per check (default)
    . per_path      - Generate one formula per path for each check
    . progressive   - Start with one formula per check, then split into
                      paths when needed

  * Proof mode values for laziness
    . all           - Attempt to prove all formulas
                      (most suited for combination of automatic and manual proof)
    . lazy          - Stop at first unproved formula for each check
                      (most suited for fully automatic proof) (default)

  * Prover name values
    (Default prover is cvc4.)
    (Provers marked with [steps] support the --steps switch.)
    . altergo       - [steps] Use Alt-Ergo
    . cvc4          - [steps] Use CVC4
    . z3            - [steps] Use Z3
    . ...           - Any other prover configured in your .why3.conf file

.. _Alternative_Provers:

Alternative Provers
===================

Installed with |SPARK|
----------------------

The provers Alt-Ergo, CVC4 and Z3 are installed with the |SPARK| tool. By
default, |GNATprove| uses prover CVC4 only. Switch ``--level`` changes the
default to use one or more provers depending on the chosen level (see
:ref:`Running GNATprove from the Command Line`). Switch ``--prover`` allows to
use another prover, or a list of provers. Prover names ``altergo``, ``cvc4``
and ``z3`` are used to refer to the versions of provers Alt-Ergo, CVC4 and Z3
that are installed with the |SPARK| toolset. The string ``alt-ergo`` can also
be used to refer to Alt-Ergo. More information on Alt-Ergo, CVC4 and Z3 can be
found on their respective websites:

 * Alt-Ergo: http://alt-ergo.ocamlpro.com
 * CVC4: http://cvc4.cs.nyu.edu
 * Z3: https://z3.codeplex.com

Other Automatic or Manual Provers
---------------------------------

Updating the Why3 Configuration File
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove| can call other provers, as long as they are supported by the Why3
platform (see complete list on `Why3 webpage
<http://why3.lri.fr/#provers>`_). To use another prover, it must be listed in
your Why3 configuration file.

To create or update automatically a Why3 configuration file, call the command
``<spark2014-install>/libexec/spark/bin/why3config --detect-provers``. It
searches your ``PATH`` for any supported provers and adds them to the default
configuration file ``.why3.conf`` in your ``HOME``, or a configuration file
given in argument with switch ``-C <file>``.  This file consists of a few
general settings and a section for each prover which is supported.

|GNATprove| reads the default configuration file ``.why3.conf`` in your
``HOME``, or the configuration file given in argument with switch
``--why3-conf=<file>``. Any prover name configured in this configuration file
can be used as an argument to switch ``--prover``.

Note that using this mechanism, you cannot replace the definitions provided
with the SPARK tools for the provers ``altergo``, ``cvc4`` and ``z3``.

If more than one prover is specified, the provers are tried in order on each
VC, until one of them succeeds or all fail. Interactive provers cannot be
combined with other provers, so must appear on their own.

Sharing Libraries of Theorems
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When |GNATprove| is used with a manual prover, the user can provide libraries
of theorems to use during the proof process.

To do so, the user will need to set a proof directory (see :ref:`Project
Attributes` for more details on this directory).  The user needs to create a
folder with the same name as the chosen manual prover (the casing of the name
is the same as the one passed to the switch ``--prover``) and put the library
sources inside this folder.

Finally, some additional fields need to be added to the prover configuration
in the Why3 configuration file (a basic example of prover configuration can
be found in the section on :ref:`Coq`):

* ``configure_build``: this field allows you to specify a command to configure
  the compilation of the library of theorems. This command will be called each
  time a source file is added to the library.

* ``build_commands``: this field allows you to specify a set of command which
  will be called sequentially to build your library. These commands will be
  called each time |GNATprove| runs the corresponding manual prover.
  (In order to define multiple commands for this field, just set the field
  multiple times with different values, each time the field is set it adds a
  new element to the set of ``build_commands``).

Inside these commands, pattern ``%f`` refers to the name of the library file
considered, and ``%o`` to the name of the main ``gnatprove`` repository
generated by |GNATprove|. This allows referring to the path of the compiled
library of theorems inside these commands with ``%o/user/<prover_name>``.

.. _Coq:

Coq
---

When manual proof is needed, one possibility is to use the interactive prover
Coq. For this you can install or compile your version of Coq on your system,
it is recommended to also install an appropriate editor (for instance
CoqIDE or ProofGeneral). Even if running ``why3config --detect-provers``
outputs:

    ``Found prover Coq version X, but Why3 wasn't compiled with support for it``

you can still use Coq on |SPARK| VCs. To do so, you just have to add the
following lines to your ``.why3.conf``::

    [prover]
    command = "coqtop -batch -I %o/coq-tactic -R %o/coq Why3 -l %f"
    driver = "${install_dir}/share/why3/drivers/coq.drv"
    editor = "${editor}"
    in_place = false
    interactive = true
    name = "Coq"
    shortcut = "coq"
    version = "X"

For this to work:

- ``coqtop`` must be in your executable path (alternatively you can provide the
  full path to ``coqtop``);

- ``${install_dir}`` should be the directory where you installed |SPARK|;

- ``${editor}`` must be a previously defined editor in ``.why3.conf``,
  here are the configurations for the two commonly used editors for Coq,
  ``CoqIDE`` and ``Proof General``::

    [editor proofgeneral-coq]
    command = "emacs --exec \\\"(push '(\\\"%o/why3_libs/coq\\\" \\\"Why3\\\") coq-load-path)\\\" %f"
    name = "Emacs/ProofGeneral/Coq"

    [editor coqide]
    command = "coqide -I %l/coq-tactic -R %o/why3_libs/coq Why3 %f"
    name = "CoqIDE"


- replace the version by your Coq version (e.g. ``version = "8.4pl3"``)

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


Implementation Defined Pragmas
==============================

.. _Pragma_SPARK_Mode:

Pragma ``SPARK_Mode``
---------------------

SPARK_Mode is a three-valued aspect. At least until we get to the
next paragraph, a SPARK_Mode of On, Off, or Auto is associated
with each Ada construct. Roughly, the meaning of the three values is the
following:

 * a value of On means that the construct is required to be in |SPARK|, and
   the construct will be analyzed by |GNATprove|.
 * a value of Off means that the construct will not be analyzed by
   |GNATprove|, and does not need to obey the |SPARK| restrictions. The
   construct also cannot be referenced from other parts that are required to
   be in |SPARK|.
 * a value of Auto means that the construct will not be analyzed, and
   |GNATprove| will infer whether this construct can be used in other |SPARK|
   parts or not.

We now explain in more detail how the SPARK_Mode pragma works.

Some Ada constructs are said to have more than one "section".
For example, a declaration which requires a completion will have (at least)
two sections: the initial declaration and the completion. The SPARK_Modes
of the different sections of one entity may differ. In other words,
SPARK_Mode is not an aspect of an entity but rather of a section of an entity.

For example, if a subprogram declaration has a SPARK_Mode of On while
its body has a SPARK_Mode of Off, then an error would be generated if
the subprogram  took a parameter of an access type but not if
the subprogram declared a local variable of an
access type (recall that access types are not in |SPARK|).

A package is defined to have 4 sections: its visible part, its private part,
its body declarations, and its body statements. A protected or task unit has
3 sections: its visible part, its private part, and its body.
Other declarations which require a completion have two sections, as noted
above; all other entities and constructs have only one section.

If the SPARK_Mode of a section of an entity is Off, then the SPARK_Mode
of a later section of that entity shall not be On. [For example, a subprogram
can have a SPARK declaration and a non-SPARK body, but not vice versa.]

If the SPARK_Mode of a section of an entity is Auto, then the SPARK_Mode
of a later section of that entity shall not be On or Off.

The SPARK_Mode aspect can be specified either via a pragma or via an
aspect_specification. In some contexts, only a pragma can be used
because of syntactic limitations. In those contexts where an
aspect_specification can be used, it has the same effect as a
corresponding pragma.

The form of a pragma SPARK_Mode is as follows:

.. code-block:: ada

   pragma SPARK_Mode [ (On | Off) ]

The form for the aspect_definition of a SPARK_Mode aspect_specification is
as follows:

.. code-block:: ada

   [ On | Off ]

For example:

.. code-block:: ada

   package P
      with SPARK_Mode => On
   is

The pragma can be used as a configuration pragma. The effect of
such a configuration pragma is described below in the rules for
determining the SPARK_Mode aspect value for an arbitrary section of an
arbitrary Ada entity or construct.

Pragma ``SPARK_Mode`` shall be used as a local pragma in only the following
contexts and has the described semantics:

* When the pragma appears at the start of the visible declarations (preceded
  only by other pragmas) of a package declaration, it specifies the
  SPARK_Mode aspect of the visible part of the package. This can also
  be accomplished via a SPARK_Mode aspect specification as part of the
  package_specification.

* When the pragma appears at the start of the visible declarations (preceded
  only by other pragmas) of a task or protected unit, it specifies the
  SPARK_Mode aspect of the visible part of the unit. This can also
  be accomplished via a SPARK_Mode aspect specification as part of the
  declaration.

* When the pragma appears at the start of the private declarations of a
  package, a protected unit, or a task unit (only other pragmas can appear
  between the ``private`` keyword and the ``SPARK_Mode`` pragma), it
  specifies the SPARK_Mode aspect of the private part. [This cannot be
  accomplished via an aspect_specification.]

* When the pragma appears immediately at the start of the declarations of a
  package body (preceded only by other pragmas),
  it specifies the SPARK_Mode aspect of the body declarations of the package.
  This can also be accomplished via a SPARK_Mode aspect specification
  as part of the package_body.

* When the pragma appears at the start of the elaboration statements of
  a package body (only other pragmas can appear between the ``begin``
  keyword and the ``SPARK_Mode`` pragma),
  it specifies the SPARK_Mode aspect of the body
  statements of the package. [This cannot be accomplished via
  an aspect_specification.]

* When the pragma appears immediately at the start of the declarations of a
  protected or task body (preceded only by other pragmas),
  it specifies the SPARK_Mode aspect of the body.
  This can also be accomplished via a SPARK_Mode aspect specification
  as part of the protected or task body.

* When the pragma appears after a subprogram declaration (with only other
  pragmas intervening), it specifies the SPARK_Mode aspect of the
  subprogram's specification. This can also be accomplished via a SPARK_Mode
  aspect_specification as part of the subprogram_declaration.
  [This does not include the case of a subprogram whose initial declaration
  is via a subprogram_body_stub. Such a subprogram has only one section
  because a subunit is not a completion.]

* When the pragma appears at the start of the declarations of a subprogram
  body (preceded only by other pragmas), it specifies the SPARK_Mode aspect
  of the subprogram's body. This can also be accomplished via a SPARK_Mode
  aspect_specification as part of the subprogram_body.

A default argument of On is assumed for any SPARK_Mode pragma or
aspect_specification for which no argument is explicitly specified.

A SPARK_Mode of Auto cannot be explicitly specified; the
cases in which a SPARK_Mode of Auto is implicitly specified are
described below. Roughly speaking, Auto indicates that it is left up to
the formal verification tools to determine whether or not a given construct
is in |SPARK|.

A SPARK_Mode pragma or aspect specification shall only apply to a
(section of a) library-level package, generic package, subprogram, or
generic subprogram. If a generic unit contains a SPARK_Mode pragma or
aspect specification, then this rule also applies to the corresponding
pragma or aspect specification which implicitly occurs within any
instance of the generic unit. Except in one case described later
in this section, this means that instances of such a generic shall only
be declared at library level.

The SPARK_Mode aspect value of an arbitrary section of an arbitrary
Ada entity or construct is then defined to be the following value
(except if this yields a result of Auto for a non-package; see below):

- If SPARK_Mode has been specified for the given section of the
  given entity or construct, then the specified value;

- else for the private part of a package or a protected or task unit,
  the SPARK_Mode of the visible part;

- else for a package body's statements, the SPARK_Mode of the
  package body's declarations;

- else for any of the visible part or body declarations of a library
  unit package or either section of a library unit subprogram,
  if there is an applicable SPARK_Mode configuration pragma then the
  value specified by the pragma; if no such configuration pragma
  applies, then an implicit specification of Auto is assumed;

- else the SPARK_Mode of the enclosing section of the nearest enclosing
  package or subprogram;

- Corner cases: the SPARK_Mode of the visible declarations of the
  limited view of a package is always Auto; the SPARK_Mode of any
  section of a generic library unit is On.
  [Recall that any generic unit is in |SPARK|.]

If the above computation yields a result of Auto for any construct
other than one of the four sections of a package, then a result of On
or Off is determined instead based on the legality (with respect to
the rules of |SPARK|) of the construct. The construct's SPARK_Mode is
On if and only if the construct is in |SPARK|. [A SPARK_Mode of Auto
is therefore only possible for (sections of) a package.]

In code where SPARK_Mode is On (also called "SPARK code"), the rules of
|SPARK| are enforced. In particular, such code shall not reference
non-SPARK entities, although such code may reference a SPARK declaration
with one or more non-SPARK subsequent sections (e.g., a package whose
visible part has a SPARK_Mode of On but whose private part has a SPARK_Mode
of Off; a package whose visible part has a SPARK_Mode of Auto may also be
referenced).
Similarly, code where SPARK_Mode is On shall not enclose code where
SPARK_Mode is Off unless the non-SPARK code is part of the "completion"
(using that term imprecisely, because we are including the private
part of a package as part of its "completion" here) of a SPARK declaration.
There are also exceptions to this rule (described below) for protected units.

Code where SPARK_Mode is Off shall not enclose code where Spark_Mode is On.
However, if an instance of a generic unit is enclosed
by code where SPARK_Mode is Off and if any SPARK_Mode specifications occur
within the generic unit, then the corresponding SPARK_Mode specifications
occurring within the instance have no semantic effect. [In particular,
such an ignored SPARK_Mode specification could not violate the preceding
"Off shall not enclose On" rule because the Spark_Mode of the
entire instance is Off. Similarly, such an ignored SPARK_Mode specification
could not violate the preceding rule that a SPARK_Mode specification
shall only apply to a (section of a) library-level entity.]

If SPARK_Mode is Off in the visible part of a library unit package, then
SPARK_Mode shall be off for the visible part of any visible child unit of
the package.
If SPARK_Mode is Off in the private part of a library unit package, then
SPARK_Mode shall be off for the visible part  of any private child unit of
the package.
If SPARK_Mode is Off in the private part of a library unit package, then
SPARK_Mode shall be off in any subsequent sections of any child unit
of the package.
[These rules express the general "Off shall not enclose On" principle
as it applies to child units.]

All of the above notwithstanding, the interactions between SPARK_Mode
and protected units follow a slightly different model, not so closely tied
to syntactic enclosure. Roughly speaking, the rules for a protected
unit follow from the rules given for other constructs after notionally
rewriting the protected unit as a package.

A protected unit declaration such as

.. code-block:: ada

   protected type Prot
     with SPARK_Mode => On
   is
      procedure Op1 (X : in out Integer);
      procedure Op2;
      procedure Non_SPARK_Profile (Ptr : access Integer)
        with SPARK_Mode => Off;
   private
      Aaa, Bbb : Integer := 0;
   end Prot;

can be thought of, for purposes of SPARK_Mode rules, as being
a lot like

.. code-block:: ada

   package Pkg
     with SPARK_Mode => On
   is
      type Prot is limited private;
      procedure Op1 (Obj : in out Prot; X : in out Integer);
      procedure Op2 (Obj : in out Prot);
      procedure Non_SPARK_Profile (Obj : in out Prot; Ptr : access Integer)
        with SPARK_Mode => Off;
   private
      type Prot is
        limited record
           Aaa, Bbb : Integer := 0;
        end record;
   end Pkg;

which would be legal. The point is that a protected type which is
in |SPARK| can have protected operation whose declaration is not in |SPARK|
despite the fact that this violates the usual "On shall not enclose
non-completion Off" rule. The declaration of the |SPARK| type no longer
encloses the non-|SPARK| subprogram declaration after this notional rewriting,
so this case is not considered to be a violation. [No such notional rewriting
is needed for task units because task entries are not in |SPARK|.]

SPARK_Mode is an implementation-defined Ada aspect; it is not (strictly
speaking) part of the |SPARK| language. It is used to notionally transform
programs which would otherwise not be in |SPARK| so that they can
be viewed (at least in part) as |SPARK| programs.

Note that if you would like to mark all your code in SPARK_Mode, the
simplest solution is to specify in your project file::

   package Builder is
      for Global_Configuration_Pragmas use "spark.adc";
   end Builder;

and provide a file `spark.adc` which contains::

   pragma SPARK_Mode;

.. _External Axiomatizations:

External Axiomatizations
========================

What is it?
----------------
It is a feature of the |SPARK| toolset that allows to manually supply a WhyMl
translation for the public specification of a library level package that is in
|SPARK|. This feature is still experimental.

Why is it useful?
-------------------------
- For features that cannot easily be described using contracts, like
  transitivity, counting, or summation
- To link functions to the logic world, like trigonometry functions
- To improve provability of client code, like for containers

How does it work?
----------------------------------
- To say that a library package has an external axiomatization, we annotate it
  using::

    pragma Annotate (GNATprove, External_Axiomatization);

- These packages should have SPARK_Mode On on their public specification and
  SPARK_Mode Off on their private part.
- The WhyMl translation for the package should be stored in a subdirectory
  named _theories of the proof directory specified for the project.

What should the translation look like?
-------------------------------------------------------------
- For each publicly visible entity E in the package P, it should provide the
  same elements (types as well as logic and program functions) as the automatic
  translation, all grouped in one single module named P__e. For example, the
  module for a function F should provide both a logic function declaration named
  f__logic and a program function declaration named f.
- For most types, a model module in defined in ada__model.mlw that can be cloned
  to get most of the required declarations.
- The manual translation may use any type, constant and function that is visible
  from the Ada package declaration.
- A good way to start an axiomatization file on a package is to launch the
  toolset on it and copy paste the modules created for each entity of the
  package. A WhyMl file created by the tool on a package P contains a module for
  every declaration visible from it, only declarations from P itself should be
  copied. The generated file usually contains two modules for each entity, one
  named P__e and one named P__e__axiom. Both should be put together in P__e for
  the manual translation. The toolset will replace statically known expressions
  with their value. Beware that they might be architecture dependent.

Example of standard package
---------------------------
For example, let us consider the following package, stored in a file sum.ads,
providing a summation function for slices of arrays of integers:

.. literalinclude:: gnatprove_by_example/examples/sums.ads
   :language: ada
   :linenos:

We can provide the following Why3 translation for it, that we should store in a
file named sum.mlw:

.. literalinclude:: gnatprove_by_example/examples/proof/_theories/sums.mlw
   :language: none

And for generic packages?
--------------------------
- External axiomatizations can also be used for a generic package P, with the
  restriction that P will then have to be instantiated at library level only.
- A generic package with external axiomatization can have type and function
  parameters, but they must be instantiated with pure functions only (that do
  not read global variables).
- If the package as a private type parameter that it used as in out or out
  parameter of a procedure, than this type cannot be instantiated with an array
  type whose bounds are not statically known.
- For now, when a package is instantiated with a function whose argument
  types or return type do not statically match the argument types or the return
  type of the parameter, it is the user responsibility to ensure that there can
  be no error during the conversions.
- The WhyMl translation for a generic package P can refer to its generic
  parameters as being translated in p__args.mlw. This file doesn't need
  to be provided.
- For practical reasons, the name of every module declared in p.mlw
  must be prefixed by P and modules of parameters can neither be
  imported nor exported.

Example of generic package
-----------------------------------------------
As an example, let us consider the formal doubly linked list package.
It has two generic parameters, the type of the elements that will be stored
in the list and the equality function that should be used over them:

.. code-block:: ada

  generic
     type Element_Type is private;

     with function "=" (Left, Right : Element_Type)
                        return Boolean is <>;

  package Ada.Containers.Formal_Doubly_Linked_Lists is
     pragma Annotate (GNATprove, External_Axiomatization);

The WhyMl translation for this package can refer to these parameters as
beging translated in the file
ada__containers__formal_doubly_linked_lists__args.mlw in the
following way::

  module Ada__containers__formal_doubly_linked_lists__element_type
      type base_type
      type element_type

      (* Translations of subprograms taking element_type as an argument will
         have an argument of type base_type.
         We therefore rely on the presence of conversion functions for it. *)
      function to_base element_type : base_type
      function of_base base_type : element_type
      predicate valid base_type
  end

  module Ada__containers__formal_doubly_linked_lists__oeq
    use Ada__containers__formal_doubly_linked_lists__element_type

    (* The name of operators is prefixed with o. Expects arguments of
       element_type's base_type. *)
    function oeq
           Ada__containers__formal_doubly_linked_lists__element_type.base_type
           Ada__containers__formal_doubly_linked_lists__element_type.base_type :
                     bool
  end

The  formal doubly linked list package for example provides on equality
function over lists:

.. code-block:: ada

   function "=" (Left, Right : List) return Boolean with
     Global => null;

Here is the module that we provide for it in
ada__containers__formal_doubly_linked_lists.mlw::

  (* The name of operators is prefixed with o. When a subprogram is overloaded,
     it must be desanbiguated using an integer. To get the expected name for
     an entity, the best way is to look at the automated translation. *)
  module Ada__containers__formal_doubly_linked_lists__oeq__2
    use import int.Int
    (* Do not import or export modules for a generic parameter. *)
    use  "ada__containers__formal_doubly_linked_lists__args".
           Ada__containers__formal_doubly_linked_lists__element_type
    use "ada__containers__formal_doubly_linked_lists__args".
           Ada__containers__formal_doubly_linked_lists__oeq
    use import Ada__containers__formal_doubly_linked_lists__list
    use import Ada__containers__formal_doubly_linked_lists__length
    use import Ada__containers__formal_doubly_linked_lists__cursor
    use import Ada__containers__formal_doubly_linked_lists__element

    function oeq__2__logic list list : bool

    (* Two lists that are equal have the same length... *)
    axiom oeq__2_length_:
     forall co1 co2 : list.
         oeq__2__logic co1 co2 = True -> length_ co1 = length_ co2

    (* ...and contain the same elements at the same position. *)
    axiom oeq__2_element:
     forall co1 co2 : list. oeq__2__logic co1 co2 = True ->
       forall cu1 : cursor [element co1 cu1]. position co1 cu1 > 0 ->
           Ada__containers__formal_doubly_linked_lists__oeq.oeq
            (Ada__containers__formal_doubly_linked_lists__element_type.to_base
              (element co2 (position_inv co2 (position co1 cu1))))
            (Ada__containers__formal_doubly_linked_lists__element_type.to_base
              (element co1 cu1)) = True

    (* Two lists that are not equal either do not have the same length or
       are different at some position. *)
    axiom oeq__2_inv:
     forall co1 co2 : list. oeq__2__logic co1 co2 <> True ->
     (length_ co1 <> length_ co2 \/
     exists i : int. 0 < i <= length_ co1 /\
      Ada__containers__formal_doubly_linked_lists__oeq.oeq
       (Ada__containers__formal_doubly_linked_lists__element_type.to_base
         (element co1 (position_inv co1 i)))
       (Ada__containers__formal_doubly_linked_lists__element_type.to_base
         (element co2 (position_inv co2 i))) = False)

    (* Symmetry axiom *)
    axiom oeq__2_sym :
     forall e1 e2 : list.
	  oeq__2__logic e1 e2 = True -> oeq__2__logic e2 e1 = True

    (* Transitivity axiom *)
    axiom oeq__2_trans :
     forall e1 e2 e3 : list.
	  oeq__2__logic e1 e2 = True -> oeq__2__logic e2 e3 = True ->
                oeq__2__logic e1 e3 = True

    val oeq__2 (co1:list) (co2:list) : bool
       ensures  { result  = oeq__2__logic co1 co2 }
  end

.. _GNATprove_Limitations:

|GNATprove| Limitations
=======================

.. _Tool Limitations:

Tool Limitations
----------------

#. The Global contracts generated automatically by |GNATprove| for subprograms
   without an explicit one do not take into account indirect calls (through
   access-to-subprogram and dynamic binding) and indirect reads/writes to
   global variables (through access variables).

#. A subset of all Ada conversions between array types is supported:

   * element types must be exactly the same
   * matching index types must either be both modular with a base type of the
     same size, or both non modular

#. A subset of all Ada fixed-point types and fixed-point operations is
   supported:

   * fixed-point types must have a small that is a negative power of 2 or 10
   * multiplication and division between different fixed-point types and
     universal real are rejected
   * multiplication and division whose result type is not the same fixed-point
     type as its fixed-point argument(s) are rejected, except for the special
     case of dividing a fixed-point value by the small of its type
     (T'Small) to yield an integer result which is always exact.

   These restrictions ensure that the result of fixed-point operations always
   belongs to the *perfect result set* as defined in Ada RM G.2.3.

#. Loop_Invariant and Loop_Variant pragmas must appear before
   any non-scalar object declaration and any nested loop.

#. Inheriting the same subprogram from multiple interfaces is not supported.

#. Formal object parameters of generics of an unconstrained record type with
   per-object constrained fields are badly supported by the tool and may
   result in crashes in some cases.

#. Quantified expressions with an iterator over a multi dimensional array (for
   example ``for all Elem of Arr`` where ``Arr`` is a multi dimensional array)
   are not supported.

#. Constrained subtypes of class-wide types and 'Class attributes of
   constrained record types are not supported.

#. Abstract states cannot be marked ``Part_Of`` a single task declaration or a
   single protected declaration (see |SPARK| RM 9(3)). An error is raised
   instead in such cases.

#. Classwide Global and Depends contracts as defined in SPARK RM 6.1.6 are not
   supported.

#. Task attributes Identity and Storage_Size are not supported.

Legality Rules
--------------

#. |SPARK| Reference Manual rule 4.3(1), concerning use of the box
   symbol "<>" in aggregates, is not currently checked.

#. The elaboration order rules described in the |SPARK| Reference
   Manual 7.7 are not currently checked.

#. The rule concerned with asserting that all child packages which
   have state denoted as being Part_Of a more visible state
   abstraction are given as constituents in the refinement of the more
   visible state is not checked (|SPARK| Reference Manual rule
   7.2.6(6)).

#. |GNATprove| does not permit formal parameters to be mentioned
   in the ``input_list`` of an Initializes Aspect, contrary
   to |SPARK| Reference Manual 7.1.5(4). This limitation is only
   relevant for packages that are nested inside subprograms.
   This limitation is corrected in versions of the toolset based
   on GNAT Pro 7.2.2, GPL 2014, or later.

#. The case of a state abstraction whose Part_Of aspect denotes a
   task or protected unit is not currently supported.

#. The case of a Refined_Post specification for a (protected) entry
   is not currently supported.

#. The use Ada.Synchronous_Barriers.Synchronous_Barrier type is not currently
   allowed in |SPARK|.

#. Entry families are not currently allowed in |SPARK|.

Flow Analysis Limitations
-------------------------

#. Flow dependencies caused by record assignments is not captured with perfect
   accuracy. This means that the value of one field might incorrectly be
   considered to participate in the derivation of another field that it does
   not really participate in.

Proof Limitations
-----------------

#. Postconditions of recursive functions called in contracts and assertion
   pragmas are not available, possibly leading to unproved checks. The current
   workaround is to use a non-recursive wrapper around those functions.

#. Attribute 'Valid is currently assumed to always return True.

#. Values read from an external source are assumed to be valid values.
   Currently there is no model of invalidity or undefinedness. The onus
   is on the user to ensure that all values read from an external source are
   valid. The use of an invalid value invalidates any proofs associated with
   the value.

#. The following attributes are not yet supported in proof: Address, Adjacent,
   Aft, Alignment, Bit_Order, Body_Version, Component_Size, Copy_Sign,
   Definite, Denorm, First_Bit, First_Valid, Fore, Last_Bit, Last_Valid, Machine,
   all Machine_* attributes, Model, all Model_* attributes, Partition_Id,
   Position, Remainder, Round, Safe_First, Safe_Last, Scale, Scaling,
   Size, Small, Unbiased_Rounding, Version, Wide_Image, Wide_Value,
   Wide_Width, Wide_Wide_Image, Wide_Wide_Value, Wide_Wide_Width,
   Width.

#. The 'Update attribute on multidimensional unconstrained arrays is not
   yet fully supported in proof. Checks might be missing so currently an
   error is emitted for any use of the 'Update attribute on
   multidimensional unconstrained arrays.

#. The difference between the floating-point values +0 and -0 (as defined in
   IEEE-754 standard) is ignored in proof. This is correct for all programs that
   do not exploit the difference in bit-pattern between +0 and -0. For example,
   the following specially crafted program is proved by |GNATprove| but fails at
   run time due to a division by zero, because function ``Magic`` exploits the
   difference of bit-pattern between +0 and -0 by using ``Unchecked_Conversion``
   to return a different integer value for arguments +0 and -0.

   .. code-block:: ada

      pragma SPARK_Mode;

      with Ada.Unchecked_Conversion;

      procedure Zero_And_Unchecked is
         procedure Crash (A, B : Float) is
            function Magic is new Ada.Unchecked_Conversion (Float, Integer);
            X : Integer;
         begin
            if A = B then
               if Magic (B) /= 0 then
                  X := 100 / Magic (A);
               end if;
            end if;
         end Crash;

         type UInt32 is mod 2 ** 32;
         function Convert is new Ada.Unchecked_Conversion (UInt32, Float);

         Zero_Plus : constant Float := Convert (16#0000_0000#);
         Zero_Neg  : constant Float := Convert (16#8000_0000#);
      begin
         Crash (Zero_Plus, Zero_Neg);
      end Zero_And_Unchecked;

#. |GNATprove| does not follow the value of tags for tagged objects. As a
   consequence, tag checks are currently unprovable in most cases.

#. For calls in class-wide postconditions, |GNATprove| uses
   the semantics defined originally in the Ada 2012 Reference Manual (calls to
   primitive operations are dispatching), and not yet the modified semantics
   introduced in the revision of the language AI12-0113 (calls to primitive
   operations are reinterpreted at each level of the inheritance hierarchy).

#. Calls to primitive operations of the tagged type being defined are not
   supported in classwide preconditions. GNATprove does not raise an
   error, but results of proof may be incorrect.

#. Constants declared in loops before the loop invariant are handled as
   variables by the tool. This means in particular that any information
   about their values needed after the loop invariant must be stated explicitly
   in the loop invariant.

#. Preconditions on arithmetic and conversion operators (including Time_Of) in
   Ada.Execution_Time and Ada.Real_Time packages described in |SPARK| Reference
   Manual 9.19 are not yet implemented.

#. The verification condition associated with the Ada rule that it is a bounded
   error to call the Current_Task function from an entry_body, or an interrupt
   handler (see Ada RM C.7.1(17/3)) is not yet implemented.

.. _Portability Issues:

Portability Issues
==================

To execute a |SPARK| program, it is expected that users will compile
the program (as an Ada program) using an Ada compiler.
The SPARK language definition defines a number of implementation-defined
(with respect to the Ada language definition) aspects,
attributes, pragmas, and conventions.
Ideally a |SPARK| program will be compiled using an Ada compiler that
supports all of these constructs. Portability problems may arise
if this is not the case.

This section is a discussion of the strategies available for coping
with this situation.

Probably the most important rule is that pragmas should be used instead
of aspect_specification syntax wherever this option is available. For example,
use pragma Abstract_State rather than specifying the Abstract_State aspect
of a package using aspect_specification syntax. Ada specifies that
unrecognized pragmas shall be ignored, as opposed to being rejected.
This is not the case for (syntactic) aspect specifications
(this terminology is a bit confusing because a pragma can be used to
specify an aspect; such a pragma is semantically, but not syntactically,
an aspect specification).
Furthermore, aspect specification syntax was introduced in Ada 2012
and will be rejected if the program is compiled as, for example, an
Ada 95 program.

Many SPARK-defined constructs have no dynamic semantics (e.g., the Global,
Depends, and Abstract_State aspects), so the run-time behavior of
a program is unaffected if they are ignored by a compiler. Thus, there is
no problem if these constructs are expressed as pragmas which are
then ignored by the Ada compiler.

Of those constructs which do have dynamic semantics, most are run-time
assertions. These include Loop_Variant, Loop_Invariant, Assert_And_Cut,
Contract_Cases, Initial_Condition, and Refined_Postcondition. Because
|SPARK| requires that the success of these assertions must be statically
proven (and that the evaluation of the asserted condition can have no side
effects), the run-time behavior a program is unaffected if they are ignored
by a compiler.

The situation with pragma Assume is slightly different because the
success of the given condition is not statically proven. If ignoring
an Assume pragma at run time is deemed to be unacceptable, then it can
be replaced with an Assert pragma (at the cost of introducing a source
code difference between the |SPARK| program that is analyzed statically
and the Ada program that is executed). An ignored Assume pragma is the
only case where the use of a SPARK-specific construct can lead to a
portability problem which is not detected at compile time. In all
other cases, either the Ada compiler will reject (as opposed to ignore)
an unrecognized construct or the construct can safely be ignored.

An Ada compiler which does not support convention Ghost will reject
any use of this convention. Two safe transformations are available for
dealing with this situation - either replace uses of convention Ghost with
convention Ada or delete the entities declared with a convention of Ghost.
Just as was mentioned above in the case of modifying an Assume pragma,
either choice introduces an analyzed/executed source code difference.

There are two |SPARK| attributes which cannot be used
if they are not supported by the Ada compiler in question: the
Update and Loop_Entry attributes.

|SPARK| includes a rule that a package which declares a state
abstraction requires a body. In the case of a library unit package
(or generic package) which requires a body only because of this rule,
an Ada compiler that knows nothing about state abstractions would
reject the body of the package because of the rule (introduced in Ada 95)
that a library unit package (or generic package) body is never optional;
if it is not required then it is forbidden. In the unlikely event
that this scenario arises in practice, the solution is to force the
library unit package to require a body for some other reason, typically
by adding an Elaborate_Body pragma.

If a |SPARK| program is to be compiled and executed as an Ada 95 program
(or any other pre-2012 version of Ada), then of course any construct
introduced in a later version of Ada must be avoided (unless it is
expressed as a safely-ignored pragma). This seems worth mentioning because
Ada 2012 constructs such as quantified expressions
and conditional expressions are often heavily used in |SPARK| programs.

.. _Semantics of Floating Point Operations:

Semantics of Floating Point Operations
======================================

SPARK assumes that floating point operations are carried out in single
precision (binary32) or double precision (binary64) as defined in the IEEE-754
standard for floating point arithmetic. You should make sure that this is the
case on your platform. For example, on x86 platforms, by default some
intermediate computations may be carried out in extended precision, leading to
unexpected results. With GNAT, you can specify the use of SSE arithmetic by
using the compilation switches "-msse2 -mfpmath=sse" which cause all arithmetic
to be done using the SSE instruction set which only provides 32-bit and 64-bit
IEEE types, and does not provide extended precision. SSE arithmetic is also
more efficient. Note that the ABI allows free mixing of units using the two
types of floating-point, so it is not necessary to force all units in a program
to use SSE arithmetic.

SPARK considers the floating point values which represent positive, negative
infinity or NaN as invalid. Proof obligations are generated that such values
cannot occur.
