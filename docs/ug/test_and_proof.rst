.. _proof and test:

*****************************************
Combining Formal Verification and Testing
*****************************************

Not all subprograms can be verified formally. Subprograms that cannot be
verified formally must be either verified by manual review, or by testing. The
tool GNATtest allows the user to easily develop unit tests for subprograms
declared in library-level package specifications.

Combining Formal Verification and Testing
-----------------------------------------

There are common reasons for combining formal verification on some part
of a codebase and testing on the rest of the codebase:

#. Formal verification is only applicable to a part of the codebase. For
   example, it might not be possible to apply formal verification to Ada code
   that is not in |SPARK|.

#. Formal verification only gives strong enough results on a part of the
   codebase. This might be because the desired properties cannot be expressed
   formally, or because proof of these desired properties cannot be
   sufficiently automated.

#. Formal verification is only cost-effective on a part of the codebase. (And
   it may be more cost-effective than testing on this part of the codebase.)

For all these reasons, it is important to be able to combine the results of
formal verification and testing on different parts of a codebase.

Contracts on subprograms provide a natural boundary for this combination. If a
subprogram is proved to respect its contract, it should be possible to call it
from a tested subprogram. Conversely, formal verification of a subprogram
(including absence of run-time errors and contract checking) depends on called
subprograms respecting their own contracts, whether these are verified by
formal verification or testing.

Formal verification works by making some assumptions, and these assumptions
should be shown to hold even when formal verification and testing are
combined. Certainly, formal verification cannot guarantee the same
properties when part of a program is only tested, as when all of a program is
proved. The goal then, when combining formal verification and testing, is to
reach a level of confidence as good as the level reached by testing alone.

|GNAT Pro| proposes a combination of formal verification and testing for
|SPARK| based on |GNATprove| and GNATtest.

Declarative and Generative Verification Modes
---------------------------------------------

SPARK 2005 strongly favoured the *declarative* verification style - where all
program units required contracts on their specifications.  These
contracts had to be designed and added at an early stage to assist modular
verification, and then maintained by the user as a program evolved.

In contrast, SPARK 2014 is designed to facilitate a more *generative* mode of
program construction and verification, where useful forms of verification can
be achieved with code that complies with the core |SPARK| restrictions, but
otherwise does not have any contracts.  In this mode, implicit contracts can be
computed from the bodies of units, and then used in the analysis of other
units, and so on.  These implicit contracts can be "promoted" by the user to
become part of the specification of a unit, allowing the designer to move from
the generative to the declarative mode as a project matures.  The
generative mode also allows for the verification of legacy code that was not
originally designed with the |SPARK| contracts in mind.

|GNATprove| supports both approaches. |GNATprove| can compute the data
dependences of subprograms both inside and outside of |SPARK|.

Assumptions of Verification Results
-----------------------------------

Provided with the option ``--assumptions``, |GNATprove| computes the remaining
assumptions of all verification results and outputs these assumptions into the
file ``gnatprove.out``, along with the verification results. Here, assumptions
are properties of subprograms which |GNATprove| could not check itself, for
example because the subprogram has not been analyzed (not in the |SPARK|
subset, disabled using ``SPARK_Mode``), or because the analysis could not
establish that the subprogram actually has the property (unproved checks).

Note that currently, only assumptions on called subprograms are output, and
not assumptions on calling subprograms.

The following table explains the meaning of assumptions and claims which
gnatprove may output:

.. tabularcolumns:: |l|p{4.5in}|

.. csv-table::
   :header: "Assumption", "Explanation"
   :widths: 2, 4

    "effects on parameters and global variables", "the subprogram does not read or write any other parameters or global variables than what is described by its Global contract"
    "absence of run-time errors", "the subprogram does not contain any run-time errors such as overflow check, division checks, etc."
    "the postcondition", "the postconditon of the subprogram holds after each call of the subprogram"

Compilation Options to Support Integration of Test and Proof
------------------------------------------------------------

..
   In order to combine formal verification with testing, the program should
   respect a number of restrictions, even on code that is not in |SPARK|. These
   restrictions are:

   .. code-block:: ada

      pragma Restrictions (
               No_Access_Subprograms,
               No_Finalization,
               No_Implicit_Aliasing);

Special switches add run-time checks to verify dynamically the
assumptions made during formal verification:

 * ``-gnateA`` adds checks that parameters are not aliased
 * ``-gnateV`` adds checks that parameters are valid, including parameters of
   composite types (arrays, records)
 * ``-gnatVa`` adds checks that objects are valid at more places than -gnateV,
   but only for scalar objects

Test Cases
----------

Although testing is not exhaustive by nature, contrary to proof, it is meant to
explore enough possibilities to gain confidence in the program. Safety and
security standards mandate which possibilities must be explored: functional
properties related to the low-level requirements, and robustness tests
with boundary values.

A formal test case is a GNAT extension to Ada meant to
facilitate the formalization of test cases. It can be expressed either as an
aspect in Ada 2012 or as a pragma in all Ada modes (83, 95, 2005, 2012). A
formal test case is attached to a subprogram declaration for a subprogram
declared in a package specification inside a package spec unit.  The syntax of
test case pragmas is the following:

.. code-block:: ada

   pragma Test_Case (
      [Name     =>] static_string_Expression
     ,[Mode     =>] (Nominal | Robustness)
    [, Requires =>  Boolean_Expression]
    [, Ensures  =>  Boolean_Expression]);

The compiler checks the validity of this pragma but its presence does not lead
to any modification of the code generated by the compiler. See the |GNAT Pro|
Reference Manual for more details. The following is an example of use within a
package spec:

.. code-block:: ada
   :linenos:

   package Math_Functions is
      ...
      function Sqrt (Arg : Float) return Float;
      pragma Test_Case (Name     => "Test 1",
                        Mode     => Nominal,
                        Requires => Arg < 10000,
                        Ensures  => Sqrt'Result < 10);
      ...
   end Math_Functions;

The meaning of a test case is that, for a set of inputs carefully chosen,
``Requires`` should hold on entry to the subprogram, and ``Ensures`` should
hold when the subprogram returns.

Mode ``Nominal`` indicates that the input context should satisfy the normal
precondition of the subprogram, and the output context should then satisfy its
postcondition. Mode ``Robustness`` indicates that the normal pre- and
postcondition of the subprogram should be ignored.

Functional Behavior
^^^^^^^^^^^^^^^^^^^

With ``Nominal`` mode, the user can partition the input state space using
the ``Requires`` components. No ``Ensures`` component is necessary in that
case. Of course, the user can also strengthen the expected postcondition after
the subprogram executes on a certain contract case or test case by adding a
``Requires`` component.

By default, GNATtest generates a test harness with individual test skeletons
for every test case in the program.
Initially, these test procedures are empty. The user can then fill in the test
procedures with the definition of proper inputs for the test and a call to the
subprogram under test. The harness takes care of checking automatically at
run-time that a test procedure correctly implements the corresponding test
case, and that all assertions in contracts cases and test cases are valid.

GNATtest generates an executable in order to run the test suite. During the
run, this executable generates a report with successful and failing tests.

Absence of Run-Time Errors
^^^^^^^^^^^^^^^^^^^^^^^^^^

With ``Robustness`` mode, the user can specify exceptional behavior in case the
precondition is not fulfilled. During all runs of both ``Nominal`` and
``Robustness`` test cases, run-time checks are performed to
detect potential run-time errors. Such errors are reported as failed tests in
the final report.
