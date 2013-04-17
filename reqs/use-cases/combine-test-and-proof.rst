
Combine Test and Proof
----------------------

:ID: UC.CombineTestAndProof
:Overview: The user shall be able to demonstrate that a program that has been verified using a combination of test and proof is at least as well verified as if it had been completely tested.

:Target Rel: |rel1|
:Priority: Required
:Part of: Base Product
:Current users:
:Future users:

Precondition
^^^^^^^^^^^^

#. :ref:`uc-check-subset` postcondition holds for a program that contains units
   intended to be verified through test and for units intended to be verified through formal proof.
#. In order for formal verification to be a substitute for conventional testing via this approach,
   the preconditions and postconditions of the code must express the expected outcomes that would
   be defined as part of a conventional testing approach.

Scenario
^^^^^^^^
#. Decide which units are to be formally verified and which are to be formally tested.
#. Confirm that the code to be tested does not violate any of the assumptions on which successful formal
   verification depends.
#. Turn on execution of contracts for units that are intended to be tested.
#. Turn off execution of contracts for units that are intended to be formally verified.
#. Test a subset of the units.
#. Formally verify the remaining units.
#. SPARK 2014 framework identifies undischarged VCs and assertions (including preconditions and
   postconditions) that failed test.
#. Confirm that each assertion (including preconditions and postconditions) that is not formally
   verified is executed during testing and that it is sufficiently covered.
#. Developer fixes all errors, including coverage errors.
#. Repeat until all tests pass and formal verification completes successfully.


Scenario Notes
^^^^^^^^^^^^^^

#. Users are supported with guidance material to help them select the best combination of tested and
   formally proven units.
#. Users are supported with guidance material to indicate which contracts must be formally verified
   and which must be tested on the basis of the designation of units to formal verification and test
   (for example, units that are tested will need to execute the preconditions of formally verified units
   prior to calling them).

Postcondition
^^^^^^^^^^^^^

#. The binary generated includes executable contracts for only those contracts selected to be executable.
#. All tests pass.
#. All formal verification completes successfully.
#. Testing provides sufficient coverage of assertions that are not formally verified.
#. The proof logs include a list of the assumptions made about the tested code.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#. The user is given an error message if contracts intended to be executable contain non-executable
   proof functions.
#. The code to be tested violates one or more of the assumptions on which formal verification depends.

Special Requirements
^^^^^^^^^^^^^^^^^^^^
None.


