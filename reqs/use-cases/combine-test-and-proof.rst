
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

#. :ref:`uc-check-subset` postcondition holds for a program that contains units intended to be verified through test and for units intended to be verified through formal proof.

Scenario
^^^^^^^^

#. The user turns on execution of contracts for units that are intended to be tested.
#. The user turns off execution of contracts for units that are intended to be formally verified.
#. The user tests a subset of the units.
#. The user formally verifies the remaining units.

Scenario Notes
^^^^^^^^^^^^^^

#. Users are supported with guidance material to help them select the best combination of tested and formally proven units.
#. Units that are tested will need to execute the precondition of formally verified units prior to calling them. 

Postcondition
^^^^^^^^^^^^^

#. The binary generated includes executable contracts for only those contracts selected to be executable.
#. The proof logs include a list of the assumptions made about the tested code.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#. The user is given an error message if contracts intended to be executable contain non-executable proof functions.

Special Requirements
^^^^^^^^^^^^^^^^^^^^
None.


