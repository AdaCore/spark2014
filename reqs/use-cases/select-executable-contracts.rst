
Select Executable Contracts
---------------------------

:ID: UC.Select.ExecutableContracts
:Overview: The user shall be able to turn on and off execution of contracts.
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

Scenario Notes
^^^^^^^^^^^^^^

Units that are tested will need to execute the precondition of formally verified units prior to calling them. 

Postcondition
^^^^^^^^^^^^^

#. The binary generated includes executable contracts for only those contracts selected to be executable.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#. The user is given an error message if contracts intended to be executable contain non-executable proof function.

Special Requirements
^^^^^^^^^^^^^^^^^^^^
None.


