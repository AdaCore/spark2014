
Perform Testing
---------------

:ID: UC.PerformTesting
:Overview:
    Use case :ref:`uc-combine-test-and-proof` allows for the mixing of formal verification and test in order to meet the objectives of DO-178C in relation to verifying low-level requirements. This use case provides the detail on performing testing where formal verification is not possible or is undesirable.


:Target Rel: rel1
:Priority: Required
:Part of: Base Product
:Current users:
:Future users:

Precondition
^^^^^^^^^^^^

#. All pre-conditions from :ref:`uc-combine-test-and-proof` are met.

#. All contracts on code to be tested are executable, as are pre-conditions where
   tested calls proven code.

#. All code to be tested has already been developer tested.

#. The code to be tested does not violate any of the assumptions on which successful formal
   verification depends.

Scenario
^^^^^^^^

#. Turn on execution of contracts for units that are intended to be tested.

#. Turn off execution of contracts for units that have been sucessfully formally verified.

#. Write tests to test the low-level requirements for the relevant units, and to check
   the anti-aliasing rules and pre-conditions when tested code calls proven code.

#. Run tests and collect results (TBD: how exactly do we use the contracts when executing tests).

#. Repeat until post-condition is met (which will involve input from developers and also
   iteration with :ref:`uc-combine-test-and-proof`).


Scenario Notes
^^^^^^^^^^^^^^

#. The detail under this use case assumes the pre and post conditions representing
   the low-level requirements will be used during testing. However, the details of how
   exactly this will be done are still to be worked out.

Postcondition
^^^^^^^^^^^^^

#. The needs of DO-178C in relation to testing of low-level requirements are met for the
   tested units.

#. The anti-aliasing rules and subprogram pre-conditions are met when tested code calls proven code.

#. Test results are available in a form that can be combined with the results of formal
   verification.


Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
None.


Special Requirements
^^^^^^^^^^^^^^^^^^^^
None








