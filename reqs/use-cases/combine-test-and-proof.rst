
Combine Test and Proof
----------------------

:ID: UC.CombineTestAndProof
:Overview: The user shall be able to demonstrate that a program that has been verified using a combination of test and proof is at least as well verified as if it had been completely tested. This approach is intended to meet the objectives of DO-178C in relation to verifying low-level requirements, where those low-level requirements are written in the code as pre and post conditions. We first try to verify via formal proof and, where this cannot be done, then we verify using test.


:Target Rel: |rel1|
:Priority: Required
:Part of: Base Product
:Current users:
:Future users:

Precondition
^^^^^^^^^^^^

#. It is feasible to represent the low-level requirements in the code as pre and post conditions,
   and that has been done.
#. All postconditions hold from :ref:`uc-check-subset`.
#. All postconditions hold from :ref:`uc-analyse-data-flow`.
#. Guidance is available on allocating verification tasks between test and proof, including
   on passing units to the test team when proof has been unsuccessful.
#. The properties are known that must be preserved by tested code so that the results of formal
   verification are not invalidated.
#. Procedures and tool support are available for combining the results of test and proof,
   and feeding those results back to the user.


Scenario
^^^^^^^^

#. Decide which units are to be formally verified and which are to be formally tested.

#. Execute the use case :ref:`uc-formally-verify` for the units to be formally verified
   and identify all units for which formal verification was unsuccessful.

#. TBD: provide additional steps in relation to conditions under which units
   can be passed to the test team.

#. On the failure of proof for a given unit:

   * Ensure that developer testing has been performed.

   * Ensure all contracts on code to be tested are executable, as are pre-conditions where
     tested calls proven code.

   * Ensure the code to be tested does not violate any of the assumptions on which formal
     verification depends.

   * Pass the code to the test team (where it may be necessary for the testers to be
     independent of the developers, depending on the DO-178C assurance level) and execute
     the use case :ref:`uc-perform-testing`.

#. On completion of testing, the results from formal verification and testing are
   combined and presented to the user.

#. Note that this process is iterative and so during this process both developers and testers
   will find errors in the code and in the tests that will need to be fixed.

Scenario Notes
^^^^^^^^^^^^^^

#. TBD: full details on the technical requirements when combining test and proof are still to
   be worked out, and these may have an impact on this use case and also :ref:`uc-perform-testing`.

#. Users are supported with guidance material to help them select the best combination of tested and
   formally proven units.
#. Users are supported with guidance material to indicate which contracts must be formally verified
   and which must be tested on the basis of the designation of units to formal verification and test
   (for example, units that are tested will need to execute the preconditions of formally verified units
   prior to calling them).
   
#. The process of performing test and proof, and of passing code and results between the development
   and test teams will be iterative to an extent that it is not necessary to represent directly
   in this use case.

Postcondition
^^^^^^^^^^^^^

#. Each subprogram is either formally verified or tested.
#. All formal verification and testing is successful.
#. There is no interference between tested code and proven code, and tested code
   supports all the assumptions made when proving code.
#. The proof logs include a list of the assumptions made about the tested code.
#. Hence, the needs of DO-178C in relation to verifying low-level requirements are all met.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#. The user is given an error message if contracts intended to be executable contain non-executable
   proof functions.
#. The code to be tested violates one or more of the assumptions on which formal verification depends.


Special Requirements
^^^^^^^^^^^^^^^^^^^^
None.

