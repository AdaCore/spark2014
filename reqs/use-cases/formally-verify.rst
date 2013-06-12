
Formally Verify
---------------

:ID: UC.FormallyVerify
:Overview:
    Perform formal verification of all |SPARK| bodies. Note that the detail on this use case has only been partially populated.

:Target Rel: |rel1|
:Priority: Required
:Part of: Base Product
:Current users: All
:Future users: All

Precondition
^^^^^^^^^^^^

#. All postconditions hold from :ref:`uc-check-subset`.

#. All postconditions hold from :ref:`uc-analyse-data-flow`.

#. Guidance is available on strategies for debugging failed proof attempts.

Scenario
^^^^^^^^

TBD


Scenario Notes
^^^^^^^^^^^^^^

#. Unsuccessful proof attempts must be debugged and the proof attempted again.
   Various strategies can be applied - up to and including refactoring code - until
   it is accepted that the relevant subprogram cannot be formally verified.

TBD

Postcondition
^^^^^^^^^^^^^

#. Either all VCs discharged and so all necessary subprograms are formally verified;

#. Or SPARK 2014 framework identifies undischarged VCs and assertions (including preconditions and
   postconditions) that failed proof. (When this use case is invoked from :ref:`uc-combine-test-and-proof`,
   it may not be possible to prove all of the units on which formal verification is attempted. In this
   case, the relevant units will be passed to the test team for testing.)

TBD

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD


Special Requirements
^^^^^^^^^^^^^^^^^^^^
.. todo:: Are there any limitations on the complexity of the source code?


