
Prove Absence of Run-Time Errors
--------------------------------

:ID: UC.AutomaticallyProve.AbsenceOfRTE
:Overview: Automatically prove the absence of Run-Time Errors in |SPARK| programs.
:Target Rel: |rel1|
:Priority: Required
:Part of: Base Product
:Current users:
:Future users:

Precondition
^^^^^^^^^^^^

#. :ref:`uc-check-subset` postcondition is true.
#. Program includes bodies.

Scenario
^^^^^^^^

#. Developer applies the |SPARK tools| to the a program body.
#. VCs are generated to discharge proof obligations associated with proof of absence of run-time errors.

Scenario Notes
^^^^^^^^^^^^^^

None.

Postcondition
^^^^^^^^^^^^^

#. VCs which are provable are discharged by the |SPARK tools|.
#. A summary of which VCs have been discharged and which VCs have not is provided.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. VCs which are not provable are not discharged by the |SPARK tools|. 
#. A summary of which VCs have been discharged and which VCs have not is provided.

Special Requirements
^^^^^^^^^^^^^^^^^^^^

None.



