
.. _specification:

Specification Statements
========================

|SPARK| language features
-------------------------

.. _S.Lang.ExtendAda2012:

S.Lang.ExtendAda2012
^^^^^^^^^^^^^^^^^^^^

:Description: |SPARK| shall be an extension of Ada 2012 which uses Ada 2012 constructs.
:Use Cases: None

.. _S.Lang.MinimiseRestrictions:

S.Lang.MinimiseRestrictions
^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: |SPARK| shall minimise the restrictions of Ada 2012 such that the largest subset of Ada 2012 to which it is currently practical to apply automatic verification is provided.
:Use Cases: None

.. _S.Lang.UndefinedBehaviour.SupportDetection:

S.Lang.UndefinedBehaviour.SupportDetection
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: |SPARK| shall be designed to support the static detection of undefined program behaviour.
:Use Cases: 

   :ref:`uc-check-subset` 

   :ref:`uc-analyse-data-flow` 

   :ref:`uc-prove-no-rte`


.. _S.Lang.CombineTestAndProof:

S.Lang.CombineTestAndProof
^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The language shall support combining programs that are verified using a combination of test and proof.
:Rationale: The assumptions associated with calling a proven program from a tested program and visa versa need to be documented.
:SA: :ref:`SA.Mixed.Verification`

.. _S.Lang.ExecutableContracts:

S.Lang.ExecutableContracts
^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The language shall support executable contracts although such contracts may be less expressive.
:Rationale: Executable contracts support testing of units but some use cases require the use of externally defined proof functions which are not executable.
:SA: :ref:`SA.Mixed.Verification`

.. _S.Lang.MultiTask:

S.Lang.MultiTask
^^^^^^^^^^^^^^^^
:Description: The language shall support Ada programs containing more than one task.
:Rationale: Many users require multiple tasks.
:Use Cases: TBC

.. _S.Lang.SecurityProperties:

S.Lang.SecurityProperties
^^^^^^^^^^^^^^^^^^^^^^^^^
:Description: The language shall support the specification of security properties.
:Rationale: The client base includes a number of customers specifically interested in proving security properties.
:Use Cases: TBC

.. _S.Lang.ToolNeutral:

S.Lang.ToolNeutral
^^^^^^^^^^^^^^^^^^

:Descrption: The language shall be written such that it does not rely on tool specific features.
:Rationale: 
   The language definition must allow specifications to be written so that the same source files can be processed by a variety of analysis and verification tools, including, but not limited to: 

   #. a compiler component or other tool enabling runtime checking;
   #. test case generation;
   #. VCGen based static verification;
   #. Symbolic Execution;
   #. full functional verification with discharging of proof obligations manually handled by users using external provers (like Coq and Isabelle).

:Use Cases: TBC

|SPARK tools| libraries
-----------------------

.. _S.Containers:

S.Containers
^^^^^^^^^^^^

:Description: Ada Containers shall be usable by |SPARK| programs.
:Use Cases: None.

.. _S.Libraries.Text_IO:

S.Libraries.Text_IO
^^^^^^^^^^^^^^^^^^^

:Description: The Ada.Text_IO Libraries shall be usable by |SPARK| programs.
:Use Cases: None.


|SPARK tools| behaviour
-----------------------

.. _S.Tool.SyntaxCheck:

S.Tool.SyntaxCheck
^^^^^^^^^^^^^^^^^^
:Description: The |SPARK tools| shall check that a program conforms with the |SPARK| syntax.
:Use Cases: 

   :ref:`uc-check-subset` 

.. _S.Tool.LegalityRuleCheck:

S.Tool.LegalityRuleCheck
^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The |SPARK tools| shall check that a program conforms with the |SPARK| legality rules.
:Rationale: Automated checking removes effort from the user.
:Use Cases: 

   :ref:`uc-check-subset` 


.. _S.Tool.VerificationRuleCheck:

S.Tool.VerificationRuleCheck
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The |SPARK tools| shall check that a program conforms with the |SPARK| verification rules.
:Rationale: Automated checking removes effort from the user.
:Use Cases: 

   :ref:`uc-check-subset` 

S.Tool.EnableExecutableContracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The |SPARK tools| shall check that a program conforms with the |SPARK| verification rules.
:Rationale: Automated checking removes effort from the user.
:Use Cases: 

   :ref:`uc-check-subset` 
   


.. _S.IFA.DataFlow.Subprogram:

S.IFA.DataFlow.Subprogram
^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The tools shall analyse the data flow of an operation body and identify the following errors:

   #. uninitialized variables;
   #. unused variables;
   #. stable loops;
   #. ineffective statements; and
   #. ineffective imported variables.

:Rationale: Identifies coding issues that may lead to undefined behaviour.
:Use Cases: :ref:`uc-analyse-data-flow`

.. _S.IFA.DataFlow.InterProcedural:

S.IFA.DataFlow.InterProcedural
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The tools shall analyse the data flow of an entire body and identify the following errors:

   #. uninitialized variables;
   #. unused variables;
   #. stable loops;
   #. ineffective statements; and
   #. ineffective imported variables.

:Rationale: Identifies coding issues that may lead to undefined behaviour.
:Use Cases: :ref:`uc-analyse-data-flow`




.. _S.IFA.InformationFlow:

S.IFA.InformationFlow
^^^^^^^^^^^^^^^^^^^^^

:Description: The tools shall analyse the information flow of a program body and compare it to the user specified information flow, where it exists.
:Rationale: Supports modular development.
:Use Cases: :ref:`uc-analyse-information-flow`

.. _S.Proof.AutomateAoRTE:

S.Proof.AutomateAoRTE
^^^^^^^^^^^^^^^^^^^^^
:Description: It shall be possible to automatically prove the absence of the following run-time errors:

#. Constraint error;
#. Array indexing error;
#. TBC

:Rationale: Automatic proof reduces the skillset required by developers to formally prove their programs.
:Use Cases: :ref:`uc-prove-no-rte`

.. _S.Proof.Manual:

S.Proof.Manual
^^^^^^^^^^^^^^

:Description: It shall be possible to manually prove VCs.
:Rationale: This provides flexibility to resolve proofs which aren't currently automatable.
:Use Cases: TBC

.. _S.Proof.FunctionalSpec:

S.Proof.FunctionalSpec
^^^^^^^^^^^^^^^^^^^^^^

:Description: It shall be possible to prove (using a combination of automatic and manual analysis) the functional properties of an operation body against its contracts.
:Rationale: This supports for formal proof.
:Use Cases: TBC

.. _S.Proof.RecordProofAssumptions:

S.Proof.RecordProofAssumptions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: Where the proof tools assume properties of aspects of a program that is not subject to formal proof, those properties shall be recorded.
:SA: :ref:`SA.Mixed.Verification`


|SPARK tools| outputs
---------------------

.. _S.Outputs.VCSummary:

S.Ouputs.VCSummary
^^^^^^^^^^^^^^^^^^

:Description: A summary of discharged and non-discharged VCs shall be produced.
:Rationale: This helps developers to see how far through the proof task they are.
:Use Cases: :ref:`uc-summarise-outstanding-vcs`


Process constraints
-------------------

Documentation
-------------

.. _S.WhitePaper.CombineTestAndProof:

S.WhitePaper.CombineTestAndProof
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: There shall be guidance describing how test and formal proof can be combined using the |SPARK| features that support executable contracts and recording proof assumptions associated with the boundary between formally proven units and tested units.
:Rationale: Users need support with using novel features of |SPARK|.
:SA: :ref:`SA.Mixed.Verification`


