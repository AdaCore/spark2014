
.. _reqs:

Requirements
============


This section presents the requirements and then, in `Requirements Satisfaction`_, provides an argument for how the requirement has been met. This is achived through a requirements satisfaction argument which uses specification and domain knowledge statements to demonstrate compliance. Use Cases may be referenced to provide a wider perspective of the requirement.

|SPARK| Requirements
^^^^^^^^^^^^^^^^^^^^

.. _Req.MaintainSPARK.Features:

Req.MaintainSPARK.Features
--------------------------

:Description: The features of SPARK 2005 shall be maintained in |SPARK|.
:Rationale: Provide continuity for current users and ensure best practice is not lost.
:Use Cases: 

   :ref:`uc-check-subset` 

   :ref:`uc-analyse-data-flow` 

   :ref:`uc-prove-no-rte`

   :ref:`uc-analyse-information-flow`   

:SA: :ref:`SA.MaintainSPARK.Features`



.. _Req.ExtendSPARK.Ada2012:

Req.ExtendSPARK.Ada2012
-----------------------

:Description: SPARK 2005 and its toolset shall be extended to embody the largest subset of Ada 2012 to which it is currently practical to apply automatic formal verification.
:Rationale: The Ada language and theoretical bases for static analysis have progressed and SPARK also needs to progress.
:Use Cases: None.
:SA: :ref:`SA.ExtendSPARK.Ada2012`


.. _Req.ExtendAda.AdaConstructs:

Req.ExtendAda.AdaConstructs
---------------------------

:Description: All Ada2012 extensions shall be encoded using Ada 2012 language constructs (e.g. aspects).
:Rationale: Ada2012 was designed to be extended and so should be extended in the way it has been designed to be.
:Use Cases: TBC

.. _Req.ExtendAda.Compilable:

Req.ExtendAda.Compilable
------------------------

:Description: |SPARK| programs shall be compilable by any Ada 2012 compliant compiler.
:Rationale: The |SPARK| language shall not force users to use a specific compiler.
:Use Cases: TBC


.. _Req.ExtendSPARK.Libraries:

Req.ExtendSPARK.Libraries
-------------------------

:Description: Ada Libraries and Containers shall be useable within |SPARK| programs.
:Rationale: |SPARK| programs shall be able to use the standard Ada libraries and containers.
:Use Cases: TBC

.. _Req.RestrictSPARK:

Req.RestrictSPARK
-----------------

:Description: It shall be possible to restrict the subset of Ada further through domain and user specific code policies.
:Rationale: SPARK 2005 users are likely to require similar limitations in |SPARK|.
:Use Cases: TBC



.. _Req.Mixed.DevelopmentMethods:

Req.Mixed.DevelopmentMethods
----------------------------

:Description: Users shall have the flexibility to use combinations of contract specifications with minimal impact on the amount of static analysis that can be carried out.
:Rationale: Static analysis tools shall maximise the value of the analysis that can be carried out.
:Use Cases: TBC

.. _Req.Mixed.Code:

Req.Mixed.Code
--------------

:Description: It shall be possible to develop programs that contain a mixture of SPARK and non-SPARK code.
:Rationale: Users need to be able to write just the core of their programs in SPARK.
:Use Cases: TBC

.. _Req.Mixed.Verification:

Req.Mixed.Verification
----------------------

:Description: It shall be possible to combine formal verification and test evidence.
:Rationale: Users need to be able to choose the most efficient method of verifying their programs.
:Use Cases: 

   :ref:`uc-combine-test-and-proof`

:SA: :ref:`SA.Mixed.Verification`


.. _Req.Contracts.Mix.ExecutableAndNonExecutable:

Req.Contracts.Mix.ExecutableAndNonExecutable
--------------------------------------------

:Description: Users shall be able to choose to execute their contracts. When contracts are not executed there shall be no additional object code generated to support proof.
:Rationale: 
:Use Cases: :ref:`uc-combine-test-and-proof`

.. _Req.Soundness:

Req.Soundness
-------------

:Description: The analysis of programs shall be sound.
:Rationale: The analysis never asserts a property to be true when it is not true. 
:Use Cases: TBC

.. _Req.Support.Ceritifcation:

Req.Support.Certifcation
------------------------

:Description: |SPARK| shall reduce the cost of software certification through the application of static analysis and the demonstration that those techniques are sound.
:Rationale: Users of SPARK often work in regulated industries where the specific properties of programs have to be demonstrated either manually or automatically. When demonstrated automatically, the tools used must have been developed to specific standards.

.. _Req.Usability.MaximiseTechRefresh:

Req.Usability.MaximiseTechRefresh
---------------------------------

:Description: Where possible, the static analysis tools shall utilise the features of the existing AdaCore toolset to improve the user experience.
:Rationale: The technology refresh provides an opportunity to provide a much more integrated user experience.
:Use Cases: TBC

.. _Req.Usability.MinimiseTraining:

Req.Usability.MinimiseTraining
------------------------------

:Description: It shall be possible to formally analyse programs without training in formal methods.
:Rationale: Maximise the uptake of formal methods.
:Use Cases: TBC

.. _Req.Usability.EasyToUnderstand:

Req.Usability.EasyToUnderstand
-------------------------------

:Description: Contracts should be as easy to write, understand and maintain.
:Rationale: Supports maximising the use of |SPARK|.
:Use Cases: TBC

.. _Req.Usability.ExpressiveContracts:

Req.Usability.ExpressiveContracts
---------------------------------

:Description: Contracts should be expressive and support refinement.
:Rationale: Not withstanding :ref:`Req.Usability.EasyToUnderstand`, the syntax for contracts needs to support full functional specification.
:Use Cases: TBC

Requirements Satisfaction
^^^^^^^^^^^^^^^^^^^^^^^^^

.. _SA.MaintainSPARK.Features:

SA.MaintainSPARK.Features
-------------------------

:Req: :ref:`Req.MaintainSPARK.Features`
:Argument: TBC
:Use Cases: TBC


.. _SA.ExtendSPARK.Ada2012:

SA.ExtendSPARK.Ada2012
----------------------

:Req: :ref:`Req.ExtendSPARK.Ada2012`
:Argument: This is wholly covered by :ref:`S.Lang.MinimiseRestrictions`.
:Use Cases: TBC

.. _SA.ExtendAda.AdaConstructs:

SA.ExtendAda.AdaConstructs
--------------------------

:Req: :ref:`Req.ExtendAda.AdaConstructs`
:Argument: This is wholly covered by :ref:`S.Lang.ExtendAda2012`.
:Use Cases: TBC

.. _SA.ExtendAda.Compilable:

SA.ExtendAda.Compilable
-----------------------

:Req: :ref:`Req.ExtendAda.Compilable`
:Argument: This is wholly covered by :ref:`S.Lang.ToolNeutral`.
:Use Cases: TBC


.. _SA.ExtendSPARK.Libraries:

SA.ExtendSPARK.Libraries
------------------------

:Req: :ref:`Req.ExtendSPARK.Libraries`
:Argument: Not all Ada Libraries will be supported immediately but Ada.Text_IO will be (:ref:`S.Libraries.Text_IO`) and some Containers will be (:ref:`S.Libraries.Text_IO`).
:Use Cases: TBC

.. _SA.RestrictSPARK:

SA.RestrictSPARK
----------------

:Req: :ref:`Req.RestrictSPARK`
:Argument: 
:Use Cases: TBC



.. _SA.Mixed.DevelopmentMethods:

SA.Mixed.DevelopmentMethods
---------------------------

:Req: :ref:`Req.Mixed.DevelopmentMethods`
:Argument: 
:Use Cases: TBC

.. _SA.Mixed.Code:

SA.Mixed.Code
-------------

:Req: :ref:`Req.Mixed.Code`
:Argument: 
:Use Cases: TBC

.. _SA.Mixed.Verification:

SA.Mixed.Verification
---------------------

:Req: :ref:`Req.Mixed.Verification`
:Argument: The |SPARK| language specification supports mixed verification through :ref:`S.Lang.CombineTestAndProof` and :ref:`S.Lang.ExecutableContracts`. The tooling supports this by recording the proof assumptions used to discharge verification conditions associated with the boundary between formally proven and tested units (:ref:`S.Proof.RecordProofAssumptions`). A "white paper" will be written explaining how these features can be used to reduce development costs (:ref:`S.WhitePaper.CombineTestAndProof`).

.. Todo: insert a reference to a tooling specification.

.. _SA.Contracts.Mix.ExecutableAndNonExecutable:

SA.Contracts.Mix.ExecutableAndNonExecutable
-------------------------------------------

:Req: :ref:`Req.Contracts.Mix.ExecutableAndNonExecutable`
:Argument: 
:Use Cases: TBC

.. _SA.Soundness:

SA.Soundness
------------

:Req: :ref:`Req.Soundness`
:Argument: 
:Use Cases: TBC

.. _SA.Usability.MaximiseTechRefresh:

SA.Usability.MaximiseTechRefresh
--------------------------------

:Req: :ref:`Req.Usability.MaximiseTechRefresh`
:Argument: 
:Use Cases: TBC

.. _SA.Usability.MinimiseTraining:

SA.Usability.MinimiseTraining
-----------------------------

:Req: :ref:`Req.Usability.MinimiseTraining`
:Argument: 
:Use Cases: TBC

.. _SA.Usability.EasyToUnderstand:

SA.Usability.EasyToUnderstand
-----------------------------

:Req: :ref:`Req.Usability.EasyToUnderstand`
:Argument: 
:Use Cases: TBC

.. _SA.Usability.ExpressiveContracts:

SA.Usability.ExpressiveContracts
--------------------------------

:Req: :ref:`Req.Usability.ExpressiveContracts`
:Argument: 
:Use Cases: TBC


