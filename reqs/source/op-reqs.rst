
Operational Reqs
================

See "Product Features" in https://docs.google.com/document/d/1DP5kKBWL5MdfrHmCFt2CEDJc3n6JfSHvGNGjwPz9j7U/edit#

**Copy in Patrice's reqs**

[Usability] S14 specification constructions should be as easy as possible to understand and use; implying ease in reading, writing and maintaining specifications.

[Expressive] S14 should be expressive, enabling/supporting a variety of verification technologies  ([VerifSuite]), in particular allowing the expression of full functional contracts and support for refinement.

[LangAbs] S14 specification constructs should represent concepts at the proper level of abstraction.


I have also heard the following requirements/constraints:


[AllExec] All specification constructs must be executable.
[Ada12Encoding] All S14 language constructs shall be encoded using Ada 2012 language constructs (mainly using aspects).
[Ada12Compiler] S14 annotated code must be compilable by any Ada 2012 compliant compiler.


Language design is an art in which one must balance competing requirements. Has a feature and requirements prioritization effort been made?

Based on previous discussions I get the impression that [AllExec], [Ada12Encoding] and [Ada12Compiler] are given priority over the other requirements stated above. IMHO, these are the wrong driving factors when it comes to language design. My research results on the semantics of assertions and integral arithmetic (wholeheartedly adopted by the Hi-Lite team :), were driven by [Usability], [LangAbs] and [Expressive] with careful consideration given to [VerifSuite].

My direct experiences in JML language and tool design, and indirect experiences with Spec#, strongly suggest that all requirements stated above can be justly prioritized by:

(1) Treating [AllExec] as secondary and, more importantly
(2) Forfeiting [Ada12Encoding] and/or [Ada12Compiler].

Stating (2) positively one could envision:

[NonStdSyntax] Allowing some constructs to be encoded outside of the Ada 2012 syntax, using stylized comments like in the current Spark is an example (thus preserving [Ada12Compiler]); or [ExtraExpansionPhase] Staying fully within the Ada 2012 syntax, but defining extra expansion phase in the compiler to map S14 constructs into a suitable representation in Ada 2012.

In fact, the Spec# compiler supports both [NonStdSyntax], via stylized comments (so that the sources can be compiled using the standard C# compiler), and [ExtraExpansionPhase] (added to the std C# compiler phase pipeline). Hence, the Spec# team left it up to the user to choose how he/she wished to encode specification constructs.  In JML we attempted to do the equivalent of [Ada12Encoding] and [Ada12Compiler] using Java 5 annotations, but gave up because the encoding became unwieldy and it became clear that end users would discouraged by having to use it.

Has feature and/or requirements prioritization been done?  If so, could the lists/artifacts be made available and open to discussion? If not, then I hope that this e-mail has reminded us of the need for such artifacts and discussions surrounding them (including getting feedback from all stakeholders such as current Spark customers).  My impression is that the current (implicit) feature prioritization is essentially asking users to do [ExtraExpansionPhase] in their heads as they attempt to write S14 specifications. We should not underestimate the adoption hurdle that is being raised by this. Hopefully, the issues being raised here are clear enough, if not, I will give concrete examples in subsequent e-mail(s) -- as this one has become long enough.



.. _Req.A.Template:

Req.A.Template

:Description: A description
:Rationale: A Rationale
:Use Cases: References to use cases


|SPARK| language features
-------------------------

.. _Req.Lang.UndefinedBehaviour.SupportDetection:

Req.Lang.UndefinedBehaviour.SupportDetection
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: |SPARK| shall be designed to support the static detection of undefined program behaviour.
:Rationale: Supports the goals.
:Use Cases: 

   :ref:`uc-check-subset` 

   :ref:`uc-analyse-data-flow` 

   :ref:`uc-prove-no-rte`


.. _Req.Lang.CombineTestAndProof:

Req.Lang.CombineTestAndProof
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The language shall support combining programs that are verified using a combination of test and proof.
:Rationale: The assumptions associated with calling a proven program from a tested program and visa versa need to be documented.
:Use Cases: TBC

.. _Req.Lang.MultiTask:

Req.Lang.MultiTask
^^^^^^^^^^^^^^^^^^
:Description: The language shall support Ada programs containing more than one task.
:Rationale: Many users require multiple tasks.
:Use Cases: TBC

.. _Req.Lang.SecurityProperties:

Req.Lang.SecurityProperties
^^^^^^^^^^^^^^^^^^^^^^^^^^^
:Description: The language shall support the specification of security properties.
:Rationale: The client base includes a number of customers specifically interested in proving security properties.
:Use Cases: TBC

Req.Lang.ToolNeutral
^^^^^^^^^^^^^^^^^^^^

:Descrption: The language shall be written such that it does not rely on tool specific features.
:Rationale: 
   The S14 language definition must allow specifications to be written so that the same source files can be processed by a variety of analysis and verification tools, including, but not limited to: 

   #. a compiler component or other tool enabling runtime checking;
   #. test case generation;
   #. VCGen based static verification;
   #. Symbolic Execution;
   #. full functional verification with discharging of proof obligations manually handled by users using external provers (like Coq and Isabelle).

:Use Cases: TBC



|SPARK tools| behaviour
-----------------------

.. _Req.Tool.SyntaxCheck:

Req.Tool.SyntaxCheck
^^^^^^^^^^^^^^^^^^^^
:Description: The |SPARK tools| shall check that a program conforms with the |SPARK| syntax.
:Rationale: Automated checking removes effort from the user.
:Use Cases: 

   :ref:`uc-check-subset` 

.. _Req.Tool.LegalityRuleCheck:

Req.Tool.LegalityRuleCheck
^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The |SPARK tools| shall check that a program conforms with the |SPARK| legality rules.
:Rationale: Automated checking removes effort from the user.
:Use Cases: 

   :ref:`uc-check-subset` 


.. _Req.Tool.VerificationRuleCheck:

Req.Tool.VerificationRuleCheck
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The |SPARK tools| shall check that a program conforms with the |SPARK| verification rules.
:Rationale: Automated checking removes effort from the user.
:Use Cases: 

   :ref:`uc-check-subset` 


.. _Req.IFA.DataFlow.Subprogram:

Req.IFA.DataFlow.Subprogram
^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The tools shall analyse the data flow of an operation body and identify the following errors:

   #. uninitialised variables;
   #. unused variables;
   #. stable loops;
   #. ineffective statements; and
   #. ineffective imported variables.

:Rationale: Identifies coding issues that may lead to undefined behaviour.
:Use Cases: :ref:`uc-analyse-data-flow`

.. _Req.IFA.DataFlow.InterProcedural:

Req.IFA.DataFlow.InterProcedural
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:Description: The tools shall analyse the data flow of an entire body and identify the following errors:

   #. uninitialised variables;
   #. unused variables;
   #. stable loops;
   #. ineffective statements; and
   #. ineffective imported variables.

:Rationale: Identifies coding issues that may lead to undefined behaviour.
:Use Cases: :ref:`uc-analyse-data-flow`




.. _Req.IFA.InformationFlow:

Req.IFA.InformationFlow
^^^^^^^^^^^^^^^^^^^^^^^

:Description: The tools shall analyse the information flow of a program body and compare it to the user specified information flow, where it exists.
:Rationale: Supports modular development.
:Use Cases: :ref:`uc-analyse-information-flow`

.. _Req.Proof.AutomateAoRTE:

Req.Proof.AutomateAoRTE
^^^^^^^^^^^^^^^^^^^^^^^
:Description: It shall be possible to automatically prove the absence of the following run-time errors:

#. Constraint error;
#. Array indexing error;
#. TBC

:Rationale: Automatic proof reduces the skillset required by developers to formally prove their programs.
:Use Cases: :ref:`uc-prove-no-rte`

.. _Req.Proof.Manual:

Req.Proof.Manual
^^^^^^^^^^^^^^^^

:Description: It shall be possible to manually prove VCs.
:Rationale: This provides flexibility to resolve proofs which aren't currently automatable.
:Use Cases: TBC

.. _Req.Proof.FunctionalSpec:

Req.Proof.FunctionalSpec
^^^^^^^^^^^^^^^^^^^^^^^^

:Description: It shall be possible to prove (using a combination of automatic and manual analysis) the functional properties of an operation body against its contracts.
:Rationale: This supports for formal proof.
:Use Cases: TBC



|SPARK tools| outputs
---------------------

Milestone 1
^^^^^^^^^^^

.. _Req.Outputs.VCSummary:

Req.Ouputs.VCSummary
^^^^^^^^^^^^^^^^^^^^

:Description: A summary of discharged and non-discharged VCs shall be produced.
:Rationale: This helps developers to see how far through the proof task they are.
:Use Cases: :ref:`uc-summarise-outstanding-vcs`


Process constraints
-------------------


