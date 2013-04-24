
Discharge VCs Manually
----------------------

:ID: UC.ManualProof
:Overview: Users should be able to manually discharge VCs when automatic provers are unable to.
:Target Rel: |rel1|
:Priority: Required
:Part of: Advanced Proof Add-On
:Current users:
:Future users:

Precondition
^^^^^^^^^^^^

#. :ref:`uc-check-subset` postcondition is true.
#. Program includes bodies.
#. There are some VCs that are not discharged by the automatic provers.

Scenario
^^^^^^^^

#. The |SPARK tools| identifies VCs that have not been discharged.
#. For each such VC it provides hypotheses and goals in human-readable form, and in a form that
   can be imported into a manual proof tool.
#. User considers VCs to be provable given the hypotheses available.
#. If the user can identify proof rules that would allow some of these VCs to be proved by the |SPARK tools|
   then those rules are supplied as input to the |SPARK tools| and use case
   :ref:`uc-formally-verify` is executed again.
#. If the user can identify VCs that are provable and are safe to be discharged by review, then
   use case :ref:`uc-use-prv-files` is executed.
#. If there are any remaining undischarged VCs then the user uses an external manual proof tool
   to discharge them.

Scenario Notes
^^^^^^^^^^^^^^

The manual proof tool is not part of the |SPARK tools| and may be one of a number of tools.

Postcondition
^^^^^^^^^^^^^

#. Undischarged VCs proven.
#. Record of undischarged VCs updated to remove manually proven VCs (including VCs proved by review).
#. List of manually-proven VCs maintained, so that they don't need to be reproven every time.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#. Undischarged VCs not proven.

Special Requirements
^^^^^^^^^^^^^^^^^^^^
None.


