

Check source against |SPARK|
----------------------------

:ID: UC.CheckSubset
:Overview:
    Check that the source code complies with the SPARK LRM Subset and rules where all code should be "in" |SPARK|.
:Target Rel: rel1
:Priority: Required
:Part of: Base Product
:Current users: All
:Future users: All

Precondition
^^^^^^^^^^^^
Developer has attempted to write source code that is |SPARK|. The following All |SPARK| aspects are used:
* None.

Scenario
^^^^^^^^
#. Developer requests source code is checked against |SPARK|;
#. |SPARK tools| reports any non-compliances with |SPARK|;
#. Developer manually fixes all non-compliances; and
#. Repeat until postcondition met.


Scenario Notes
^^^^^^^^^^^^^^

The |SPARK tools| will carry out flow analysis automatically but this is excluded from this scenario.


.. _uc-check-subset_ postcondition:

Postcondition
^^^^^^^^^^^^^

* Source code is compliant with |SPARK|
* |SPARK tools| does not report any non-compliances against the |SPARK| subset

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Any use of non-|SPARK| language features are reported as errors.


Special Requirements
^^^^^^^^^^^^^^^^^^^^
.. todo:: Are there any limitations on the size of source code?


