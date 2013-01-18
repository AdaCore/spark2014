
Analyse Information Flow
------------------------

:ID: UC.AnalyseDataFlow
:Overview:
    Check that the executable code is consistent with its derives aspect.

:Target Rel: rel1
:Priority: Required
:Part of: Base Product
:Current users: All
:Future users: All

Precondition
^^^^^^^^^^^^

uc-analyse-data-flow_ postcondition is true.

Developer has attempted to write source code that is |SPARK|. The following All |SPARK| aspects are used:
* Derives.

Scenario
^^^^^^^^
#. Developer requests source code is checked against |SPARK|;
#. |SPARK tools| reports any information flow errors;
#. Developer manually fixes all information flow errors; and
#. Repeat until postcondition met.


Scenario Notes
^^^^^^^^^^^^^^

None.

Postcondition
^^^^^^^^^^^^^

# Source code is compliant with |SPARK|; and
# |SPARK tools| does not report any information flow errors.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
None.


Special Requirements
^^^^^^^^^^^^^^^^^^^^
.. todo:: Are there any limitations on the complexity of the source code?


