
Analyse Data Flow
-----------------

:ID: UC.AnalyseDataFlow
:Overview:
    Check the data flow of all |SPARK| bodies.

:Target Rel: rel1
:Priority: Required
:Part of: Base Product
:Current users: All
:Future users: All

Precondition
^^^^^^^^^^^^

uc-check-subset_ postcondition is true.

Developer has attempted to write source code that is |SPARK|. The following All |SPARK| aspects are used:
* Globals with in/out defined

Scenario
^^^^^^^^
#. Developer requests source code is checked against |SPARK|;

#. |SPARK tools| reports if the code contains any:
    * uninitialized variables;

    * unused variables;

    * stable loops;

    * ineffective statements; or

    * ineffective imported variables.

#. Developer manually fixes all data flow errors; and

#. Repeat until postcondition met.


Scenario Notes
^^^^^^^^^^^^^^

None.

Postcondition
^^^^^^^^^^^^^

#. Source code is compliant with |SPARK|; and

#. |SPARK tools| does not report any flow errors.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
None.


Special Requirements
^^^^^^^^^^^^^^^^^^^^
.. todo:: Are there any limitations on the complexity of the source code?


