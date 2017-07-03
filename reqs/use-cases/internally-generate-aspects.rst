
Internally Generate Aspects
---------------------------

:ID: UC.InternallyGenerateAspects
:Overview: Tools internally generate SPARK 2014 aspects after processing the body.
:Target Rel: rel1
:Priority: Required
:Part of: Base Product
:Current users: None
:Future users: TBC

Precondition
^^^^^^^^^^^^

#.  The specifications and body of a package are present and no |SPARK| aspects exist in them.
#.  |SPARK| aspects may exist on operations used by operations that do not have |SPARK| aspects.

Scenario
^^^^^^^^

#. User provides the specifications and body of a package without having included any |SPARK| aspects.
#. All code is "in SPARK 2014" and GNATprove can generate global and dependency relationships where they do not exist. 
#. Where global and dependency relationships have been specified by the user, these are used by the |SPARK tools| and the body ignored.
#. The aggregation of user and tool generated relationships are used for modular flow analysis.

Scenario Notes
^^^^^^^^^^^^^^

None.

Postcondition
^^^^^^^^^^^^^

#. Flow analysis of the entire program can be carried out at a modular level.


Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
The body is not "in SPARK 2014" and thus GNATprove cannot generate relations.

Special Requirements
^^^^^^^^^^^^^^^^^^^^

Are there additional restrictions that should be imposed on the user's code?

