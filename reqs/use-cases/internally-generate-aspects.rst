
Internally Generate Aspects
---------------------------

:ID: UC.InternallyGenerateAspects
:Overview: Tools internally generate SPARK 2014 aspects after processing the body.
:Target Rel: rel2+
:Priority: Optional
:Part of: Base Product
:Current users: None
:Future users: TBC

Precondition
^^^^^^^^^^^^

#.  The specifications and body of a package are present and no SPARK 2014 aspects exist in them.

Scenario
^^^^^^^^

#.  User provides the specifications and body of a package without having included any SPARK 2014 aspects.
#.  The code is "in SPARK 2014" and GNATProve can generate relations upon reading the body.
#. These internal annotations are used for modular flow analysis.

Scenario Notes
^^^^^^^^^^^^^^

Can these features actually be implemented?

Postcondition
^^^^^^^^^^^^^

#. Flow analysis of the entire program can be carried out at a modular level.


Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
The body is not "in SPARK 2014" and thus GNATProve cannot generate relations.

Special Requirements
^^^^^^^^^^^^^^^^^^^^

Are there additional restrictions that should be imposed on the user's code?

