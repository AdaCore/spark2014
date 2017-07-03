
Internally Generate Aspects And Bless Them
------------------------------------------

:ID: UC.InternallyGenerateAspects.Bless
:Overview: Tools automatically introduce SPARK 2014 aspects after processing the body.
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

#.  The code is "in SPARK 2014" and GNATprove can generate relations upon reading the body.

    #. The tools automatically augment the source code with SPARK 2014 aspects (user has to request that).

    #. An internal augmented version of the code is produced. This internal version is used insted of the original (this allows analysis to proceed even when code does not include SPARK 2014 aspects).

Scenario Notes
^^^^^^^^^^^^^^

Can these features actually be implemented?

Postcondition
^^^^^^^^^^^^^

#. Based on the relations that GNATprove generates after processing the body, the tools automatically introduce SPARK 2014 aspects at both the specifications and body of the package.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
The body is not "in SPARK 2014" and thus GNATprove cannot generate relations.

Special Requirements
^^^^^^^^^^^^^^^^^^^^

Are there additional restrictions that should be imposed on the user's code?

