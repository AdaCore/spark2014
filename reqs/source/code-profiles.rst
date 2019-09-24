Code Profile High-Level Requirements
====================================

Introduction
------------

The detail below defines the high-level requirements for *Code Profiles*.
A *Code Profile* is composed of a set of *Policies*, where each *Policy* imposes
a limitation that code written under the Profile must respect.

Note that these requirements do not necessarily imply the need for a new language
feature or features. However, the term Policy is used so as not to imply that Policies
*have* to be implemented via pragma Restriction.

Example
-------

The most obvious example of a Profile that will be developed under the SPARK 2014 project
is *Strict SPARK*, which represents a useful subset of the limitations imposed by SPARK 2005.

Goal of the Strict SPARK Profile
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

That |SPARK| is designed to allow the largest subset of Ada amenable to formal verification
leads to a product offering quite distinct from the current SPARKPro toolset and language.
This is because limitations were imposed on the Ada 2005 subset allowable under SPARK 2005
for other reasons, such as:

#. Enforcing good programming practice;

#. Making code easier to read and understand;

#. Ensuring that the memory used by a program can be statically determined.

Hence, the Strict SPARK Profile will aim to meet the same goals as are met by SPARK 2005,
by imposing some of the restrictions imposed by SPARK 2005 (it will be possible, however,
to eliminate restrictions that were only present due to time or cost constraints).

Example Policies
~~~~~~~~~~~~~~~~

A Code Profile is composed of a number of Policies, where each Policy imposes
a restriction to be met by programs written by the user.

The following are example Policies that could be part of the Strict SPARK Profile.

No_Recursion
^^^^^^^^^^^^

Recursion shall be forbidden.

No_Default_Subprogram_Parameters
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This Policy prohibits the use of default subprogram parameters, that is, a
``parameter_specification`` cannot have a ``default_expression``.

Limited_Variable_Access_During_Elaboration
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

No variable declared immediately within another package can
be read or updated during elaboration of this package.

User-defined modifications
~~~~~~~~~~~~~~~~~~~~~~~~~~

Having defined the Strict SPARK Profile, some users might decide they need not
impose all Policies that it contains. For example, they might feel recursion should
be allowed and so the No_Recursion Policy is not needed. Hence, it should be possible
for users to define new Profiles (possibly based on modification of existing Profiles).

High-level goal
---------------

#. **Requirement**: It shall be possible to define a Code Profile or Profiles each of which defines
   a subset of the Ada 2012 language and mandate that programs respect a given
   Profile or Profiles.

   **Rationale**: In order to meet domain needs or certification requirements; or possibly to
   simplify proof or analysis. In addition, this allows the definition of a *Strict SPARK* Profile
   that imposes (some of) the restrictions imposed by SPARK 2005, but within a |SPARK| framework.

Defining a Profile
------------------

#. **Requirement**: It shall be possible to define Code Profiles in a modular fashion as a
   collection of individual Policies, where each Policy specifies
   an individual constraint to impose.

   **Rationale**: This allows greater flexibility and ease of defining Profiles (and allows
   users to define their own Profiles based on the existing set of Policies).

#. **Requirement**: It shall be possible to impose both syntactic and semantic constraints when
   defining a Code Profile [that is, it shall be possible to impose whatever
   constraints can be imposed when defining a language using the Ada RM structure).

   **Rationale**: A Profile effectively defines a language, and so should be expressed using the
   same type of rules as are used to define |SPARK|.

#. **Requirement**: It shall be possible to provide user-defined Profiles. *Note that we would
   expect to allow incrementing or decrementing existing Profiles rather than defining a
   completely new Profile.*

   **Rationale**: This provides greater flexibility for the user and means they are not simply
   tied into using the provided Profiles.

Applying Profiles
-----------------

#. **Requirement**:  It shall be possible to impose multiple Profiles simultaneously, the result
   being defined by the union of all the Policies contained within each Profile.

   **Rationale**:   To allow greater flexibility in imposing constraints on a given code base.

#. **Requirement**:  It shall be possible to impose a Profile or Profiles on a given code base
   at multiple levels of granularity (this will be partition-wide or program unit level).

   **Rationale**:   To allow the user maximum flexibility when applying a Profile.

#. **Requirement**: It shall be possible to accept deviations from a given Profile or Policy,
   and at a finer level of granularity than partition-wide or program-unit level.
   *Note it must be possible to add a justification for the overriding of the error message
   associated with the deviation, as well as having the possibility of logging that an error
   message has been overridden (to provide evidence for assurance purposes).*


   **Rationale**: This provides similar functionality to that of the --# accept statement
   in SPARK 2005 and gives the user the flexibility to decide that a given instance of a deviation is
   acceptable.

#. **Requirement**: It shall be possible to forbid any deviations from a given Profile or Policy.

   **Rationale**: This makes it easier to ensure the goals associated with a given Profile
   will be met. For example, if the goal of a Profile is to enable checking
   of a particular non-functional property then it should not be possible to
   step outside of the Profile at all.

Non-Language Requirements
-------------------------

#. **Requirement**: It shall be possible to record the goal or goals that a given Profile is
   intended to meet.

   **Rationale**: This provides the rationale for the existence and use of the Profile. The
   goals associated with the Profile are to be met by the Policies that make
   up the Profile, by the properties of the code that is outside of the
   Profile and by the set of compiler switches used when building the code. Hence, it may
   be necessary to impose certain restrictions on the code
   outside of the Profile in order to meet the goals. In addition, the goal
   to be met may restrict the places where we can step outside of a given Profile.

#. **Requirement**: It shall be possible to impose constraints to be met that hold at the
   boundary between the application areas of two Profiles (or between the application areas
   of a Profile and SPARK 2014, or between the application areas of SPARK 2014 and Ada 2012).

   **Rationale**: This is necessary, for example, in the case that we have code in |SPARK|
   that is formally verified and code in Ada 2012 that is tested. In more general terms,
   it may be necessary to meet the goal or goals associated with the Profiles.

#. **Requirement**: It shall be possible to record the compiler switch or switches that must be
   used in association with a given Profile.

   **Rationale**: In order to meet the goal/s associated with a given Profile, it may be
   necessary to require the use of certain switches.
