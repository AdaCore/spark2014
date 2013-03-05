Code Profile High-Level Requirements
====================================

Introduction
------------

The detail below defines the high-level requirements for the 
Code Profile language feature. Note that not all requirements
given below are expected to have tool support: some,
for example, may be implemented via procedures to be followed by the user.

General Points To Note
----------------------

#. |SPARK| is regarded as a Profile, though not one composed of individual Policies.

#. This means that the requirements below give information on mixing of SPARK and non-SPARK.

#. Ada 2012 is regarded as the empty Profile.

#. Hence, all code is under at least one Profile.


Example
-------

The most obvious example of a Profile that will be developed under the SPARK 2014 project
is *Classic SPARK*, which represents the set of restrictions imposed by SPARK 2005.

Goal
~~~~

That |SPARK| is designed to allow the largest subset of Ada amenable to formal verification
leads to a product offering quite distinct from the current SPARKPro toolset and language.
This is because limitations were imposed on the Ada 2005 subset allowable under SPARK 2005
for other reasons, such as:

#. Enforcing good programming practice;

#. Making code easier to read and understand;

#. Ensuring that the memory used by a program can be statically determined.

Hence, the Classic SPARK Profile will aim to meet the same goals as are met by SPARK 2005,
by imposing many of the restrictions imposed by SPARK 2005 (it will be possible, however,
to eliminate restrictions that were only present due to time or cost constraints).

Example Policies
~~~~~~~~~~~~~~~~

A Code Profile is composed of a number of Policies, where each Policy imposes
a restriction to be met by programs written by the user.

The following are example Policies that could be part of the Classic SPARK Profile.

No_Recursion
^^^^^^^^^^^^

Recursion shall be forbidden. *This check would be performed
by flow analysis.*

No_Default_Subprogram_Parameters
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This Policy prohibits the use of default subprogram parameters, that is, a
``parameter_specification`` cannot have a ``default_expression``.
*This check could be performed in the GNAT front-end.*

Limited_Variable_Access_During_Elaboration
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

No variable declared immediately within another package can
be read or updated during elaboration of this package.

User-defined modifications
~~~~~~~~~~~~~~~~~~~~~~~~~~

Having defined the Classic SPARK Profile, some users might decide they need not
impose all Policies that it contains. For example, they might feel recursion should
be allowed and so the No_Recursion Policy is not needed. Hence, it should be possible
for users to define new Profiles (possibly based on modification of existing Profiles).

High-level goal
---------------

#. **Requirement**: It shall be possible to define a Code Profile or Profiles each of which defines
   a subset of the Ada 2012 language and mandate that programs respect a given
   Profile or Profiles.

   **Rationale**: In order to meet domain needs or certification requirements; or possibly to
   simplify proof or analysis. In addition, this allows the definition of a Classic SPARK Profile
   that imposes the same restrictions as SPARK 2005, but within a |SPARK| framework.

Defining a Profile
------------------

#. **Requirement**: It shall be possible to define Code Profiles in a modular fashion as a
   collection of individual Policies, where each Policy specifies
   an individual constraint to impose. *Note that the SPARK 2014 Profile will not be defined
   as a set of Policies, since that would require all SPARK 2014-related legality and verification
   rules to be implemented conditionally.*

   **Rationale**: This allows greater flexibility and ease of defining Profiles (and allows
   users to define their own Profiles based on the existing set of Policies).

#. **Requirement**: It shall be possible to record the goal or goals that a given Profile is
   intended to meet.

   **Rationale**: This provides the rationale for the existence and use of the Profile. The
   goals associated with the Profile are to to be met by the Policies that make
   up the Profile, by the properties of the code that is outside of the
   Profile and by the set of compiler switches used when building the code. Hence, it may
   be necessary to impose certain restrictions on the code
   outside of the Profile in order to meet the goals. In addition, the goal
   to be met may restrict the places where we can step outside of a given Profile
   (see below). *Procedural detail would be provided in relation to this.*

#. **Requirement**: It shall be possible to impose both syntactic and semantic constraints when
   defining a Code Profile [that is, it shall be possible to impose whatever
   constraints can be imposed when defining a language using the Ada RM structure).

   **Rationale**: A Profile effectively defines a language, and so should be expressed using the
   same type of rules as are used to define |SPARK|.

#. **Requirement**: It shall be possible to provide user-defined Profiles and Policies [though
   additional user-defined Policies will require updates to the toolset to implement
   them]. *Note that we might be able to allow incrementing or decrementing existing Profiles
   rather than defining a completely new Profile.*

   **Rationale**: This provides greater flexibility for the user and means they are not simply
   tied into using the provided Profiles and Policies.
   
#. **Requirement:** It shall be possible to check Policies for consistency. *Note that this
   will likely be covered by an appropriate procedure.*

   **Rationale:** It is possible that simultaneously imposed Policies might be inconsistent
   and hence there are no programs that can satisfy them.

Applying Profiles
-----------------

#. **Requirement**:  It shall be possible to impose multiple Profiles simultaneously, the result
   being defined by the union of all the Policies contained within each Profile.

   **Rationale**:   To allow greater flexibility in imposing constraints on a given code base.

#. **Requirement**:  It shall be possible to impose a Profile or Profiles on a given code base
   at multiple levels of granularity (for example, at a partition level or at a package level).
   *Note that where a Profile no longer needs to cover the whole code base, a mechanism is needed
   to be sure that it covers enough of the code base: for example, if code mandated to be in
   SPARK 2014 calls a subprogram from another package, at least the declaration of that subprogram
   should be in SPARK 2014.*

   **Rationale**:   To allow the user maximum flexibility when applying a Profile.

#. **Requirement**:  Within an area of code otherwise covered by a given Profile, it shall be
   possible to designate code artefacts as being outside of the Profile. *Note that
   if we step outside of one Profile, all other imposed Profiles still hold;
   if no Profile is imposed explicitly then the Ada 2012 Profile holds. Note
   also that the ability to step outside of a given Profile may need to be limited
   procedurally by the user depending on the goal/s to be met by that Profile.*

   **Rationale**:   This provides similar functionality to that of the --# hide annotation from
   SPARK 2005 and allows users to take advantage of additional language features
   in limited places, where that use is more beneficial than what is gained by
   imposing the Profile or where that use cannot be avoided.

#. **Requirement**: It shall be possible to accept deviations from a given Profile or Policy.

   **Rationale**: This provides similar functionality to that of the --# accept statement
   in SPARK 2005 and gives the user the flexibility to decide that a given deviation is
   acceptable.

#. **Requirement**: It shall be possible to forbid certain deviations from a Profile or Policy.
   *This could be managed, for example, via forbidding any deviations from a given Policy anywhere,
   or via forbidding any deviations at all within specified parts of a program.*

   **Rationale**: This makes it easier to ensure the goals associated with a given Profile
   will be met. For example, if the goal of a Profile is to enable checking
   of a particular non-functional property then it should not be possible to
   step outside of the Profile at all.

Boundary between Profiles
-------------------------

#. **Requirement**: It shall be possible to impose constraints to be met that hold at the
   boundary between the application areas of two Profiles.

   **Rationale**: This is necessary, for example, in the case that we have code in |SPARK|
   that is formally verified and code in Ada 2012 that is tested. In more general terms,
   it may be necessary to meet the goal or goals associated with the Profiles. *Note that this
   requirement is present because it is assumed SPARK 2014 itself will be treated as a Profile.
   This assumption is useful because it gives a clear framework within which to think
   about issues such as mixing SPARK 2014 and non-SPARK 2014 code. However, if it is decided
   this is not the way to proceed and this SPARK 2014-related need will be met simply
   by miscellaneous language rules then this requirement can be removed from the
   consideration of Profiles.*

Domain Restrictions
-------------------

#. **Requirement**: It shall be possible to impose restrictions to be met by the code that is
   not in a given Profile.

   **Rationale**: This may be necessary to meet the goal or goals associated with the Profile
   and is especially necessary in the case that we have code in |SPARK|
   that is formally verified and code in Ada 2012 that is tested.
   *Note that these restrictions could simply be defined as another Profile,
   though we would need to require that the two Profiles taken together provided
   full coverage of the partition. Perhaps we would have a language feature to
   define Profile B as covering everything not covered by Profile A?* *Note also that this
   requirement is present because it is assumed SPARK 2014 itself will be treated as a Profile.
   This assumption is useful because it gives a clear framework within which to think
   about issues such as mixing SPARK 2014 and non-SPARK 2014 code. However, if it is decided
   this is not the way to proceed and this SPARK 2014-related need will be met simply
   by miscellaneous language rules then this requirement can be removed from the
   consideration of Profiles.*

#. **Requirement**: It shall be possible to record the compiler switch or switches that must be
   used in association with a given Profile.

   **Rationale**: In order to meet the goal/s associated with a given Profile, it may be
   necessary to require the use of certain switches.

