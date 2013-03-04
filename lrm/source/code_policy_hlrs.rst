Code Policy High-Level Requirements
===================================

Introduction
------------

The detail below defines the high-level requirements for the 
Code Profile language feature. Note that not all requirements
given below are expected to be implemented in the tool: some,
for example, will be implemented via procedures to be followed by the user.


Example
-------

*Goal of covering each of the requirements, to justify them.*

High-level goal
---------------

#. **Requirement**: It shall be possible to define a Code Profile or Profiles each of which defines
   a subset of the Ada 2012 language and mandate that programs respect a given
   Profile or Profiles.

   **Rationale**: In order to meet domain needs or certification requirements; or possibly to
   simplify proof or analysis.

Defining a Profile
------------------

#. **Requirement**: It shall be possible to define Code Profiles in a modular fashion as a
   collection of individual Policies, where each Policy specifies
   an individual constraint to impose. *Note that the SPARK 2014 Profile - see
   below - will not be defined as a set of Policies, since that would
   require the implementation of all SPARK 2014-related legality and verification
   rules to be implemented conditionally.*

   **Rationale**: This allows greater flexibility and ease of defining Profiles (and allows
   users to define their own Profiles based on the existing set of Policies).

#. **Requirement**: It shall be possible to record the goal or goals that a given Profile is
   intended to meet.

   **Rationale**: This provides the rationale for the existence and use of the Profile. The
   goals associated with the Profile are to to be met by the Policies that make
   up the profile and also by the properties of the code that is outside of the
   Profile. Hence, it may be necessary to impose certain restrictions on the code
   outside of the Profile in order to meet the goals. In addition, the goal
   to be met may restrict the places where we can step outside of a given Profile
   see below). *Procedural detail will be provided on doing this.*

#. **Requirement**: It shall be possible to impose both syntactic and semantic constraints when
   defining a Code Profile [that is, it shall be possible to impose whatever
   constraints can be imposed when defining a language using the Ada RM structure).

   **Rationale**: A Profile effectively defines a language, and so should be expressed using the
   same type of rules as are used to define SPARK 2014.

#. **Requirement**: It shall be possible to provide user-defined Profiles and Policies [though
   additional user-defined Policies will require updates to the tool to implement
   them]. *Note that we might be able to increment or decrement existing Profiles
   rather than defining a completely new Profile.*

   **Rationale**: This provides greater flexibility for the user and means they are not simply
   tied into using the provided Profiles and Policies.

#. **Requirement**: It shall be necessary for users to consider the potential for conflicts
   between Policies when defining a Profile and also between Profiles that might be applied
   in tandem to given program. *This requirement would be met via user procedure.*

   **Rationale**: It is possible that two Policies within the same or different Profiles
   impose inconsistent restrictions.


Applying Profiles
-----------------

#. **Requirement**:  It shall be possible to impose use of a given Profile at multiple levels of
   granularity.

   **Rationale**:   To allow the user maximum flexibility when applying a Profile.

#. **Requirement**:  It shall be possible to impose multiple Profiles simultaneously, the result
   being defined by the union of all the Policies contained within each Profile.

   **Rationale**:   To allow greater flexibility in imposing constraints on a given code base.

   **Requirement**:  Within an area of code otherwise covered by a given Profile, It shall be
   possible to designate code artefacts as outside of the Profile. *Note that
   if we step outside of one Profile, all other imposed Profiles still hold;
   if no Profile is imposed explicitly then the Ada 2012 Profile holds. Note
   also that the ability to step outside of a given Profile may be limited
   depending on the goal/s to be met by that Profile and also by the "closure
   rules" defined (see below).*

   **Rationale**:   This provides similar functionality to that of the --# hide annotation from
   SPARK 2005 and allows users to take advantage of additional language features
   in limited places, where that use is more beneficial than what is gained by
   imposing the Profile or where that use cannot be avoided.

#. **Requirement**:  It shall be possible to assign a classification to the Policies imposed by a
   given Profile that determines whether failure to meet a given Policy can be
   "accepted" and so ignored. *For example, it might not be possible to ignore
   a given Policy, it could be ignored in specific instances or it could be
   possible to ignore it globally.*

   **Rationale**:   In certain cases it may be necessary to relax the constraints imposed by a
   given Profile, but in the case of some Policies that may not be desirable.

#. **Requirement**:  It shall be possible to specify parts of a program where it should not
   be possible to deviate from the Policies of a given Profile.

   **Rationale**:   This makes it easier to ensure the goals associated with a given Profile
   will be met. For example, if the goal of a Profile is to enable checking
   of a particular non-functional property then it should not be possible to
   step outside of the Profile.

#. **Requirement**:  It shall be possible to specify the "closure rule" to be applied to a
   Profile (this defines - when a given language feature usage is defined
   to be outside of the Profile - how much of the enclosing or calling code
   is also defined to be outside of the Profile). *We could just define two
   closure rules: one that says everything in the partition has to be covered
   by the Profile, the other that gives the rules we will define for in and
   out of SPARK 2014.*

   **Rationale**:   This allows a less restrictive definition of what is necessary for code to
   be within a Profile: for example, it allows a Package to be regarded as
   within a Profile, even though it contains declarations that are outside of
   the Profile, provided those declarations are not used within the Package.

**Are we over-complicating from this point on? Need to either beef up the justification
and make sure the example illustrates why these things are necessary, or remove them.
Note we can say these things are all generalizations of what in/out of SPARK 2014 would need,
though maybe we don't need them in the general case.**

Boundary between Profiles
-------------------------

#. **Requirement**:  It shall be possible to impose constraints to be met - via imposition of a
   Profile - that hold at the boundary between the application areas of two
   Profiles.

   **Rationale**:   This is necessary, for example, in the case that we have code in SPARK 2014
   that is formally verified and code in Ada 2012 that is tested. In general,
   it may be necessary to meet the goal or goals associated with the Profiles.

Domain Restrictions
-------------------

#. **Requirement**: It shall be possible to record the compiler switch or switches that must be
   used in association with a given Profile.

   **Rationale**:   In order to meet the goal/s associated with a given Profile, it may be
   necessary to require the use of certain switches.

#. **Requirement**:  It shall be possible to impose restrictions to be met by the code that is
   not in a given Profile.

   **Rationale**:   This may be necessary to meet the goal or goals associated with the Profile.
   *Note that these restrictions would simply be defined as another Profile,
   though we would need to require that the two Profiles taken together provided
   full coverage of the Partition. Perhaps we would have a language feature to
   define Profile B as covering everything not covered by Profile A.*

#. **Requirement**:  It shall be possible to define the coverage of one Profile to be the
   complement of that of another Profile.

   **Rationale**:   This allows an easy way to state restrictions on the code that is outside of
   a given Profile.

General Points To Note
----------------------

#. SPARK 2014 shall be regarded as a Profile, though not one composed of individual Policies.

#. This means that the rules above give information on mixing of SPARK and non-SPARK.

#. Ada 2012 shall be regarded as the empty Profile.

#. Hence, all code is under at least one Profile.

