The Standard Libraries
======================

This chapter describes how |SPARK| treats the Ada predefined
language environment and standard libraries, corresponding
to appendices A through H of the Ada RM. The goal is that |SPARK| programs are able
to use as much as possible of the  the Ada predefined language environment and standard libraries.

.. todo:: Provide detail on Standard Libraries.
          To be completed in a post-Release 1 version of this document. This targeting applies
          to all ToDos in this chapter.

.. todo:: In particular, it is intended that predefined container generics
          suitable for use in |SPARK| will be provided. These will
          have specifications as similar as possible to those of
          Ada's bounded containers (i.e., Ada.Containers.Bounded_*), but with
          constructs removed or modified as needed in order to maintain the
          language invariants that |SPARK| relies upon in providing
          formal program verification.

Predefined Language Environment
-------------------------------

The Package Standard
~~~~~~~~~~~~~~~~~~~~

|SPARK| supports all of the types, subtypes and operators declared in package Standard.
The predefined exceptions are considered to be declared in Standard, but their use is
constrained by other language restrictions.

The Package Ada
~~~~~~~~~~~~~~~

.. todo:: Should we say here which packages are supported in |SPARK| or which ones aren't
   supported?  How much of the standard library will be available, and in which run-time
   profiles?


Interface to Other Languages
----------------------------

This section describes features for mixed-language programming in |SPARK|, covering facilities
offered by Ada's Annex B.

.. todo:: How much to say here?  S95 supports a subset of Interfaces, and a very small subset of
   Interfaces.C but that's about it. 

.. todo:: What is status of supported for pragma ``Unchecked_Union`` in GNATProve at present?

Systems Programming
-------------------

tbd.

Real-Time Systems
-----------------

This section describes features for real-time programming in |SPARK|, covering facilities
offered by Ada's Annex D.

.. todo:: RCC: Need to think about Ada.Real_Time.  It's important for all S95 customers, to get
   at monotonic clock, even if not using RavenSPARK.  It does depend on support for external
   variables, though, since Ada.Real_Time.Clock is most definitely Volatile. TN [LB07-024]
   raised to discuss this.

Distributed Systems
-------------------

TBD.

Information Systems
-------------------

TBD.

Numerics
--------

This section describes features for numerical programming in |SPARK|, covering facilities
offered by Ada's Annex G.

.. todo:: How much here can be supported?  Most S95 customers want Ada.Numerics.Generic_Elementary_Functions
   plus its predefined instantiation for Float, Long_Float and so on.  How far should we go?

High Integrity Systems
----------------------

|SPARK| fully supports the requirements of Ada's Annex H.




