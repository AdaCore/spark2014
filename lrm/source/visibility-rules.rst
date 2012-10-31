Visibility Rules
================

Declarative Region
------------------

No extensions or restrictions.

Scope of Declarations
---------------------

No extensions or restrictions.

Visibility
----------

No extensions or restrictions.

Use Clauses
-----------

Use clauses are always in |SPARK|, even if the unit mentioned is not completely
in |SPARK|.

Renaming Declarations
---------------------

.. todo:: RCC. TJJ spots that a *renaming-as-body* is potentially problematic for proof.
   Ada says that the profile of a renaming-as-body must "conform fully to that of
   the declaration it completes", but what does this mean for |SPARK|?  What if the
   renamed subprogram has a different list of Globals (e.g. different side-effects)
   to that of the subprogram declaration being completed?  What if the Pre and Post
   are completely different?  Ada LRM 6.3.1 defines "fully conformant", but this
   doesn't seem to say anything and Pre and Post. Do we need
   to define a concept of "Proof Conformance" for |SPARK| that includes conformance
   of Globals, Pre and Post? UPDATE: conversation with SB says to think of a 
   renaming-as-body as a one-line "call through wrapper" subprogram body. In that way,
   the rules are clear: Parameters, Globals and Depends must match exactly, but Pre and Post
   may exhibit the usual refinement relationship. Action on RCC to check what
   GNATProve actually implements at the moment. Target: D2.

.. todo:: RCC: Also concern about renaming-as-body when state refinement is present?
   Should that be possible? Target: D2.

The Context of Overload Resolution
----------------------------------

No extensions or restrictions.
