General
=======

Alfa is a subset of Ada suitable for automatic formal verification of
programs. Defining characteristics of Alfa are the following:

  * Alfa is defined for all Ada versions (83, 95, 2005, 2012).
  * Verification of Alfa code relies essentially on the ability to specify a 
    contract for subprograms, and possibly test-cases, whether it is with a
    pragma notation or an aspect notation (in Ada 2012 only).
  * Being in Alfa is not an all-or-nothing property. Subprograms in Alfa can
    call Ada subprograms that are not in Alfa. Units in Alfa can ``with`` units
    that are not in Alfa. An Ada unit can contain both subprograms in Alfa and
    subprograms that are not in Alfa.
  * A subprogram in Alfa can be formally analyzed to prove that its sequential
    execution is free from run-time errors, and that it respects a specified
    contract. A contract is given by two boolean expressions: a precondition
    and a postcondition. A subprogram respect its contract if, whenever it is
    called in a context where the precondition holds, and it terminates
    normally, then it returns to the caller in a context where the
    postcondition holds.
  * A subprogram can be in Alfa only if the complete program to which it
    belongs respects some constraints which define the ``Alfa_Friendly``
    profile.

Profiles and Restrictions
-------------------------

The Alfa Friendly Profile
^^^^^^^^^^^^^^^^^^^^^^^^^

This profile defines the set of restrictions that a unit must respect to be
part of a program containing Alfa code. It is equivalent to the following set
of pragmas:

.. code-block:: ada

   pragma Restrictions (
            No_Access_Subprograms,
            No_Finalization,
            No_Implicit_Aliasing,
	    No_Parameter_Aliasing);

In the following, when we say that a construct is in Alfa, this is always
subject to the constraint that the code of the complete program is Alfa
friendly.

The Alfa Restriction
^^^^^^^^^^^^^^^^^^^^

This restriction defines what it is for a unit to be in Alfa.


