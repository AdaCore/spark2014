General
=======

Alfa is a subset of Ada 2012 suitable for automatic formal verification of
programs. Alfa builds on the capability to specify contracts for subprograms in
Ada 2012, which supports modular verification of subprograms by unit testing or
unit proving: a subprogram with a contract can be unit tested; a subprogram in
Alfa with a contract can also be unit proved. In order to combine the results
of unit testing and unit proving, the complete program should be *Alfa
friendly*, so that the assumptions made during unit proving of a subprogram can
be dynamically verified during unit testing of a caller or callee of this
subprogram.

The Alfa friendly profile is equivalent to the following set of pragmas:

.. code-block:: ada

   pragma Restrictions (
            No_Access_Subprograms,
            No_Finalization,
            No_Implicit_Aliasing,
	    No_Parameter_Aliasing);

This document defines both the the Alfa restriction and the Alfa friendly
profile.

