Procedure Calls
=================

The previous chapter was concerned with the declaration of subprograms.  This chapter discusses the semantic checks and restrictions placed on a call to a procedure.  The semantic checks are present to avoid the possibility of introducing aliases where the same object may be referenced by two different names.  The presence of aliasing is inconsistent with the underlying flow analysis and proof models used by the tools which assume that different names represent different entities.  In general, it is not possible or is difficult to deduce that two name refer to the same object and problems arise when one of names is used to update the object.  

A common place for aliasing to be introduced is through the *actual parameters* (see Ada LRM 6.4.1)  and between *actual parameters* and *global variables* in a procedure call.  The extra semantic rules avoid the possibility of aliasing through *actual parameters* and *global variables*.  A function is not allowed to have side-effects and cannot update an *actual parameter* or *global variable*.  Therefore a function call cannot introduce aliasing and are excluded from the anti-aliasing static semantic rules given below for procedure calls.

Anti-Aliasing 
-------------

The static semantics require the determination of the ``global_items`` of a procedure.  These may be obtained from a ``global_aspect`` or ``dependency_aspect`` of the procedure, if one is present, or has to be calculated from a whole program analysis.

Extended Static Semantics
^^^^^^^^^^^^^^^^^^^^^^^^^

#. If a procedure P has a ``global_aspect`` then:
  
   #.  in applying the static semantic rules to calls of a procedure P occurring outside the package in which P is declared, the ``global_aspect`` in the declaration should be employed; 
   #. whereas in applying the rules to calls to P within the body of this package, the ``refined_global_aspect``  (need a reference here???)  of the procedure body or body stub should be used, if it exists, otherwise the one from the declaration is used.

#. If a procedure does not have an aspect clause, then the globals will be determined from whole program analysis and the rules applied to the computed *global variables*.  If a computed *global variable* is not visible at the place where the procedure is called it is considered to be unable to be involved with aliasing.
#.  If a *variable* V named in the ``global_aspect`` of a procedure P is of mode **out** or **in out**, then neither V nor any of its subcomponents can occur as an *actual parameter* of P.
#. If a *variable* V occurs in the ``global_aspect`` of a procedure P, then neither V nor any of its subcomponents can occur as an *actual parameter* of P where the corresponding *formal parameter* is of mode **out** or **in out**.
#. If an *entire variable* V or a subcomponent of V occurs as an *actual parameter* in a procedure call statement, and the corresponding *formal parameter* is of mode **out** or **in out**, then neither V or an overlapping subcomponent of V can occur as another *actual parameter* in that statement. Two components are considered to be overlapping if they are elements of the same array with the same index, or slices of the same array with common indices, or are the same component of a record (for example V.F and V.F) including subcomponents of the component (for example V.F and V.F.P).
#. Where one of these rules prohibits the occurrence of a *variable* V or any of its subcomponents as an actual parameter, the following constructs are also prohibited in this context:

    #. a type conversion whose operand is a prohibited construct;
    #. a qualified expression whose operand is a prohibited construct;
    #. a prohibited construct enclosed in parentheses.

Restrictions That May Be Applied
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. The  restriction ``Array_Elements_Assumed_To_Overlap`` assumes that array elements are always considered to be overlapping and so, for example, V.A(I).P and V.A(J).Q are considered as overlapping.  This restriction can be enforced simply whereas the more general rule that array subcomponents are only considered to be overlapping when they have common indices requires formal proof in general.

Dynamic Semantics
^^^^^^^^^^^^^^^^^

The extended static semantics are checked using static analyses, no extra dynamic checks are required.

.. todo::  I can imagine that the anti-aliasing checks could be done dynamically but this could change the behaviour of what are currently valid Ada programs.  I think we should consider this as a staticly determined check used with SPARK 2014.
