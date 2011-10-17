Subprograms
===========

Subprogram Declarations
-----------------------

Preconditions and Postconditions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Global Parameters
^^^^^^^^^^^^^^^^^

Besides reading and writing its parameters, a subprogram may reference directly
objects in scope at the point of the reference, as well as locations pointed-to
through dereferences. Note that such references may occur directly in the body
of the subprogram, or in the body of another subprogram called. The locations
referenced through objects in scope and dereferences, instead of just
parameters, are the global parameters of a subprogram.

GNAT provides a way to specify the global parameters of a subprogram:

.. code-block::

  Aspect_Mark global [in|out|in out]? => Annotation_List
  Annotation_List ::= ( Annotation_Item {, Annotation_Item} )
  Annotation_Item ::= object_name | NULL | OTHERS

Specifying ``global => null`` states that the subprogram is a pure function of
its arguments to its result.

Formal Parameter Modes
----------------------

In Alfa-friendly code, it is not allowed in a call to pass as parameters
references to overlapping locations, when at least one of the parameters is of
mode ``out`` or ``in out``. Likewise, it is not allowed in a call to pass as
``out`` or ``in out`` parameter a reference to some location which overlaps
with any global parameter of the subprogram. Finally, it is not allowed in a
call to pass as ``in`` or ``in out`` parameter a reference to some location
which overlaps with a global parameter of mode ``out`` or ``in out`` of the
subprogram. This is the meaning of restriction ``No_Parameter_Aliasing``.

A parameter of type T is said to be valid if:

  * it is in range for an integral type T;

  * all components are valid for a record type T, and

    * the value of the tag corresponds to T or a derived type from T, for a
      tagged record T;
    * the discriminant is valid for a discriminant type T;
    * an array component whose bounds are controlled by the discriminant has
      expected bounds, for a discriminant type T; 

  * all indexed components are valid for an array type T;

In Alfa-friendly code, all ``in`` and ``in out`` parameters should be valid at
the point of call. And all ``out`` and ``in out`` parameters should be valid
when returning from the subprogram.

Subprogram Bodies
-----------------

Subprogram Calls
----------------
