Subprograms
===========

We separate the *declaration view* introduced by a ``subprogram_declaration``
from the *implementation view* introduced by a ``subprogram_body`` or an
``expression_function_declaration``. For subprograms that are not announced by
a ``subprogram_declaration``, the ``subprogram_body`` or
``expression_function_declaration`` also introduces a declaration view which
may be in Alfa even if the implementation view is not.

Subprogram Declarations
-----------------------

A function is in Alfa only if it is pure.

Preconditions and Postconditions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As indicated by the ``aspect_specification`` being part of a
``subprogram_declaration``, a subprogram is in Alfa only if its specific
contract expressions (introduced by ``Pre`` and ``Post``) and class-wide
contract expressions (introduced by ``Pre'Class`` and ``Post'Class``), if any,
are in Alfa.

Global Parameters
^^^^^^^^^^^^^^^^^

Besides reading and writing its parameters, a subprogram may reference directly
objects in scope at the point of the reference, as well as locations pointed to
through dereferences of a non-local access type. Note that such references may
occur directly in the body of the subprogram, or in the body of another
subprogram called. The locations referenced through objects in scope and global
dereferences, instead of just parameters and local dereferences, are the global
parameters of a subprogram.

GNAT provides a way to specify the global parameters of a subprogram:

.. code-block:: ada

    Aspect_Mark Global [in|out|in out]? => Annotation_List
    Annotation_List ::= ( Annotation_Item {, Annotation_Item} )
    Annotation_Item ::= object_name | NULL

Item ``object_name`` should identify an object in scope, while **null**, if
present, should be the only item in the list. Specifying ``Global => null`` on
an imported function states that the subprogram is a pure function of its
arguments to its result. An imported function is in Alfa only if it has such an
annotation.

Formal Parameter Modes
----------------------

In Alfa-friendly code, it is not allowed in a call to pass as parameters
references to overlapping locations, when at least one of the parameters is of
mode ``out`` or ``in out``, unless the other parameter is of mode ``in`` and
by-copy. Likewise, it is not allowed in a call to pass as ``out`` or ``in out``
parameter a reference to some location which overlaps with any global parameter
of the subprogram. Finally, it is not allowed in a call to pass as ``in`` or
``in out`` parameter a reference to some location which overlaps with a global
parameter of mode ``out`` or ``in out`` of the subprogram, unless the parameter
is of mode ``in`` and by-copy. This is the meaning of restriction
``No_Parameter_Aliasing``.

A parameter X of type T is said to be valid if:

  * ``X'Valid`` evaluates to True for a scalar type T;

  * all components are valid for a record type T, where the validity of a 
    variant component is defined as the validity of the components for its 
    current value of discriminant;

  * all indexed components are valid for an array type T.

In Alfa-friendly code, all ``in`` and ``in out`` parameters should be valid at
the point of call. And all ``out`` and ``in out`` parameters should be valid
when returning from the subprogram. This is the meaning of restriction
``No_Uninitialized_Parameters``.

Subprogram Bodies
-----------------

No specific restrictions.

Subprogram Calls
----------------

A call is in Alfa only if it resolves statically to a subprogram whose
declaration view is in Alfa (whether the call is dispatching or not).

Return Statements
-----------------

No specific restrictions.

Overloading of Operators
------------------------

No specific restrictions.

Null Procedures
---------------

No specific restrictions.

Expression Functions
--------------------

No specific restrictions.
