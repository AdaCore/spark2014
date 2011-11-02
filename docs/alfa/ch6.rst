Subprograms
===========

We distinguish the *declaration view* introduced by a ``subprogram_declaration``
from the *implementation view* introduced by a ``subprogram_body`` or an
``expression_function_declaration``. For subprograms that are not declared by
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

Besides reading and writing its parameters, a subprogram in Ada may directly
reference objects in scope at the point of the reference, as well as locations
pointed to through dereferences of a non-local access type. Note that such
references may occur directly in the body of the subprogram, or in the body of
another called subprogram. Objects other than formal parameters that are
referenced either directly by their name or via dereferences of a non-local
access type are referred to as the *global parameters* of a subprogram.

GNAT provides a way to specify the global parameters of a subprogram:

.. code-block:: ada

   Global [in|out|in out]? => Annotation_List
   Annotation_List ::= ( Annotation_Item { Annotation_Item} )
   Annotation_Item ::= object_name | NULL

Item ``object_name`` shall identify an object in scope, while **null**, if
present, shall be the only item in the list. Specifying ``Global => null`` on
an imported function states that the subprogram does not have global
parameters. An imported function is in Alfa only if it has an annotation
giving its global parameters.

Here are examples of use of global parameters:

.. code-block:: ada

   procedure Get_Obj with Global in => Obj;
   procedure Set_Obj with Global out => Obj;
   procedure Incr_Obj with Global in out => Obj;
   procedure Copy with Global in => From, Global out => To;
   procedure Mult_Copy with Global in => From1 From2, Global out => To1 To2;
   function Pure_Func (X, Y : T) return Boolean with Global => null;

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
