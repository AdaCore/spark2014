Names and Expressions
=====================

 

.. todo:: Need to think about this chapter.


.. todo:: This text has been copied directly from the initial langauge
    design document as prepared by Johannes. It needs to be tided up
    into LRM format.  It was headed Richer Expressions but describes
    attributes.  I am not sure this is the right chapter for these?

Richer Expressions
------------------

New Attributes
--------------

The attributes ``'Loop_Entry``, ``'Update``, ``'Valid_Scalars`` are
introduced.

.. todo::
  Need to discuss the use/need for ``'Loop_Entry`` that apply to an outer
  loop, to be used in the expression of an inner loop invariant. If we want
  to support that, we will need special rules to prevent the use of a name
  of an object that does not exist at loop entry.

Legality rules
--------------

Some valid Ada programs are invalid in SPARK. In particular, a program that
attempts accessing a component of an object of type ``T`` is invalid in SPARK
if that composent is absent from ``T`` (while it may be valid in Ada for
subtypes of discriminant records, although it would raise an exception at run
time).

.. todo::
  Need to discuss 'Loop_Entry execution model, in particular when does the
  object go out of scope (leading to e.g. finalization call)

All these attributes apply to names. The ``'Loop_Entry`` attribute can only be
used in assertions in loops (such as ``Loop_Invariant`` or ``Assert``), and
can not be applied to objects of limited type. It has an optional label
as argument which denotes a loop block. If no such label is given,
``'Loop_Entry`` is associated to the innermost enclosing loop.

The ``'Update`` attribute only applies to composite objects. It expects a
comma-separated list of associations as argument, of the form ``expression =>
expression``.

Semantics
---------

The expression ``Name'Loop_Entry`` designates the value of ``Name`` at the
beginning of the first iteration of its associated loop. The expression
``Name'Update (...)`` designates the value of ``Name``, except for the
components that are specified by the association list in argument. The
expression ``Name'Valid_Scalars`` is a boolean expression that evaluates to
``True`` whenever all scalar components or subcomponents of ``Name`` have
values allowed by their type.
