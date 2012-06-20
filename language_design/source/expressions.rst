Richer expressions
==================

New Attributes
--------------

The attributes ``'Loop_Entry``, ``'Update``, ``'Valid_Scalars`` are
introduced.

Legality rules
--------------

.. todo::
  Need to discuss 'Loop_Entry execution model, in particular when does the
  object go out of scope (leading to e.g. finalization call)

All these attributes apply to names. The ``'Loop_Entry`` attribute can only be
used in assertions in loops (such as ``Loop_Invariant`` or ``Assert``), and
can not be applied to objects of limited type. It has an optional label
as argument which denotes a loop block. If no such label is given,
``'Loop_Entry`` is associated to the innermost enclosing loop.

The ``'Update`` attribute only applies to aggregate objects. It expects a
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
