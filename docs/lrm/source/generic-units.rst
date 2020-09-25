Generic Units
=============

Enforcement of |SPARK|'s rules within a generic unit is not
guaranteed. Violations might not be reported until an
instance of the generic unit is analyzed.
If an instance of a generic unit occurs within another generic unit,
this principle is applied recursively.

.. _generic_instantiation:

Generic Instantiation
---------------------

.. centered:: **Legality Rules**


1. An instantiation of a generic is or is not in |SPARK| depending on
   whether the instance declaration and the instance body (described
   in section 12.3 of the Ada reference manual) are in |SPARK| [(i.e.,
   when considered as a package (or, in the case of an instance of a
   generic subprogram, as a subprogram)].

2. [A generic actual parameter corresponding to a generic formal
   object having mode **in** shall not have a variable input;
   see :ref:`expressions` for the statement of this rule.]


[For example, a generic which takes a formal limited private type
would be in |SPARK|. An instantiation which passes in a general access type
as the actual type would not be in |SPARK|; another instantiation
of the same generic which passes in, for example, Standard.Integer,
might be in |SPARK|.]

[Ada has a rule that legality rules are not enforced in an
instance body (and, in some cases, in the private part of an
instance of a generic package). No such rule applies to the restrictions
defining which Ada constructs are in |SPARK|. For example, a backward goto
statement in an instance body would cause the instantiation to not be in
|SPARK|.]

[Consider the problem of correctly specifying the Global and Depends
aspects of a subprogram declared within an instance body which contains
a call to a generic formal subprogram (more strictly speaking, to the
corresponding actual subprogram of the instantiation in question).
These aspects are simply copied from the corresponding aspect specification
in the generic, so this implies that we have to "get them right" in the generic
(where "right" means "right for all instantiations"). One way to do this
is to assume that a generic formal subprogram references no globals
(or, more generally, references any fixed set of globals)
and to only instantiate the generic with actual subprograms that
meet this requirement.]

.. todo:: Discsuss LSP-ish rules for globals, similar to the
   compatibility rules for Global/Depends aspects of a subprogram
   which overrides a dispatching operation. OK, for example, if a
   subprogram reads fewer inputs than it said it would.] To be
   considered post release 1.
