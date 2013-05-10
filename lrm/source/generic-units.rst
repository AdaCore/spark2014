Generic Units
=============

Any generic unit is in |SPARK|, regardless of whether it
contains constructs that are not normally in |SPARK|.
[Information flow analysis is not performed on a generic unit;
a generic unit generates no proof obligations].

An instantiation of a generic is or is not in |SPARK|
depending on whether the instance declaration and the instance
body (described in section 12.3 of the Ada reference manual)
are in |SPARK| [(i.e., when considered as a package (or, in the
case of an instance of a generic subprogram, as a subprogram)].

[For example, a generic which takes a formal limited private type
would be in |SPARK|. An instantiation which passes in a task type
as the actual type would not be in |SPARK|; another instantiation
of the same generic which passes in, for example, Standard.Integer,
might be in |SPARK|.]

[Ada has a rule that legality rules are not enforced in an
instance body. No such rule applies to the restrictions defining
which Ada constructs are in |SPARK|. For example, a goto statement
in an instance body would cause the instantiation to not be in |SPARK|.]

[Consider the problem of correctly specifying the Global and Depends
aspects of a subprogram declared within an instance body which contains
a call to a generic formal subprogram (more strictly speaking, to the
corresponding actual subprogram of the instantation in question).
These aspects are simply copied from the corresponding aspect specification
in the generic, so this implies that we have to "get them right" in the generic
(where "right" means "right for all instantiations"). One way to do this
is to assume that a generic formal subprogram references no globals
(or, more generally, reference any fixed set of globals)
and to only instantiate the generic with actual subprograms that
meet this requirement. Other solutions involving "generative mode"
(where flow-related aspect specifications are omitted in the source
and generated implicitly by the tools) may also be available, but
are outside of the scope of this document.]

[At some point in the future, a more sophisticated treatment of
generics may be defined, allowing a generic to be "proven" and
eliminating the need separately verify the correctness of each
instantiation. That is not today's approach.]

[TBD: discsuss LSP-ish rules for globals, similar to the
compatibility rules for Global/Depends aspects of a
subprogram which overrides a dispatching operation. OK, for example,
if a subprogram reads fewer inputs than it said it would.]
