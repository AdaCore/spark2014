Generated Global Contracts
==========================

The code for generating global contracts has been almost entirely rewritten
in 2016. The original design document for this rewrite is in
`docs/flow/generated_globals_2016_redesign/`. Here is a more down-to-code
explanation, including many important issues with the original design that were
only discovered while implementing that document.

As a running example, let's consider this code:

.. code-block:: ada

   package Outer is
      package Inner with Abstract_State => State is
         function A return Boolean;
         function B return Boolean;
      end;
      function C return Boolean;
   end;

   package body Outer is
      package body Inner with Refined_State => (State => (X, Y)) is
         X, Y : Boolean := True;
         function A return Boolean is (X and C);
         function B return Boolean is (Y);
      end Inner;

      function C return Boolean is (B);
   end;

with the notable calls A->C->B, which go outside of the package with an
abstract state and then inside back. Our job is to figure out the Global and
Refined_Global contracts for all routines.

Preanalysis
***********

The entry point is the ``Generate_Contracts`` routine. It analyses the entities
from the current compilation unit to collect intra-subprogram data, i.e. data
that can be deduced from the subprogram alone without looking at its
callees. If the SPARK_Mode barrier allows us to look at the subprogram body, we
get this data with ``Preanalyze_Body``, which relies on the CFG analysis;
otherwise, we get it with ``Preanalyze_Spec``, which relies on the frontend
cross-references. Note: if the body is not in SPARK, but there are explicit
Global/Depends contracts on the spec, we trust those contracts and do not query
frontend cross-references. This is intentional and it allows the users to
override the imperfect frontend-cross references with explicit contracts.

From the ``Preanalyze_[Body|Spec]`` we get *direct* (refined) proof_ins, inputs
and outputs (this should be obvious) and *direct* callees split into definite,
conditional and proof calls.

The intuition behind having three different kinds of calls is this: output of a
definitive call will become our output (this is obvious); output of a
conditional call will become our in_out (because when condition for a call is
not satisfied, we pretend there is a self-assignment of the output object);
inputs of proof calls will become our proof_ins (again, this is obvious). If we
omit any of those categories, we will miss-classify too many global objects.

For our example, those are:
::
   A: inputs => {X}, definite_calls => {C}
   B: inputs => {Y}
   C: definite_calls {B}

Now we "just" need to compute proof_ins/inputs/outputs contributed by
definite/conditional/proof calls and produce both Refined_Global and Global
contracts.

Naive solution
**************

A naive solution would be to start from any routine, recursively iterate over
its callees and union their globals with ours. Say, let's start from A: we go
to C (which has no globals, so there is nothing to do) and then to B (which has
an input Y, which we are tempted to union with our own own input X). However,
on the call A->C we went out of the package Inner and lost the visibility of
its state's constituent; the call C->B must contribute the abstract view of
State, not its constituent Y.

Another hurdle is with a call graphs like this:
::
   Foo --[definite]--> Proxy --[proof]--> Bar
    |                                      ^
    +--------------[conditional]-----------+

When we look at Foo and want to take into account both the direct and indirect
call to Bar (via Proxy), we must decide what kind of callee Bar really is.
Also, it raises questions: does it matter if we already took Bar globals into
account when it acted as another kind of callee? does it matter if we took them
before we walked out-and-back from our own package?

As you can see, the naive solution is getting complicated...

A modular solution
******************

Instead, our solution is based on principle of modularity: we start from the
most nested context (i.e. a subprogram, task type or package) and keep
resolving both globals and calls as we move into enclosing contexts, one at a
time.

In terms of code, we start by calling ``Do_Global`` on the root entity of the
current compilation unit (Outer); then we immediately recurse into its nested
entities (Inner) and then we do the same with A and B (which are leaf entities,
so the recursion terminates). Within each invocation of ``Do_Global``, we first
iterate over all nested entities with ``Fold``, which combines globals and
calls of its parameter ``Folded`` knowing that it operates in the context of
its parameter ``Analyzed``. In picture, it looks like this: ::
   * Do_Global (Outer)
     * Do_Global (Inner)
       * Do_Global (A)
       * Do_Global (B)
     * Fold [Inner, A, B] with Analyzed => Inner
   * Fold [Outer, Inner, A, B] with Analyzed => Outer

You can think of this as a double-level iteration. As it happens, we populate
the Refined_Global/Global contracts based on the Refined_Global/Global
contracts of the callees, forget about the callees from the inner contexts, and
keep discover (indirect) callees from the outer contexts.
