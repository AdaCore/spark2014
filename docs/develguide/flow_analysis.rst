Flow Analysis
=============

..  this is about global generation

Flow analysis is really about two activities: verifying the explicit data flow
contracts (e.g. Global/Depends) and generating them when they are missing.
Historically, 'vintage' SPARK only did the former; SPARK 2014 introduced the
latter. Contract generation is especially useful for users that want to prove
AoRTE without bothering to annotate their code. Global contract is enough for
that, so flow doesn't generate the Depends (although it could, but this would
be more complicated and quite likely also more expensive to compute).

At first GNATprove was generating only Global contracts; that's why we often
talk about "global generation", or GG in short. However, these days it also
generates contracts related to initialization, tasking and subprogram
termination, so strictly speaking we should talk about "contract generation."
Finally, GG also decides which constants have variable input (thus can appear
in the Global/Depends contracts), which is not really a contract at all. This
is quite a lot of features, so here is an overview of how they are implemented.

Two phases of contract generation
*********************************

To generate Global contract for a subprogram (caller) that calls another
subprogram (callee), we need the callee Globals [when saying "subprogram" we
really mean procedure, function, entry, task or a package; basically a unit
that might be annotated with a flow contract]. But callee might be in another
compilation unit, and because frontend works with a single compilation unit at
a time, we don't have the callee's AST. That's why GNATprove executes gnat2why
twice for each compilation unit: in first invocation we compute intra-unit info
about each subprogram and write it to an ALI file; in second invocation we
combine ALI files for the closure of the WITHed units.

Because of this single-unit restriction every analysis that involves more than
one unit is delegated to the flow analysis; yet, for our convenience frontend
rejects some violations that can be detected by looking at one unit alone. The
rationale for this duplication is not really clear. I suspect that in some
cases after implementing a check in the frontend we found corner cases that can
be only detected by inter-unit analysis; we added checks in flow, but decided
to keep the existing ones in the frontend.

We store the intermediate information in the ALI files, because GNAT already
has an infrastructure for that (e.g. we reuse the gprbuild facility for reading
the closure of the WITHed units). Also, in the Alfa days we relied on objects
read/written and callees of each subprogram discovered by the cross-references
and written in the ALI files. That information was imprecise (more on this
later) and we don't use that anymore. Actually, all the information stored in
the ALI file by the frontend could be removed to make tool slightly faster.

Historical note: the 'vintage' SPARK analysing all compilation units at a once,
but GNAT frontend can't do this (and we shall not expect that it will ever
do). Pros: analysing one unit at a time requires less memory; units can be
analysed in parallel. Cons: we need to store intermediate results in files.

Phase 1
*******

In phase 1 we want to find objects referenced as Input/Output/Proof_In and
definite/possible/proof callees for each subprogram of the current compilation
unit. In the Alfa days we got this info from the frontend cross-references, but
they were imprecise. For example, for a code like this:

.. code-block:: ada

   X := 0;
   X := X + 1;

they would tell us that X is both written and read, so we would classify it as
an In_Out global. Also, it was not possible to tell which references occurs in
proof contexts (e.g. in pragma Assert expressions), or to know which calls
happen for sure, which only conditionally, and which only in proof contexts.
Finally, some references were missing (e.g. in implicit calls to type
predicates) while other were spurious (e.g. references in pragma Pre/Post
expressions are believed to belong to the where the pragma occurs, not to which
subprogram it annotates).

To get precise information we need a something smarter. It is natural to reuse
the existing code for the flow analysis, thought it was designed for checking
contracts. Note that for contract checking we track full dependencies between
objects (as captured by the Depends contract). This is more than we need to
synthesize the Global contract (or in other words: from this info we could
synthesize the Depends contract too), but it feels easier to reuse the existing
code. Note: we could execute some sections of that code only when checking the
contract (i.e. only in phase 2), and indeed we already do this to improve
performance (in code related to record components, IIRC).

Consequently, it is natural to reuse the same code to generate contracts
related to tasking, termination, etc.

To keep the GG sane and correct, it is important that:

* info about subprograms is stored in the ALI for the unit where they are
  declared; this way, it won't be repeated in many files

* info about objects (e.g. their Ghost or Constant_After_Elaboration status) is
  stored in the ALI file of subprograms that reference them and not where that
  objects are declared; this way we won't miss this info when using "-u" switch
  or when no ALI file is generated for the unit with object declaration
  (e.g. because it is a predefined unit, is excluded from the analysis by a
  .gpr directive, or belongs to an external library)

Storing info about objects is rather straightforward; also, storing non-global
info about subprograms is easy (e.g. termination or non-blocking status).

Anything related to the Global contract is much harder, because we need to
track call chains that go outside and return to the declarative regions with
visibility of the abstract state refinement. To make things more complicated,
this is now implemented in both phase 1, where the algorithm was much easier to
prototype with all entities known by Entity_Id (so that existing frontend
routines can be easily used, especially for assertions), and in phase 2, where
we have info for subprograms from other units. It is tempting to think, that in
phase 2 all calls cross the boundary of visibility of the abstract state
refinement; unfortunately, calls between private child and private units do not
cross this boundary, yet we know nothing about private child units when
analysing parents in phase 1.

We might consider generating the Global contract in phase 2 only, but splitting
the work into two phases quite likely improves the performance. Contracts that
can be resolved in phase 1 are resolved only once (e.g. for a subprogram whose
all callees are in the same unit); we could do the same for other contracts
too, but so far their generation is not a performance bottleneck.

Phase 2
*******

Collecting info about objects is easy; we just need to remember that it might
be repeated in several ALI files.

Combining info about properties like termination and non-blocking status is
slightly harder. We do this with graphs rooted at selected subprograms from the
current compilation unit (e.g. protected subprograms for the non-blocking
status). However, we must be careful to respect the modularity; e.g. when a
protected subprogram calls a protected callee, we assume that the callee is
non-blocking, since this will be verified when analysing that callee itself.

Finally, generation of the Global contract is as complicated as in phase 1. We
generate these contracts for subprograms both from the current unit (because
most checks done on the flow analysis graphs require globals, either provided
by the user or generated) and for subprograms from the other units that are
translated by proof (e.g. expression functions that might reference their
Global in their Pre/Post contracts). The former are needed always; the latter
are only needed in --mode=proof; but a subset of both is also needed
in --mode=check_all, for detecting variable input in illegal contexts.

..  the remaining text is about everything except global generation
