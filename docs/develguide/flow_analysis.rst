Flow Analysis
=============

To start hacking on the flow analaysis you should first read about the general
tool architecture (:ref:`Tool Structure`). Then the main entry point for the
gnat2why backed is the GNAT_To_Why routine. Note: we hack on gnat2why with
different editors, but for newcomers it is the easiest to stick with GNAT Studio,
because it seems best with code navigation (e.g. showing where objects are
written and where subprograms are called).

The GNAT_To_Why routine takes a root node of the current compilation unit; you
can read about the abstract syntax tree, or AST in section 2.2.1 The Abstract
Syntax Tree of the GNAT Book (https://www2.adacore.com/gap-static/GNAT_Book/).

To navigate the AST we use routines from these units (from high- to low-level):

1. ``SPARK_Util``
2. ``Sem_Util``
3. ``Einfo``
4. ``Sinfo``

It is impossible to become familiar with all of those routines up front, but it
will happen as you hack. Just keep in mind that we prefer high-level routines,
because they make the code more readable and are more robust (as they abstract
from many "AST anomalies", e.g. renamings as compilation units and renamings as
bodies); also, Entity_Id is preferred over Node_Id (where possible).

Inspired by the frontend Node_Ids and Entity_Ids, flow analysis mostly deals
with Flow_Ids. However, they are heavier that the frontend ones (because they
have a controlled component) and are not kept in tables (because we are not
restricted by the frontend bootstrapping issues and can freely use
Ada.Containers which offer nicer API). This is why instead of local copies of
Flow_Id objects we prefer renamings (this used to be a performance bottleneck,
so those renamings are not a premature optimization).

The need for a dedicated data structure is best illustrated by record
components (e.g. A.B.C), which can't be represented with a single Entity_Id
(instead, the Flow_Id.Node represents A and Flow_Id.Component represents a
vector [B,C]). Note: the Flow_Id contains much more (and arguably its current
design evolved into this and perhaps should be revisited one day); you will
become familiar with this as you hack.

Finally, Flow_Id can wrap around Entity_Name for objects that can't be
represented as an Entity_Id. This is best illustrated by an example: remember
that frontend processes one unit at a time, but the unit might (indirectly)
reference an object from another units:

.. code-block:: ada

   package Other is
      function Proxy return Boolean;
   end;

   package body Other is
      Hidden : Boolean := True;
      function Proxy return Boolean is (Hidden);
   end;

   with Other;
   procedure Main is
      X : Boolean := Other.Proxy;
   ...

When analysing Main the frontend will not see the Hidden object (and this is
the right choice as far as the compilation is concerned), but flow analysis
must recognize that Proxy references Hidden and so Hidden will be represented
as an Entity_Name. The Entity_Name is just an integer (just like Entity_Id), so
it is cheap to test for equality and store in containers. For error reporting
we map Entity_Name to a corresponding string (e.g. "other__hidden").

To have unique representation, if an object can be represented by both
Entity_Name and Entity_Id, we choose Entity_Id, as it makes navigating the AST
and writing assertions easier. The correspondence in maintained in
``SPARK_Register``. However, if we need to know any property of an object known
by an Entity_Name (e.g. its ghost status), we must store it the ALI file in
phase 1 and read it back in phase 2.

This unique representation is convenient for flow analysis, but for proof it is
simpler if Entity_Name is used for any object that should not be "translated"
into Why3. By "translated" we mean "given to the Translate_Entity routine",
which examines what this object is and how it should be represented in Why3.
Such objects include those which are not known by an Entity_Id, those whose
Entity_Id is known but they have not been marked as "in SPARK", and finally,
abstract states; all these objects are represented as "blobs" without any
internal structure in Why3.

Flow graphs
***********

The bulk of flow analysis is based on a widely cited paper "The Program
Dependence Graph and Its Use in Optimization" by Ferrante, et al. We have 5
kinds of graphs, but in practice we primarily look at control flow graph (CFG)
and code that populates it, and on the program dependence graph (PDG) and code
that analyses it. To see the graph use ``--flow-debug`` switch; they will be
placed as gnatprove/*.pdf files. They are prefixed with gg_ and fa_, which
stands for "global generation" and "flow analysis" (or phase 1 and 2),
respectively.

Intuitively, at the top of the graphs are vertices for initial values of
various "places" (in the Common Lisp sense), i.e. formal and global parameters,
local objects, loop variables, etc; record objects are "flattened" into
components.  At the bottom are the final vertices. (Pronounced "tick initial"
and "tick final", respectively, as they resemble Ada attributes.) In the middle
are vertices that correspond to statements in the source code.

Graph vertices are manipulated as integers (for same reasons as Entity_Names).
Internally each vertex represents a Flow_Id, which is quite natural for the
top/bottom vertices, but note that their Flow_Id.Variant is set to
Initial_Value and Final_Value, respectively. Vertices that represent statements
have Flow_Id.Node set to the Node_Id of the statement. Now you see that Flow_Id
can represent quite different things (just like Entity_Id). It might be
confusing at the beginning, but soon stops to be a problem, because typically
routines only deal with one "kind" of thing at a time.

Graphs are created in ``flow-control-flow-graph.adb`` and analysed in
``flow-analysis.adb``.

..  this is about global generation

Global generation
=================

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
an In_Out global. Also, it was not possible to tell which references occur in
proof contexts (e.g. in pragma Assert expressions), or to know which calls
happen for sure, which only conditionally, and which only in proof contexts.
Finally, some references were missing (e.g. in calls to predicates expressions)
while other were spurious (e.g. references in pragma Pre/Post expressions are
believed to belong to the where the pragma occurs, not to the subprogram it
annotates).

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

Visibility
**********

Flow analysis heavily relies on a routine with an almost self-explanatory
signature:

  function Is_Visible (From, To: Node_Id) return Boolean;

We use it to decide access to components of a private type, constituents of an
abstract state, and the Refined_Global/Refined_Depends contracts. This routine
seems innocent, but as soon as generics, (private) child packages and their
combinations come into picture things becomes dreadful.

Proof either doesn't need the visibility info (e.g. the for Refined_Global) or
intentionally ignores it (e.g. for the private types).

Frontend needs this information and it maintains it in a stack-like fashion by
setting & clearing flags on selected entities, e.g. for abstract state it uses
such flags in Has_Partial_Visible_Refinement. Piotr much prefers this approach,
but it can only work with a disciplined top-down analysis of the AST, i.e. like
it is implemented in the frontend. Beware: frontend analyses generic templates
and the stack-like flags seem sufficient there; gnat2why analyses generic
instances, and he has no idea whether stack-like flags would work for us.

Anyway, in gnat2why we are quite far from such a top-down analysis. For
marking, the visibility would mostly matter because of private types (which
marking processes in its own complicated way) and default-initialization (which
it delegates to flow). For flow, historically, Florian & Pavlos were not aware
of the subtlety of this problem and so didn't care about the top-down
discipline; we started to care when rewriting the "generated Global" facility,
but Florian never liked this discipline and argued that top-down processing
would restrict our ability to parallel analysis in the future.

With Florian we decided that given the trouble of converting marking and flow
to top-down style, it will be better to first preprocess the closure of the
compilation unit, including all the generics, their bodies and instances.

The preprocessing gives us a graph with vertices representing 'visibility
regions' and directed edges representing the 'can see' relation. (Tuck rightly
pointed that our vertices are closer to what Ada RM calls 'declarative
regions'.)

This design was drafted by Florian in LaTeX; however, it became depracated by
its implementation, because it missed few corner cases (e.g. generic parents
with generic child units, which btw. are described in a dedicated section of
the archival GNAT Book) and generic formal packages.

Transitive closure algorithm
****************************

Flow analysis does several checks that involve a call graph of the entire
partition, e.g. checks for exclusive accesses to unsynchronized objects from
several tasks. Those checks rely on information that (as of today) is not
captured by subprograms' contracts. Those checks are thus naturally implemented
with a transitive closure of a call graph, which for each caller gives us all
its callees (both direct and indirect ones).

Also, transitive closure is essential for the visibility query, where we start
with visibility links between individual declarative regions but ultimately
need to know whether the source region can "see" the target one. Here instead
of looking for a path in the original graph (which is expensive) we look for an
edge in the pre-computed transitive closure (which is cheap).

We need an efficient implementation of the transitive closure, as otherwise it
would easily become the performance bottleneck. For example, it often happens
that we process ~2000 visibility regions that come from WITHing a predefined
generic unit, whose body itself WITHs several other units.

Apparently, the most comprehensive work on transitive closure algorithms is the
PhD thesis "Efficient Transitive Closure Computation in Large Digraphs" by
Nuutila (1995). He starts with a straightforward but inefficient Warshall’s
algorithm. I tried it as an oracle implementation and it was visibly slow. Its
slightly improved variant, the Warshall’s algorithm, is still quite
straightforward and still inefficient; I didn't try it though.

Then there come algorithms based on strongly connected components; as Nuutila
says "Most of the redundant operations in many algorithms are caused by the
strong components of the input graph, since all vertices in a strong component
have the same successor set" (he supports this claim with a paper reference).

To get the intuition behind those algorithms, you can look at the "A transitive
closure algorithm" by Purdom (1968) and its division into parts: (1) eliminate
cycles, (2) order nodes in the condensed graph, (3) transitive closure and (4)
output. Note that the code in the current Boost library (1.68) and in old but
googlable LEDA (4.2) both have an explicit reference to "topological ordering",
which suggests that they implement some variant of the Purdom's algorithm.
However, both claim a running time complexity of O(|E|*|V|), while descriptions
of the Purdom's algorithm claim it runs in O(|E|+μ|V|), where μ≤|E| is the
number of strongly connected components of this graph.

Finally, Nuutila gets into details of the Tarjan's algorithm for detecting
strongly connected components and gives it as a VISIT procedure pseudocode.
From that he derives a SIMPLE_TC, which actually computes the transitive
closure. This is the algorithm that we implement. The code is dense but short.
Nuutila claims it runs in O(|E|*|V|) "in the worst case when the successor sets
are implemented as ordered lists or ordered binary trees". We implement them
with the standard hashed sets, which appear to be red-black trees, but I think
that his estimate still holds.

Note that Nuutila gives improved variants of both the VISIT procedure (NEWSSC1
and NEWSSC2) and improved variants of the SIMPLE_TC procedure (CR_TC and
STACK_TC). I didn't investigate whether they could be "better" for us; he gives
a comparison of various algorithms, but their complexity seems to depend on
various coefficient that characterize graphs and on the data structures
employed. Neither I try to reimplement or reuse the Boost and LEDA algorithms.

To summarize: we seem to have an O(|E|*|V|) implementation that is on par with
the state-of-the art libraries and so far it is good enough for us.

Renamings of controlled objects
*******************************

In flow analysis we often use renamings like this:

   Var_Def : Flow_Id renames
      A.Variables_Defined (A.Variables_Defined.First);

which might seem minor, but actually is meant to avoid genuine performance
bottlenecks that happened with explicit copies like this:

   Var_Def : constant Flow_Id :=
      A.Variables_Defined (A.Variables_Defined.First);

The issue is that objects like Flow_Id and even more flow vertex attributes
(i.e. elements of the "FA.Atr" map) tend to be "big", i.e. they are records
with container components. Unsurprisingly, local copies of such objects are
expensive.

When written as renaming the code is actually expanded into something like:

   Tmp : constant Container_Instance_Package.Reference :=
      Container_Instance_Package.Element (...);

where the Reference_Type is ultimately a pointer and is very cheap. This type
is declared with Implicit_Dereference aspect, which allows GNAT to magically
use it where an element type would be needed. We could explicitly use this
type in flow, but that would be quite verbose; renamings seem much better.

Handling of protected objects
*****************************

There are few nuances in how protected units are represented in flow. They are
not documented explicitly in the code for historical reasons: the initial
handling was different (and slightly broken), yet equally undocumented. The
code is now fixed, but there were no comments to be fixed and we did not add
any.

The simplest protected type looks like this:

   protected type PT is
      procedure Proc;
   begin
      Comp : Boolean := True;
   end;

and is completed like this:

   protected body PT is
      procedure Proc is
         procedure Inner with Global => (In_Out => PT) is
         begin
            Comp := not Comp;
         end Inner;
      begin
         Comp := not Comp;
         Inner;
      end Proc;
   end protected;

Note the lack of Global aspect on `Proc`, where the current instance of the
*entire* protected object is an _implicit_ formal parameter for this
subprogram; likewise, note the explicit Global aspect on `Inner`. This in turn
dictates the only reasonable representation of Comp as a Flow_Id where

  {Kind => Record_Field; Node => PT; Components => [Comp]}

The same representation is also used for Part_Ofs single concurrent objects and
discriminants (for both task and protected units).

However, when a Part_Of is seen from the outside of a single concurrent unit
(i.e. when we process its object declaration and possibly access from the
elaboration of its enclosing package), we shall represent them as standalone
objects. As of today, this is probably broken (but it is a corner case).
