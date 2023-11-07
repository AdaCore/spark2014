The goal of the Gold level is to ensure key integrity properties such as
maintaining critical data invariants throughout execution and guaranteeing that
transitions between states follow a specified safety automaton. Typically
these properties derive from software requirements. Together with the
Silver level, these goals ensure program integrity, that is, the program
executes within safe boundaries: the control flow of the program is
correctly programmed and cannot be circumvented through run-time errors
and data cannot be corrupted.

SPARK has a number of useful features for specifying both data
invariants and control flow constraints:

.. index:: Type predicate
.. index:: Precondition
.. index:: Postcondition

* Type predicates reflect properties that should always be true of any object of
  the type.
* Preconditions reflect properties that should always hold on subprogram entry.
* Postconditions reflect properties that should always hold on subprogram exit.

.. index:: Proof mode (for GNATprove)
.. index:: Info message (from GNATprove)
.. index:: Check message (from GNATprove)
.. index:: Unit testing

These features can be verified statically by running GNATprove in proof
mode, similarly to what was done at the Silver level. At every point where
a violation of the property may occur, GNATprove issues either an 'info'
message, verifying that the property always holds, or a 'check' message
about a possible violation. Of course, a benefit of proving properties is
that they don't need to be tested, which can be used to reduce or
completely eliminate unit testing.

.. index:: Integration testing
.. index:: -gnata switch (compiler)
.. index:: pragma Assertion_Policy

These features can also be used to augment integration testing with dynamic
verification of key integrity properties. To enable
this additional verification during execution, you can use either the
compilation switch ``-gnata`` (which enables verification of all invariants and
contracts at run time) or ``pragma Assertion_Policy`` (which enables a subset
of the verification) either inside the code (so that it applies to the
code that follows in the current unit) or in a pragma configuration file
(so that it applies to the entire program).

.. rubric:: Benefits

The SPARK code is guaranteed to respect key integrity properties as well as
being free from all the defects already detected at the Bronze and Silver
levels: no reads of uninitialized variables, no possible interference
between parameters and global variables, no unintended access to global
variables, and no run-time errors. This is a unique feature of SPARK that
is not found in other programming languages. In particular, such guarantees
may be used in a safety case to make reliability claims.

.. index:: DO-178C / ED-12C
.. index:: EN 50128, CENELEC EN 50128
.. index:: IEC 61508
.. index:: Proof (as alternative to unit testing)

The effort in achieving this level of confidence based on proof is
relatively low compared to the effort required to achieve the same level
based on testing. Indeed, confidence based on testing has to rely on an
extensive testing strategy. Certification standards
define criteria for approaching comprehensive testing, such as Modified
Condition / Decision Coverage (MC/DC), which are expensive to
achieve. Some certification standards allow the use of proof as a
replacement for certain forms of testing, in particular DO-178C in avionics, EN 50128 in
railway and IEC 61508 for functional safety. Obtaining proofs, as done in
SPARK, can thus be used as a cost-effective alternative to unit testing.

.. rubric:: Impact on Process

.. index:: Contract-based programming

In a high-DAL certification context where proof replaces testing and
independence is required between certain development/verification activities,
one person can define the architecture and low-level requirements
(package specs) and another person can develop the corresponding bodies
and use GNATprove for verification. Using a common syntax/semantics
-- Ada 2012 contracts -- for both the specs/requirements and the code
facilitates communication between the two activities and makes it easier
for the same person(s) to play different roles at different times.

Depending on the complexity of the property being proven, it may be more or
less costly to add the necessary contracts on types and subprograms and to
achieve complete automatic proof by interacting with the tool. This
typically requires some experience with the tool, which can be gained by
training and practice. Thus not all developers should be
tasked with developing such contracts and proofs, but instead a few
developers should be designated for this task.

.. index:: Loop_Invariant; for Gold level

As with the proof of AoRTE at Silver level, special treatment is required
for loops, such as the addition of loop invariants to prove
properties inside and after the loop. Details are
presented in the SPARK User's Guide, together with examples of loops and their
corresponding loop invariants.

.. rubric:: Costs and Limitations

The analysis may take a long time, up to a few hours, on large programs,
but it is guaranteed to terminate. It may also take more or less time
depending on the proof strategy adopted (as indicated by the switches
passed to GNATprove). Proof is, by construction, limited to local
understanding of the code, which requires using sufficiently precise types
of variables and some preconditions and postconditions on subprograms to
communicate relevant properties to their callers.

.. index:: Limitations of provers

Even if a property is provable, automatic provers may fail to prove it due
to limitations of the heuristic techniques they employ. In
practice, these limitations are mostly visible on non-linear integer
arithmetic (such as division and modulo) and on floating-point arithmetic.

Some properties might not be easily expressible in the form of data
invariants and subprogram contracts, for example properties of execution
traces or temporal properties. Other properties may require the use of
non-intrusive instrumentation in the form of ghost code.
