.. _usage scenarios for spark:

***************************
Usage Scenarios for |SPARK|
***************************

..  Note that, in many cases, ad-hoc data structures based on pointers can be
    replaced by the use of standard Ada containers (vectors, lists, sets, maps,
    etc.) Although the implementation of standard containers is not in |SPARK|,
    we have defined a slightly modified version of these targeted at formal
    verification. These formal containers are implemented in the GNAT standard
    library. These alternative containers are typical of the tradeoffs implicit
    in |SPARK|: favor automatic formal verification as much as possible, at the
    cost of minor adaptations to the code.

This section discusses in more detail the various types of verification that
|GNATprove| may be used for, ranging from flow analysis to formal verification
of correctness properties.

.. _flow analysis of unannotated code:

Flow Analysis of Unannotated Code
---------------------------------

When |GNATprove| is run in ``flow`` mode it performs flow analysis to check
for errors relating to initialization of, and information flow between,
variables. If the code under analysis does not include global or depends
annotations then this analysis will detect errors relating to:
 
 - the use of uninitialized variables;
 - unused variables;
 - unused assignments;
 - ineffective statements.

(Note that the terms "unused" and "ineffective" both mean that the construct
in question ultimately has no impact on any output from the subprogram.)

This corresponds to the "generative" or "retrospective" style of analysis.
For example, in the code shown below |GNATprove| warns that the initial value
of ``X`` is unused.

.. code-block:: ada
   :linenos:

   procedure P (X : in out Integer) is
   begin
      X := 10;
   end P;

If this is the intended behaviour then the warning can be eliminated by
changing the mode of the parameter to ``out`` as has been done below.
But in this version the result of the first assignment is overwritten
by the second assignment, so |GNATprove| warns that the initial
assignment is unused.

.. code-block:: ada
   :linenos:

   procedure P (X : out Integer) is
   begin
      X := 0;
      X := 10;
   end P;

The previous examples were instances of warnings, but the use of
uninitialized variables is considered more serious and results in
an error being reported, as in the case below.

.. code-block:: ada
   :linenos:

   procedure P (X : out Integer) is
      T : Integer;
   begin
      X := T;
   end P;

Here |GNATprove| reports the error that ``T`` might not be initialized.
The reason for the word "might" is that the flow analyser cannot, in
general, determine whether the use of the uninitialized variable is on
a non-executable path. To do so would require proof, and it is possible
that this may be done in a future version of the tools.

Flow analysis will also detect unused variables as in this example
where |GNATprove| warns that ``T`` is unused.

.. code-block:: ada
   :linenos:

   procedure P (X : out Integer) is
      T : Integer;
   begin
      X := 0;
   end P;

.. _flow analysis of code with globals:

Flow Analysis of Code with Globals 
----------------------------------

If the user has added global annotations to the code then |GNATprove|
is able to go further with flow analysis and report any discrepancies
between the contract specified in the annotation and the executable
code. Here, ``P`` has an annotation specifying that the global ``G``
is an input (but not an output).

.. code-block:: ada
   :linenos:

   procedure P
      with Global => (Input => G)
   is
   begin
      G := G + 1;
   end P;

|GNATprove| reports that ``G`` must be a global output. This corresponds
to the constructive analysis style, where the contract must be provided
by the user before the executable code is written (or at least simultaneously
with writing the code). Note that if the global aspect was not present then
|GNATprove| would synthesize a global contract that matched the code and no
error would be reported. This corresponds to the generative or retrospective
style of analysis which has the advantage of not requiring the user to add
the annotations but the disadvantage of not being able to detect cases where
the user-supplied annotation is correct but the code is incorrect. Note also
that for the code shown above |GNATprove| reports one more warning, that
initial value of ``G`` is unused. This may seem surprising at first glance,
because the initial value of ``G`` must be read in order to increment it.
However, the global aspect states that ``G`` is not an output, so the
assignment statement is not considered to affect any outputs and the new
value of ``G`` is unused. Both of these messages disappear when the global
annotation is corrected and the code is reanalysed.

.. _flow analysis of code with depends:

Flow Analysis of Code with Depends 
----------------------------------

If the user has specified depends annotations then |GNATprove| can go still
further with the flow analysis it performs. This typically corresponds to a
scenario where the constructive analysis style is being used and the extra
analysis is considered to be valuable, for example when it is important to
see the flows of information between inputs and outputs on a security or
safety related system. The presence of depends annotations, which specify
the relationships between inputs and outputs of a subprogram, allows
|GNATprove| to check the specified dependency against the executable code
and report any discrepancies.

Here is our old friend ``Swap`` which is intended to exchange the values
of its two integer parameters, ``X`` and ``Y``. The depends annotation
correctly captures this specification, but the user has made a mistake in
the implementation.

.. code-block:: ada
   :linenos:

   procedure Swap (X, Y : in out Integer)
      with Depends => (X => Y, Y => X)
   is
      T : Integer;
   begin
      T := Y; -- should be T := X;
      X := Y;
      Y := T;
   end Swap;

|GNATprove| analyses the body, calculates the actual dependencies between
inputs and outputs, compares these with the specified dependencies and
reports the following warnings:

.. code-block:: ada

   q.adb:4:20: warning: unused initial value of "X" [unused_initial_value]
   q.adb:5:12: warning: missing dependency "null => X" [depends_null]
   q.adb:5:32: warning: missing dependency "Y => Y" [depends_missing]
   q.adb:5:32: warning: incorrect dependency "Y => X" [depends_wrong]

Note that the style of these messages implies that the code is correct and
the depends annotation should be fixed. However it should be borne in
mind that where a discrepancy between the code and the depends annotation
is detected it is generally up to the user to decide whether the code or
the annotation is incorrect and to take the appropriate corrective action.
In this case it is the code which is wrong, and correcting the first
assignment statement will eliminate all of the errors listed above.

It is important to note that the inclusion of user-supplied global and
depends annotations is not an "all or nothing" decision that must be
applied rigidly across all files. The tools are flexible enough to make
use of, and check against, the annotations where they are present, and
to synthesize them otherwise. There are various usage scenarios where
there might be a mix of annotated and unannotated code, for example:

 - Some projects, working in the constructive style, might opt to write
   global and depends annotations for subprograms at the lower levels
   of the calling hierarchy, but only use globals at the higher levels.
   The depends annotations tend to give more value at the lower levels
   of the hierarchy but can become more unweildy and less informative at
   the higher levels.

 - Some projects might opt to write the global and depends aspects for
   the most critical areas of the software, but leave the less critical
   parts unannotated.

 - If an existing Ada project is adopting |SPARK|, annotations might be
   added to all newly written code, but not retrospectively applied to
   existing code. Or such a project might choose to gradually introduce
   annotations to the code base as existing modules are modified, rather
   than having to go for a "big bang" approach of applying annotations to
   everything at the same time.

These are just some of the possible usage scenarios. Yet more combinations
can be envisaged when we consider that the proof contracts may also be
specified or not, depending on the circumstances of the project. The
following sections consider how |GNATprove| can be used for formal
verification.

.. _absence of run-time errors:

Absence of Run-Time Errors
--------------------------

This verification activity is available in mode ``prove``.
|GNATprove| automatically generates Verification Conditions (VCs) whose proof
ensures that the code of the subprogram being analyzed will not violate any of
the following checks when it is executed:

* overflow check
* range check
* index check
* division check
* discriminant check
* length check

The precise meaning of these checks is given by the Ada Language Reference
Manual. An (*overflow check*) violation occurs when the result of an arithmetic
operation cannot be represented in the base type (usually a machine integer)
for this operation. A (*range check*) violation occurs when a value does not
respect the range constraint for its type. An (*index check*) violation occurs
when the value used to index into an array does not fit between the array
bounds. A (*division check*) violation occurs when the divisor of a division
operation (or ``rem`` or ``mod``) is zero. A *discriminant check* violation
occurs when the discriminant(s) of a discriminant record does not have the
expected value for a given operation. A *length check* violation occurs when an
array does not have the expected length.

|GNATprove| also takes into account checks that occur within preconditions.
VCs are generated to show that preconditions of subprograms can never raise
run-time errors, whatever the calling context. In order to achieve this
property for preconditions, the user should in general guard all expressions
which may raise a ``Constraint_Error`` in Ada, such as array accesses and
arithmetic operations.

These guards may take the form desired by the user. In particular, no guard is
necessary if the operation cannot raise a run-time error, e.g. due to the
ranges of variables involved. As an example, consider the following subprogram
specifications:

.. code-block:: ada
   :linenos:

   procedure Not_Guarded (X, Y : Integer) with
     Pre => X / Y > 0;

   procedure Guarded_And_Then (X, Y : Integer) with
     Pre => Y /= 0 and then X / Y > 0;

   procedure Guarded_If_Then (X, Y : Integer) with
     Pre => (if Y /= 0 then X / Y > 0);

   procedure No_Need_For_Guard (X, Y : Positive) with
     Pre => X / Y > 0;

|GNATprove| is able to show that only the precondition of the first of these
specifications could raise a run-time error::

   p.ads:4:15: division check not proved
   p.ads:7:31: (info) division check proved
   p.ads:10:31: (info) division check proved
   p.ads:13:15: (info) division check proved

Notice also that division might also overflow here, if ``X`` is the minimal
integer value and ``Y`` is ``-1`` (standard 32-bits integers are assumed
here). |GNATprove| checks this overflow condition, and it detects that only
the precondition of the last of these specifications cannot raise a run-time
error::

   p.ads:4:15: overflow check not proved
   p.ads:7:31: overflow check not proved
   p.ads:10:31: overflow check not proved
   p.ads:13:15: (info) overflow check proved

Similar VCs are generated to ensure that postconditions and assertions are
also free from run-time exceptions.

.. _functional verification:

Functional Verification
-----------------------

This verification activity is available in mode ``prove``.  |GNATprove| generates
VCs to prove that all subprograms called in the code of a subprogram analyzed
have their precondition satisfied at the point of call. It also generates VCs
to prove that the postcondition of the subprogram analyzed is satisfied.

In order to prove such VCs, the user may have to write loop invariants, for
which specific VCs are generated, to prove that the loop invariant is initially
valid (*loop invariant initiation*) and that it is preserved through the loop
(*loop invariant preservation*).

