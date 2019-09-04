.. _manual_proof:

Manual Proof Examples
---------------------

The examples in this section contain properties that are difficult to prove
automatically and thus require more user interaction to prove completely. The
degre of interaction required depends on the difficuly of the proof:

* simple addition of calls to ghost lemmas for arithmetic properties involving
  multiplication, division and modulo operations, as decribed in :ref:`Manual
  Proof Using SPARK Lemma Library`

* more involved addition of ghost code for universally or existentially
  quantified properties on data structures and containers, as described in
  :ref:`Manual Proof Using Ghost Code`

* interaction at the level of Verification Condition formulas in the syntax of
  an interactive prover for arbitrary complex properties, as described in
  :ref:`Manual Proof Using Coq`

* interaction at the level of Verification Condition formulas in the syntax of
  Why3 for arbitrary complex properties, as described in
  :ref:`Manual Proof Using GNAT Studio`

.. _Manual Proof Using SPARK Lemma Library:

Manual Proof Using SPARK Lemma Library
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If the property to prove is part of the :ref:`SPARK Lemma Library`, then manual
proof simply consists in calling the appropriate lemma in your code. For
example, consider the following assertion to prove, where ``X1``, ``X2`` and
``Y`` may be signed or modular positive integers:

.. code-block:: ada

   R1 := X1 / Y;
   R2 := X2 / Y;
   pragma Assert (R1 <= R2);

The property here is the monotonicity of division on positive values. There is
a corresponding lemma for both signed and modular integers, for both 32 bits
and 64 bits integers:

* for signed 32 bits integers, use
  ``SPARK.Integer_Arithmetic_Lemmas.Lemma_Div_Is_Monotonic``
* for signed 64 bits integers, use
  ``SPARK.Long_Integer_Arithmetic_Lemmas.Lemma_Div_Is_Monotonic``
* for modular 32 bits integers, use
  ``SPARK.Mod32_Arithmetic_Lemmas.Lemma_Div_Is_Monotonic``
* for modular 64 bits integers, use
  ``SPARK.Mod64_Arithmetic_Lemmas.Lemma_Div_Is_Monotonic``

For example, the lemma for signed integers has the following signature:

.. code-block:: ada

   procedure Lemma_Div_Is_Monotonic
     (Val1  : Int;
      Val2  : Int;
      Denom : Pos)
   with
     Global => null,
     Pre  => Val1 <= Val2,
     Post => Val1 / Denom <= Val2 / Denom;

Assuming the appropriate library unit is with'ed and used in your code (see
:ref:`SPARK Lemma Library` for details), using the lemma is simply a call to
the ghost procedure ``Lemma_Div_Is_Monotonic``:

.. code-block:: ada

   R1 := X1 / Y;
   R2 := X2 / Y;
   Lemma_Div_Is_Monotonic (X1, X2, Y);
   --  at this program point, the prover knows that R1 <= R2
   --  the following assertion is proved automatically:
   pragma Assert (R1 <= R2);

Note that the lemma may have a precondition, stating in which contexts the
lemma holds, which you will need to prove when calling it. For example, a
precondition check is generated in the code above to show that ``X1 <=
X2``. Similarly, the types of parameters in the lemma may restrict the contexts
in which the lemma holds. For example, the type ``Pos`` for parameter ``Denom``
of ``Lemma_Div_Is_Monotonic`` is the type of positive integers. Hence, a range
check may be generated in the code above to show that ``Y`` is positive.

To apply lemmas to signed or modular integers of different types than the ones
used in the instances provided in the library, just convert the expressions
passed in arguments, as follows:

.. code-block:: ada

   R1 := X1 / Y;
   R2 := X2 / Y;
   Lemma_Div_Is_Monotonic (Integer(X1), Integer(X2), Integer(Y));
   --  at this program point, the prover knows that R1 <= R2
   --  the following assertion is proved automatically:
   pragma Assert (R1 <= R2);

.. _Manual Proof Using User Lemmas:

Manual Proof Using User Lemmas
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If the property to prove is not part of the :ref:`SPARK Lemma Library`, then a
user can easily add it as a separate lemma in her program. For example, suppose
you need to have a proof that a fix list of numbers are prime numbers. This can
be expressed easily in a lemma as follows:

.. code-block:: ada

   function Is_Prime (N : Positive) return Boolean is
     (for all J in Positive range 2 .. N - 1 => N mod J /= 0);

   procedure Number_Is_Prime (N : Positive)
   with
     Ghost,
     Global => null,
     Pre  => N in 15486209 | 15487001 | 15487469,
     Post => Is_Prime (N);

Using the lemma is simply a call to the ghost procedure ``Number_Is_Prime``:

.. code-block:: ada

   Number_Is_Prime (15486209);
   --  at this program point, the prover knows that 15486209 is prime, so
   --  the following assertion is proved automatically:
   pragma Assert (Is_Prime (15486209));

Note that the lemma here has a precondition, which you will need to prove when
calling it. For example, the following incorrect call to the lemma will be
detected as a precondition check failure:

.. code-block:: ada

   Number_Is_Prime (10);  --  check message issued here

Then, the lemma procedure can be either implemented as a null procedure, in
which case |GNATprove| will issue a check message about the unproved
postcondition, which can be justified (see :ref:`Justifying Check Messages`) or
proved with Coq (see :ref:`Manual Proof Using Coq`):

.. code-block:: ada

   procedure Number_Is_Prime (N : Positive) is null;

Or it can be implemented as a normal procedure body with a single assumption:

.. code-block:: ada

   procedure Number_Is_Prime (N : Positive) is
   begin
      pragma Assume (Is_Prime (N));
   end Number_Is_Prime;

Or it can be implemented in some cases as a normal procedure body with ghost
code to achieve fully automatic proof, see :ref:`Manual Proof Using Ghost
Code`.

.. _Manual Proof Using Ghost Code:

Manual Proof Using Ghost Code
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Guiding automatic solvers by adding intermediate assertions is a commonly used
technique. More generally, whole pieces of :ref:`Ghost Code` can be added to
enhance automated reasoning.

Proving Existential Quantification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Existentially quantified properties are difficult to verify for
automatic solvers. Indeed, it requires coming up with a concrete value for
which the property holds and solvers are not good at guessing. As an example,
consider the following program:

.. code-block:: ada

  pragma Assume (A (A'First) = 0 and then A (A'Last) > 0);

  pragma Assert
    (for some I in A'Range =>
       I < A'Last and then A (I) = 0 and then A (I + 1) > 0);

Here we assume that the first element of an array ``A`` is 0, whereas is last
element is positive. In such a case, we are sure that there is an index ``I`` in
the array such ``A (I)`` is 0 but not ``A (I + 1)``. Indeed, we know that ``A``
starts with a non-empty sequence of zeros. The last element of this sequence has
the expected property. However, automatic solvers are unable to prove such a
property automatically because they cannot guess which index they should
consider.
To help them, we can define a ghost function returning a value for which the
property holds, and call it from an assertion:

.. code-block:: ada

  function Find_Pos (A : Nat_Array) return Positive with Ghost,
    Pre  => A (A'First) = 0 and then A (A'Last) > 0,
    Post => Find_Pos’Result in A'First .. A'Last - 1 and then
       A (Find_Pos'Result) = 0 and then A (Find_Pos'Result + 1) > 0;

  pragma Assume (A (A'First) = 0 and then A (A'Last) > 0);
  pragma Assert (Find_Pos (A) in A'Range);
  pragma Assert
    (for some I in A'Range =>
       I < A'Last and then A (I) = 0 and then A (I + 1) > 0);

Automatic solvers are now able to discharge the proof.

Performing Induction
~~~~~~~~~~~~~~~~~~~~

Another difficult point for automated solvers is proof by induction. Though
some automatic solvers do have heuristics allowing them to perform the most
simple inductive proofs, they generally are lost when the induction is less
straightforward. For example, in the example below, we state that the array
``A`` is sorted in two different ways, first by saying that each element is
bigger than the one just before, and then by saying that each element is
bigger than all the ones before:

.. code-block:: ada

  pragma Assume
    (for all I in A'Range =>
      (if I > A'First then A (I) > A (I - 1)));
  pragma Assert
    (for all I in A'Range =>
      (for all J in A'Range => (if I > J then A (I) > A (J))));

The second assertion is provable from the first one by induction over the
number of elements separating ``I`` and ``J``, but automatic solvers are unable
to verify this code. To help them, we can use a ghost loop. In the loop
invariant, we say that the property holds for all indexes ``I`` and ``J``
separated by less than ``K`` elements:

.. code-block:: ada

  procedure Prove_Sorted (A : Nat_Array) with Ghost is
  begin
    for K in 0 .. A'Length loop
      pragma Loop_Invariant
        (for all I in A'Range => (for all J in A'Range =>
            (if I > J and then I - J <= K then A (I) > A (J))));
    end loop;
  end Prove_Sorted;

|GNATprove| will verify that the invariant holds in two steps, first it will
show that the property holds at the first iteration, and then that, if it holds
at a given iteration, then it also holds at the next
(see :ref:`Loop Invariants`). Both proofs are straightforward using the
assumption.

Note that we have introduced a ghost subprogram above to contain the loop.
This will allow the compiler to recognize that this loop is ghost, so that it
can be entirely removed when assertions are disabled.

If ``Prove_Sorted`` is declared locally to the subprogram that we want to
verify, it is not necessary to supply a contract for it, as local subprograms
with no contracts are inlined (see :ref:`Contextual Analysis of Subprograms
Without Contracts`). We can still choose to provide such a contract to turn
``Prove_Sorted`` into a lemma (see :ref:`Manual Proof Using User Lemmas`).

A Concrete Example: a Sort Algorithm
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We show how to prove the correctness of a sorting procedure on arrays using
ghost code. In particular, we want to show that the sorted array is a permuation
of the input array.
A common way to define permutations is to use the number of occurrences of
elements in the array, defined inductively over the size of its array parameter
(but it is not the only one, see :ref:`Ghost Variables`):

.. literalinclude:: examples/sort_types.ads
   :language: ada
   :linenos:

.. literalinclude:: examples/perm.ads
   :language: ada
   :linenos:

Note that Occ was introduced as a wrapper around the recursive definition of
Occ_Def. This is to work around a current limitation of the tool that only
introduces axioms for postconditions of non-recursive functions (to avoid
possibly introducing unsound axioms that would not be detected by the tool).

The only property of the function Occ required to prove that swapping two
elements of an array is in fact a permutation, is the way Occ is modified when
updating a value of the array.

There is no native construction for axioms in SPARK 2014. As a workaround, a
ghost subprogram, named "lemma subprogram", can be introduced with the desired
property as a postcondition. An instance of the axiom will then be available
whenever the subprogram is called. Notice that an explicit call to the lemma
subprogram with the proper arguments is required whenever an instance of the
axiom is needed, like in manual proofs in an interactive theorem prover. Here
is how a lemma subprogram can be defined for the desired property of Occ:

.. literalinclude:: examples/perm-lemma_subprograms.ads
   :language: ada

This "axiom" can then be used to prove an implementation of the selection
sort algorithm. Lemma subprograms need to be explicitely called for every
natural. To achieve that, a loop is introduced. The inductive proof necessary
to demonstrate the universally quantified formula is then achieved thanks to
the loop invariant, playing the role of an induction hypothesis:

.. literalinclude:: examples/sort.adb
   :language: ada

.. literalinclude:: examples/sort.ads
   :language: ada

The procedure Selection_Sort can be verified using |GNATprove|, with the
default prover CVC4, in less than 1s per verification condition.

.. literalinclude:: results/sort.prove
   :language: none

To complete the verification of our selection sort, the only remaining issue
is the correctness of the axiom for Occ. It can be discharged using the
definition of Occ. Since this definition is recursive, the proof requires
induction, which is not normally in the reach of an automated prover. For
|GNATprove| to verify it, it must be implemented using recursive calls on
itself to assert the induction hypothesis. Note that the proof of the
lemma is then conditioned to the termination of the lemma functions, which
currently cannot be verified by |GNATprove|.

.. literalinclude:: examples/perm-lemma_subprograms.adb
   :language: ada

|GNATprove| proves automatically all checks on the final program, with a small
timeout of 1s for the default automatic prover CVC4.

.. literalinclude:: results/perm-lemma_subprograms.prove
   :language: none

.. _Manual Proof Using Coq:

Manual Proof Using Coq
^^^^^^^^^^^^^^^^^^^^^^

This section presents a simple example of how to prove interactively a check
with an interactive prover like Coq when |GNATprove| fails to prove it
automatically (for installation of Coq, see also: :ref:`Coq`). Here is a simple
|SPARK| procedure:

.. literalinclude:: examples/nonlinear.adb
   :language: ada
   :linenos:

When only the Alt-Ergo prover is used, |GNATprove| does not prove automatically
the postcondition of the procedure, even when increasing the value of the
timeout:

.. literalinclude:: results/nonlinear.prove
   :language: none

This is expected, as the automatic prover Alt-Ergo has only a simple support
for non-linear integer arithmetic. More generally, it is a known difficulty for
all automatic provers, although, in the case above, using prover CVC4 is enough
to prove automatically the postcondition of procedure ``Nonlinear``. We will
use this case to demonstrate the use of a manual prover, as an example of what
can be done when automatic provers fail to prove a check. We will use Coq here.

The Coq input file associated to this postcondition can be produced by either
selecting :menuselection:`SPARK --> Prove Check` and specifying ``Coq`` as
alternate prover in GNAT Studio or by executing on the command-line:

    ``gnatprove -P <prj_file>.gpr --limit-line=nonlinear.adb:4:11:VC_POSTCONDITION --prover=Coq``

The generated file contains many definitions and axioms that can be used in the
proof, in addition to the ones in Coq standard library. The property we want
to prove is at the end of the file:

.. code-block:: coq

  Theorem WP_parameter_def :
    forall (r1:Z) (r2:Z) (o:Z) (o1:Z) (result:Z)
           (r11:Z) (result1:Z) (r21:Z) (r12:Z) (r22:Z)
           (r13:Z) (r23:Z),
      ((in_range1 x)
       /\ ((in_range1 y)
       /\ ((in_range1 z)
       /\ (((0%Z <= 2147483647%Z)%Z -> (in_range r1))
       /\ (((0%Z <= 2147483647%Z)%Z -> (in_range r2))
       /\ ((z < y)%Z
       /\ (((((o = (ZArith.BinInt.Z.quot x y))
       /\ (in_range (ZArith.BinInt.Z.quot x y)))
       /\ (((mk_int__ref result) = (mk_int__ref r1))
       /\ (r11 = o)))
       /\ (((o1 = (ZArith.BinInt.Z.quot x z))
       /\ (in_range (ZArith.BinInt.Z.quot x z)))
       /\ ((result1 = r2)
       /\ (r21 = o1))))
       /\ (((r21 = r22)
       /\ (r11 = r12))
       /\ ((r23 = r21)
       /\ (r13 = r11)))))))))) ->
       (r12 <= r22)%Z.

    intros r1 r2 o o1 result r11 result1 r21 r12 r22 r13 r23
    (h1,(h2,(h3,(h4,(h5,(h6,((((h7,h8),(h9,h10)),((h11,h12),
    (h13,h14))),((h15,h16),(h17,h18))))))))).

  Qed.

From the ``forall`` to the first ``.`` we can see the expression of what must
be proved, also called the goal. The proof starts right after the dot and ends
with the ``Qed`` keyword.  Proofs in Coq are done with the help of different
tactics which will change the state of the current goal. The first tactic
(automatically added) here is ``intros``, which allows to "extract" variables
and hypotheses from the current goal and add them to the current
environment. Each parameter to the ``intros`` tactic is the name that the
extracted element will have in the new environment.  The ``intros`` tactic here
puts all universally quantified variables and all hypotheses in the
environment. The goal is reduced to a simple inequality, with all potentially
useful information in the environment.

Here is the state of the proof as displayed in a suitable IDE for Coq::

  1 subgoal

    r1, r2, o, o1, result, r11, result1, r21, r12, r22, r13, r23 : int
    h1 : in_range1 x
    h2 : in_range1 y
    h3 : in_range1 z
    h4 : (0 <= 2147483647)%Z -> in_range r1
    h5 : (0 <= 2147483647)%Z -> in_range r2
    h6 : (z < y)%Z
    h7 : o = (x ÷ y)%Z
    h8 : in_range (x ÷ y)
    h9 : mk_int__ref result = mk_int__ref r1
    h10 : r11 = o
    h11 : o1 = (x ÷ z)%Z
    h12 : in_range (x ÷ z)
    h13 : result1 = r2
    h14 : r21 = o1
    h15 : r21 = r22
    h16 : r11 = r12
    h17 : r23 = r21
    h18 : r13 = r11
    ______________________________________(1/1)
    (r12 <= r22)%Z

Some expresions are enclosed in ``()%Z``, which means that they are dealing
with relative integers. This is necessarily in order to use the operators
(e.g. ``<`` or ``+``) on relative integers instead of using the associated Coq
function or to declare a relative integer constant (e.g. ``0%Z``).

Next, we can use the ``subst`` tactic to automaticaly replace variables by
terms to which they are equal (as stated by the hypotheses in the current
environment) and clean the environment of replaced variables. Here, we can get
rid of many variables at once with ``subst o o1 result1 r11 r12 r21 r22 r23
r13.`` (note the presence of the ``.`` at the end of each tactic). The new
state is::

  1 subgoal

    r1, r2, result : int
    h1 : in_range1 x
    h2 : in_range1 y
    h3 : in_range1 z
    h4 : (0 <= 2147483647)%Z -> in_range r1
    h5 : (0 <= 2147483647)%Z -> in_range r2
    h6 : (z < y)%Z
    h8 : in_range (x ÷ y)
    h9 : mk_int__ref result = mk_int__ref r1
    h12 : in_range (x ÷ z)
    ______________________________________(1/1)
    (x ÷ y <= x ÷ z)%Z

At this state, the hypotheses alone are not enough to prove the goal without
proving properties about ``÷`` and ``<`` operators. It is necessary to use
theorems from the Coq standard library. Coq provides a command ``SearchAbout``
to find theorems and definition concerning its argument. For instance, to find
the theorems referring to the operator ``÷``, we use ``SearchAbout Z.quot.``,
where ``Z.quot`` is the underlying function for the ``÷`` operator.  Among the
theorems displayed, the conclusion (the rightmost term separated by ``->``
operator) of one of them seems to match our current goal::

   Z.quot_le_compat_l:
     forall p q r : int, (0 <= p)%Z -> (0 < q <= r)%Z -> (p ÷ r <= p ÷ q)%Z

The tactic ``apply`` allows the use of a theorem or an hypothesis on the
current goal. Here we use: ``apply Z.quot_le_compat_l.``. This tactic will try
to match the different variables of the theorem with the terms present in the
goal. If it succeeds, one subgoal per hypothesis in the theorem will be
generated to verify that the terms matched with the theorem variables satisfy
the hypotheses on those variables required by the theorem.  In this
case, ``p`` is matched with ``x``, ``q`` with ``z`` and
``r`` with ``y`` and the new state is::

  2 subgoals

    r1, r2, result : int
    h1 : in_range1 x
    h2 : in_range1 y
    h3 : in_range1 z
    h4 : (0 <= 2147483647)%Z -> in_range r1
    h5 : (0 <= 2147483647)%Z -> in_range r2
    h6 : (z < y)%Z
    h8 : in_range (x ÷ y)
    h9 : mk_int__ref result = mk_int__ref r1
    h12 : in_range (x ÷ z)
    ______________________________________(1/2)
    (0 <= x)%Z
    ______________________________________(2/2)
    (0 < z <= y)%Z

As expected, there are two subgoals, one per hypothesis of the theorem. Once
the first subgoal is proved, the rest of the script will automatically apply to
the second one.  Now, if we look back at the |SPARK| code, ``X`` is of type
``Positive`` so ``X`` is greater than 0 and ``in_rangeN`` (where N is a number)
are predicates generated by |SPARK| to state the range of a value from a ranged subtype
interpreted as a relative integer in Coq. Here, the predicate ``in_range1``
provides the property needed to prove the first subgoal which is that "All
elements of subtype positive have their integer interpretation in the range
1 .. (2³¹ - 1)".  However, the goal does not match exactly the predicate, because
one is a comparison with 0, while the other is a comparison
with 1. Transitivity on "lesser or equal" relation is needed to prove this
goal, of course this is provided in Coq's standard library:

.. code-block:: coq

  Lemma Zle_trans : forall n m p:Z, (n <= m)%Z -> (m <= p)%Z -> (n <= p)%Z.

Since the lemma's conclusion contains only two variables while it uses three,
using tactic ``apply Zle_trans.`` will generate an error stating that Coq was
not able to find a term for the variable ``m``.  In this case, ``m`` needs to
be instantiated explicitly, here with the value 1: ``apply Zle_trans with (m:=
1%Z).`` There are two new subgoals, one to prove that ``0 <= 1`` and the other
that ``1 <= x``::

  3 subgoals

    r1, r2, result : int
    h1 : in_range1 x
    h2 : in_range1 y
    h3 : in_range1 z
    h4 : (0 <= 2147483647)%Z -> in_range r1
    h5 : (0 <= 2147483647)%Z -> in_range r2
    h6 : (z < y)%Z
    h8 : in_range (x ÷ y)
    h9 : mk_int__ref result = mk_int__ref r1
    h12 : in_range (x ÷ z)
    ______________________________________(1/3)
    (0 <= 1)%Z
    ______________________________________(2/3)
    (1 <= x)%Z
    ______________________________________(3/3)
    (0 < z <= y)%Z

To prove that ``0 <= 1``, the theorem ``Lemma Zle_0_1 : (0 <= 1)%Z.`` is used.
``apply Zle_0_1`` will not generate any new subgoals since it does not contain
implications. Coq passes to the next subgoal::

  2 subgoals

    r1, r2, result : int
    h1 : in_range1 x
    h2 : in_range1 y
    h3 : in_range1 z
    h4 : (0 <= 2147483647)%Z -> in_range r1
    h5 : (0 <= 2147483647)%Z -> in_range r2
    h6 : (z < y)%Z
    h8 : in_range (x ÷ y)
    h9 : mk_int__ref result = mk_int__ref r1
    h12 : in_range (x ÷ z)
    ______________________________________(1/2)
    (1 <= x)%Z
    ______________________________________(2/2)
    (0 < z <= y)%Z

This goal is now adapted to the ``in_range1`` definition with ``h1`` which does
not introduce subgoals, so the subgoal 1 is fully proved, and all that remains
is subgoal 2::

  1 subgoal

    r1, r2, result : int
    h1 : in_range1 x
    h2 : in_range1 y
    h3 : in_range1 z
    h4 : (0 <= 2147483647)%Z -> in_range r1
    h5 : (0 <= 2147483647)%Z -> in_range r2
    h6 : (z < y)%Z
    h8 : in_range (x ÷ y)
    h9 : mk_int__ref result = mk_int__ref r1
    h12 : in_range (x ÷ z)
    ______________________________________(1/1)
    (0 < z <= y)%Z

Transitivity is needed again, as well as ``in_range1``.  In the previous
subgoal, every step was detailed in order to show how the tactic ``apply``
worked. Now, let's see that proof doesn't have to be this detailed. The first
thing to do is to add the fact that ``1 <= z`` to the current
environment: ``unfold in_range1 in h3.`` will add the range of ``z`` as
an hypthesis in the environment::

  1 subgoal

    r1, r2, result : int
    h1 : in_range1 x
    h2 : in_range1 y
    h3 : (1 <= z <= 2147483647)%Z
    h4 : (0 <= 2147483647)%Z -> in_range r1
    h5 : (0 <= 2147483647)%Z -> in_range r2
    h6 : (z < y)%Z
    h8 : in_range (x ÷ y)
    h9 : mk_int__ref result = mk_int__ref r1
    h12 : in_range (x ÷ z)
    ______________________________________(1/1)
    (0 < z <= y)%Z

At this point, the goal can be solved simply using the ``omega.`` tactic.
``omega`` is a tactic made to facilitate the verification of properties about
relative integers equalities and inequalities. It uses a predefined set of
theorems and the hypotheses present in the current environment to try to solve
the current goal. ``omega`` either solves the goal or, if it fails, it does not
generate any subgoals.  The benefit of the latter way is that there are less
steps than with the previous subgoal for a more complicated goal (there are two
inequalities in the second subgoal) and we do not have to find the different
theorems we need to solve the goal without omega.

Finally, here is the final version of the proof script for the postcondition:

.. code-block:: coq

  Theorem WP_parameter_def :
    forall (r1:Z) (r2:Z) (o:Z) (o1:Z) (result:Z)
           (r11:Z) (result1:Z) (r21:Z) (r12:Z) (r22:Z)
           (r13:Z) (r23:Z),
      ((in_range1 x)
       /\ ((in_range1 y)
       /\ ((in_range1 z)
       /\ (((0%Z <= 2147483647%Z)%Z -> (in_range r1))
       /\ (((0%Z <= 2147483647%Z)%Z -> (in_range r2))
       /\ ((z < y)%Z
       /\ (((((o = (ZArith.BinInt.Z.quot x y))
       /\ (in_range (ZArith.BinInt.Z.quot x y)))
       /\ (((mk_int__ref result) = (mk_int__ref r1))
       /\ (r11 = o)))
       /\ (((o1 = (ZArith.BinInt.Z.quot x z))
       /\ (in_range (ZArith.BinInt.Z.quot x z)))
       /\ ((result1 = r2)
       /\ (r21 = o1))))
       /\ (((r21 = r22)
       /\ (r11 = r12))
       /\ ((r23 = r21)
       /\ (r13 = r11)))))))))) ->
       (r12 <= r22)%Z.

    intros r1 r2 o o1 result r11 result1 r21 r12 r22 r13 r23
    (h1,(h2,(h3,(h4,(h5,(h6,((((h7,h8),(h9,h10)),((h11,h12),
    (h13,h14))),((h15,h16),(h17,h18))))))))).

  subst o o1 result1 r11 r12 r21 r22 r23 r13.
  apply Z.quot_le_compat_l.
    apply Zle_trans with (m:=1%Z).
      (* 0 <= 1 *)
      apply Zle_0_1.
      (* 1 <= x *)
      unfold in_range1 in h1.
      apply h1.
    (* 0 < z <= y *)
    unfold in_range1 in h3.
    omega.
  Qed.

To check and save the proof:

     ``gnatprove -P <prj_file>.gpr --limit-line=nonlinear.adb:4:11:VC_POSTCONDITION --prover=Coq --report=all``

Now running |GNATprove| on the project should confirm that all checks are
proved::

  nonlinear.adb:4:11: info: postcondition proved
  nonlinear.adb:7:12: info: range check proved
  nonlinear.adb:7:12: info: division check proved
  nonlinear.adb:8:12: info: range check proved
  nonlinear.adb:8:12: info: division check proved


.. _Manual Proof Using GNAT Studio:

Manual Proof Using GNAT Studio
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This section presents a simple example of how to prove interactively a check
with the manual proof feature. We reuse here the example presented in
section :ref:`Manual Proof Using Coq`. We launch the Manual Proof on the failed
check at::

  nonlinear.adb:4:11:VC_POSTCONDITION

Right click on the corresponding location in the ``Locations`` terminal of GNAT Studio
and select the menu
:menuselection:`SPARK --> Start Manual Proof`. The manual proof interface
immediately starts. Both the ``Proof Tree`` and the ``Verification Condition``
(VC) appear in separate windows. In particular, the VC ends with the
following::

  axiom H : dynamic_property first last X

  axiom H1 : dynamic_property first last Y

  axiom H2 : dynamic_property first last Z

  axiom H3 : first1 <= last1 -> dynamic_property1 first1 last1 R14

  axiom H4 : first1 <= last1 -> dynamic_property1 first1 last1 R23

  axiom H5 : Y > Z

  axiom H6 : o1 = div X Y /\ in_range1 (div X Y)

  axiom H7 : result = R1

  axiom H8 : R13 = o1

  axiom H9 : o = div X Z /\ in_range1 (div X Z)

  axiom H10 : result1 = R23

  axiom H11 : R22 = o

  axiom H12 : R22 = R21

  axiom H13 : R13 = R12

  axiom H14 : R2 = R22

  axiom H15 : R11 = R13

  goal WP_parameter def : R12 <= R21

The Verification Condition is very similar to the one generated for Coq (as
expected: the check is the same). As soon as the menus appear, the user can
start using transformations to simplify the goal thus helping automatic provers.
We will start the description of a complete proof for this lemma using only
``altergo``.
At first, we want to remove the equalities between constants that make the VC
very difficult to read. These equalities were generated by the weakest
precondition algorithm. They can be safely removed by ``subst`` and
``subst_all``. In ``Manual Proof`` console, type::

  subst_all

The transformation node was added to the Proof Tree and the current node is now
changed making your transformation appear and the new Verification Condition to
prove has been simplified::

  axiom H : dynamic_property first last X

  axiom H1 : dynamic_property first last Y

  axiom H2 : dynamic_property first last Z

  axiom H3 : first1 <= last1 -> dynamic_property1 first1 last1 R14

  axiom H4 : first1 <= last1 -> dynamic_property1 first1 last1 R23

  axiom H5 : Y > Z

  axiom H6 : o1 = div X Y /\ in_range1 (div X Y)

  axiom H7 : o = div X Z /\ in_range1 (div X Z)

  ----------------------------- Goal ---------------------------

  goal WP_parameter def : o1 <= o

We should also have replaced the value of ``o1`` and ``o`` in the goal. These
were not replaced because ``H6`` and ``H7`` are conjunctions. We can destruct
both hypotheses ``H6`` and ``H7`` in order to make the equalities appear at
toplevel::

  destruct H6

Then::

  subst o1

After simplifications, the goal is the following::

  axiom H2 : dynamic_property first last X

  axiom H3 : dynamic_property first last Y

  axiom H4 : dynamic_property first last Z

  axiom H5 : first1 <= last1 -> dynamic_property1 first1 last1 R14

  axiom H6 : first1 <= last1 -> dynamic_property1 first1 last1 R23

  axiom H7 : Y > Z

  axiom H1 : in_range1 (div X Y)

  axiom H : in_range1 (div X Z)

  ----------------------------- Goal ---------------------------

  goal WP_parameter def : div X Y <= div X Z

This is more readable but ``altergo`` still does not manage to prove it::

  altergo

answers ``Unknown`` as seen in the Proof Tree.

We need to investigate further what we know about ``div``, and what would be
useful to prove the goal::

  search div

returns in the ``Manual Proof`` console::

  function div (x:int) (y:int) : int = div1 x y

  axiom H1 : in_range1 (div X Y)

  axiom H : in_range1 (div X Z)

So, ``div`` is actually a shortcut for a function named ``div1``. Let's search
for this one::

  search div1

Now, we get a lot of axioms about ``div`` and ``mod`` as expected. In
particular, the axiom ``Div_mod`` looks interesting::

  axiom Div_mod :
     forall x:int, y:int. not y = 0 -> x = ((y * div1 x y) + mod1 x y)

Perhaps, it is a good idea to instantiate this axiom with X and Y (respectively
X and Z) and see what is provable from there::

  instantiate Div_mod X,Y

A new hypothesis appears in the context::

  axiom Div_mod : not Y = 0 -> X = ((Y * div1 X Y) + mod1 X Y)

After some struggling with those hypotheses, it looks like they won't actually
help proving the goal. Let's remove these hypotheses::

  remove Div_mod

Alternatively, we can go back to the node above the current one in the Proof
Tree by clicking on it. We can also remove the transformation node
corresponding to the use of ``instantiate`` by selecting it and writing in
``Manual Proof`` console::

  Remove

The actual proof is going to use an additional lemma that we are going to
introduce with ``assert``. The Coq proof uses this exact same lemma inside the
proof of ``Z.quot_le_compat_l``. We could have expected ``altergo`` to have
this lemma inside its theories but, currently, it does not::

  assert (forall q a b:int. 0<b -> 0<a -> b*q <= a -> q <= div1 a b)

So, two new nodes appear below the current one (the first to prove the formula
we just wrote and the second adding it as an hypothesis). We are going to prove
this ``assert`` by induction on the unbounded integer q (the base case is 0)::

  induction q from 0

Both new goals can be discharged by ``altergo``: this small lemma is
proven. Now, we can use it in our proof. We begin by unfolding ``div`` to make
``div1`` appear::

  unfold div

Then we can apply our new lemma::

  apply h

We are left with the following three subgoals to prove::

  goal G : (Z * div1 X Y) <= X

  goal G : 0 < X

  goal G : 0 < Z

``altergo`` proves the positivity of X and Z easily but it does not find a proof
for the first subgoal. We are going to prove this one by transitivity of ``less
or equal`` using ``Y * div1 X Y``. Currently, we don't have a transformation to
apply the transitivity directly so we assert it::

  assert ((Y * div1 X Y <= X && Z) * ((div1 X Y) <= Y * div1 X Y))

To make two goals of this conjunction, we are using::

  split_goal_wp

The left part is provable by ``altergo``. On the second part, we are going to
apply an axiom ``CompatOrderMult`` we found by querying what is known about the
multiplication::

  search (*)

We apply it to the current goal::

  apply CompatOrderMult

The remaining goals can all be proven by ``altergo``. This closes the proof. A
popup should appear asking if the user wants to save and exit. Answer no
because we want to make the proof cleaner (you can still save it by writing
``Save`` in ``Manual Proof`` console). Select a node and type::

  clean

All attempted proof that did not succeed are erased and only the successful
proofs remain. The proof can now be saved and manual proofs menus closed by
clicking on
:menuselection:`SPARK --> Exit Manual Proof` from the menu.
The proof is complete and |GNATprove| can be called again on the whole project to
check that the former failing check is now understood as proved by
|GNATprove|.
