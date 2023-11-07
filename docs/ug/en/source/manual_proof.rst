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

.. index:: manual proof; using the lemma library
           lemma library; example of use

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

.. index:: manual proof; using lemmas
           ghost code; manual proof using lemmas

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

.. index:: manual proof; using ghost code
           ghost code; manual proof

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
ghost code. In particular, we want to show that the sorted array is a
permutation of the input array.
A common way to define permutations is to encode the number of occurrences of
each element in the array as a multiset, constructed inductively over the size
of its array parameter (but it is not the only one, see :ref:`Ghost Variables`).
The :ref:`Functional Containers Library` of SPARK provides an implementation
of multisets that we use here:

.. literalinclude:: /examples/ug__long__perm/nat_multisets.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__long__perm/sort_types.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/ug__long__perm/perm.ads
   :language: ada
   :linenos:

The only property of the function ``Occurrences`` required to prove that
swapping two elements of an array is in fact a permutation, is the way
``Occurrences`` is modified when updating a value of the array.

There is no native construction for axioms in SPARK. As a workaround, a
ghost subprogram, named "lemma subprogram", can be introduced with the desired
property as a postcondition. An instance of the axiom will then be available
whenever the subprogram is called. Notice that an explicit call to the lemma
subprogram with the proper arguments is required whenever an instance of the
axiom is needed, like in manual proofs in an interactive theorem prover. Here
is how a lemma subprogram can be defined for the desired property of
``Occurrences``:

.. literalinclude:: /examples/ug__long__perm/perm-lemma_subprograms.ads
   :language: ada

This "axiom" can then be used to prove an implementation of the selection
sort algorithm. The lemma subprogram needs to be explicitely called when needed:

.. literalinclude:: /examples/ug__long__sort/sort.adb
   :language: ada

.. literalinclude:: /examples/ug__long__sort/sort.ads
   :language: ada

The procedure ``Selection_Sort`` can be verified using |GNATprove| at level 2.

.. literalinclude:: /examples/ug__long__sort/test.out
   :language: none

To complete the verification of our selection sort, the only remaining issue
is the correctness of the axiom for ``Occurrences``. It can be discharged using
its definition. Since this definition is recursive, the proof requires
induction, which is not normally in the reach of an automated prover. For
|GNATprove| to verify it, it must be implemented using recursive calls on
itself to assert the induction hypothesis. Note that the proof of the
lemma is then conditioned to the termination of the lemma functions, which
can be verified by |GNATprove| using a :ref:`Subprogram Variant`.

.. literalinclude:: /examples/ug__long__perm/perm-lemma_subprograms.adb
   :language: ada

|GNATprove| proves automatically all checks on the final program at level 2.

.. literalinclude:: /examples/ug__long__perm/test.out
   :language: none

.. index:: manual proof; using Coq

Manual Proof Using Coq
^^^^^^^^^^^^^^^^^^^^^^

This section presents a simple example of how to prove interactively a check
with an interactive prover like Coq when |GNATprove| fails to prove it
automatically (for installation of Coq, see also: :ref:`Coq`). Here is a simple
|SPARK| procedure:

.. literalinclude:: /examples/ug__nonlinear/nonlinear.adb
   :language: ada
   :linenos:

When only the Alt-Ergo prover is used, |GNATprove| does not prove automatically
the postcondition of the procedure, even when increasing the value of the
timeout:

.. literalinclude:: /examples/ug__nonlinear/test.out
   :language: none

This is expected, as the automatic prover Alt-Ergo has only a simple support
for non-linear integer arithmetic. More generally, it is a known difficulty for
all automatic provers, although, in the case above, using prover cvc5 is enough
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

  Theorem def'vc :
    forall (r1:Numbers.BinNums.Z) (r2:Numbers.BinNums.Z),
    dynamic_invariant1 x Init.Datatypes.true Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true ->
    dynamic_invariant1 y Init.Datatypes.true Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true ->
    dynamic_invariant1 z Init.Datatypes.true Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true ->
    dynamic_invariant r1 Init.Datatypes.false Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true ->
    dynamic_invariant r2 Init.Datatypes.false Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true -> (z < y)%Z ->
    forall (r11:Numbers.BinNums.Z), (r11 = (ZArith.BinInt.Z.quot x y)) ->
    forall (r21:Numbers.BinNums.Z), (r21 = (ZArith.BinInt.Z.quot x z)) ->
    (r11 <= r21)%Z.
  Proof.
  intros r1 r2 h1 h2 h3 h4 h5 h6 r11 h7 r21 h8.

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
  r1, r2 : int
  h1 : dynamic_invariant1 x true false true true
  h2 : dynamic_invariant1 y true false true true
  h3 : dynamic_invariant1 z true false true true
  h4 : dynamic_invariant r1 false false true true
  h5 : dynamic_invariant r2 false false true true
  h6 : (z < y)%Z
  r11 : int
  h7 : r11 = (x ÷ y)%Z
  r21 : int
  h8 : r21 = (x ÷ z)%Z
  ______________________________________(1/1)
  (r11 <= r21)%Z

Some expresions are enclosed in ``()%Z``, which means that they are dealing
with relative integers. This is necessarily in order to use the operators
(e.g. ``<`` or ``+``) on relative integers instead of using the associated Coq
function or to declare a relative integer constant (e.g. ``0%Z``).

Next, we can use the ``subst`` tactic to automaticaly replace variables by
terms to which they are equal (as stated by the hypotheses in the current
environment) and clean the environment of replaced variables. Here, we can get
rid of many variables at once with ``subst.`` (note the presence of the ``.``
at the end of each tactic). The new state is::

  1 subgoal
  r1, r2 : int
  h1 : dynamic_invariant1 x true false true true
  h2 : dynamic_invariant1 y true false true true
  h3 : dynamic_invariant1 z true false true true
  h4 : dynamic_invariant r1 false false true true
  h5 : dynamic_invariant r2 false false true true
  h6 : (z < y)%Z
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
  r1, r2 : int
  h1 : dynamic_invariant1 x true false true true
  h2 : dynamic_invariant1 y true false true true
  h3 : dynamic_invariant1 z true false true true
  h4 : dynamic_invariant r1 false false true true
  h5 : dynamic_invariant r2 false false true true
  h6 : (z < y)%Z
  ______________________________________(1/2)
  (0 <= x)%Z
  ______________________________________(2/2)
  (0 < z <= y)%Z

As expected, there are two subgoals, one per hypothesis of the theorem. Once
the first subgoal is proved, the rest of the script will automatically apply to
the second one.  Now, if we look back at the |SPARK| code, ``X`` is of type
``Positive`` so ``X`` is greater than 0 and ``dynamic_invariantN`` (where N is
a number) are predicates generated by |SPARK| to state the range of a value
from a ranged subtype interpreted as a relative integer in Coq. Here, the
predicate ``dynamic_invariant1`` provides the property needed to prove the first
subgoal which is that "All elements of subtype positive have their integer
interpretation in the range 1 .. (2³¹ - 1)". To be able to see the definition
of ``dynamic_invariant1`` in ``h1``, we can use the ``unfold`` tactic of Coq. We
need to supply the name of the predicate to unfold:
``unfold dynamic_invariant1 in h1``. After this unfolding, we get a new
predicate ``in_range1`` that we can unfold too so that ``h1`` is now
``true = true \/ (1 <= 2147483647)%Z -> (1 <= x <= 2147483647)%Z``.

We see now that the goal does not match
exactly the hypothesis, because
one is a comparison with 0, while the other is a comparison
with 1. Transitivity on "lesser or equal" relation is needed to prove this
goal, of course this is provided in Coq's standard library:

.. code-block:: coq

  Lemma Z.le_trans : forall n m p:Z, (n <= m)%Z -> (m <= p)%Z -> (n <= p)%Z.

Since the lemma's conclusion contains only two variables while it uses three,
using tactic ``apply Z.le_trans.`` will generate an error stating that Coq was
not able to find a term for the variable ``m``.  In this case, ``m`` needs to
be instantiated explicitly, here with the value 1: ``apply Zle_trans with (m:=
1%Z).`` There are two new subgoals, one to prove that ``0 <= 1`` and the other
that ``1 <= x``::

  3 subgoals
  r1, r2 : int
  h1 : true = true \/ (1 <= 2147483647)%Z -> (1 <= x <= 2147483647)%Z
  h2 : dynamic_invariant1 y true false true true
  h3 : dynamic_invariant1 z true false true true
  h4 : dynamic_invariant r1 false false true true
  h5 : dynamic_invariant r2 false false true true
  h6 : (z < y)%Z
  ______________________________________(1/3)
  (0 <= 1)%Z
  ______________________________________(2/3)
  (1 <= x)%Z
  ______________________________________(3/3)
  (0 < z <= y)%Z

To prove that ``0 <= 1``, the theorem ``Lemma Z.le_0_1 : (0 <= 1)%Z.`` is used.
``apply Z.le_0_1`` will not generate any new subgoals since it does not contain
implications. Coq passes to the next subgoal::

  2 subgoals
  r1, r2 : int
  h1 : true = true \/ (1 <= 2147483647)%Z -> (1 <= x <= 2147483647)%Z
  h2 : dynamic_invariant1 y true false true true
  h3 : dynamic_invariant1 z true false true true
  h4 : dynamic_invariant r1 false false true true
  h5 : dynamic_invariant r2 false false true true
  h6 : (z < y)%Z
  ______________________________________(1/2)
  (1 <= x)%Z
  ______________________________________(2/2)
  (0 < z <= y)%Z

This goal is now adapted to the range information in hypothesis ``h1``. It
introduces a subgoal which is the disjunction in the hypothesis of ``h1``.
To prove this disjunction, we need to tell Coq which operand we want to prove.
Here, both are obviously true. Let's choose the left one using the tactic
``left.``. We are left with only the equality to prove::

  2 subgoals
  r1, r2 : int
  h1 : true = true \/ (1 <= 2147483647)%Z -> (1 <= x <= 2147483647)%Z
  h2 : dynamic_invariant1 y true false true true
  h3 : dynamic_invariant1 z true false true true
  h4 : dynamic_invariant r1 false false true true
  h5 : dynamic_invariant r2 false false true true
  h6 : (z < y)%Z
  ______________________________________(1/2)
  true = true
  ______________________________________(2/2)
  (0 < z <= y)%Z

This can be discharged using ``apply eq_refl.`` to apply the reflexivity
axiom of equality.
Now the subgoal 1 is fully proved, and all that remains
is subgoal 2::

  1 subgoal
  r1, r2 : int
  h1 : dynamic_invariant1 x true false true true
  h2 : dynamic_invariant1 y true false true true
  h3 : dynamic_invariant1 z true false true true
  h4 : dynamic_invariant r1 false false true true
  h5 : dynamic_invariant r2 false false true true
  h6 : (z < y)%Z
  ______________________________________(1/1)
  (0 < z <= y)%Z

Transitivity is needed again, as well as the definition of
``dynamic_invariant1``.  In the previous
subgoal, every step was detailed in order to show how the tactic ``apply``
worked. Now, let's see that proof doesn't have to be this detailed. The first
thing to do is to add the fact that ``1 <= z`` to the current
environment: ``unfold dynamic_invariant1, in_range1 in h3.`` will add the range
of ``z`` as an hypthesis in the environment::

  1 subgoal
  r1, r2 : int
  h1 : dynamic_invariant1 x true false true true
  h2 : dynamic_invariant1 y true false true true
  h3 : true = true \/ (1 <= 2147483647)%Z -> (1 <= z <= 2147483647)%Z
  h4 : dynamic_invariant r1 false false true true
  h5 : dynamic_invariant r2 false false true true
  h6 : (z < y)%Z
  ______________________________________(1/1)
  (0 < z <= y)%Z

At this point, the goal can be solved simply using the ``intuition.`` tactic.
``intuition`` is an automatic tactic of Coq implementing a decision procedure
for some simple goals. It either solves the goal or, if it fails, it does not
generate any subgoals.  The benefit of the latter way is that there are less
steps than with the previous subgoal for a more complicated goal (there are two
inequalities in the second subgoal) and we do not have to find the different
theorems we need to solve the goal without ``intuition``.

Finally, here is the final version of the proof script for the postcondition:

.. code-block:: coq

  Theorem def'vc :
    forall (r1:Numbers.BinNums.Z) (r2:Numbers.BinNums.Z),
    dynamic_invariant1 x Init.Datatypes.true Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true ->
    dynamic_invariant1 y Init.Datatypes.true Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true ->
    dynamic_invariant1 z Init.Datatypes.true Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true ->
    dynamic_invariant r1 Init.Datatypes.false Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true ->
    dynamic_invariant r2 Init.Datatypes.false Init.Datatypes.false
    Init.Datatypes.true Init.Datatypes.true -> (z < y)%Z ->
    forall (r11:Numbers.BinNums.Z), (r11 = (ZArith.BinInt.Z.quot x y)) ->
    forall (r21:Numbers.BinNums.Z), (r21 = (ZArith.BinInt.Z.quot x z)) ->
    (r11 <= r21)%Z.
  Proof.
  intros r1 r2 h1 h2 h3 h4 h5 h6 r11 h7 r21 h8.
  subst.
  apply Z.quot_le_compat_l.
    apply Z.le_trans with (m:=1%Z).
      (* 0 <= x *)
    - apply Z.le_0_1.
      (* 1 <= x *)
    - unfold dynamic_invariant1, in_range1 in h1.
      apply h1. left. apply eq_refl.
    (* 0 < z <= y *)
    - unfold dynamic_invariant1, in_range1 in h3.
      intuition.
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
