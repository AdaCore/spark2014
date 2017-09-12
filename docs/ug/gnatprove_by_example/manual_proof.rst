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
technique. More generally, whole pieces of ghost code, that is, code that do not
affect the program's output, can be added to enhance automated reasoning. This section presents an example on which complex proofs involving in particular inductive reasoning can be verified automatically using ghost code.

This example focuses on proving the correctness of a sorting procedure on arrays
implementing a selection sort, and, more precisely, that it always returns a
permutation of the original array.

A common way to define permutations is to use the number of occurrences of
elements in the array, defined inductively over the size of its array parameter:

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

This section presents a simple example how to prove interactively a check with
an interactive prover like Coq when |GNATprove| fails to prove it
automatically. Here is a simple |SPARK| procedure:

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
alternate prover in GPS or by executing on the command-line:

    ``gnatprove -P <prj_file>.gpr --limit-line=nonlinear.adb:4:11:VC_POSTCONDITION --prover=Coq``

The generated file contains many definitions and axioms that can be used in the
proof, in addition to the ones in Coq standard library. The property we want
to prove is at the end of the file:

.. code-block:: coq

  Theorem WP_parameter_def :
  forall (o:natural) (o1:natural) (r1:natural) (r2:natural) (r11:natural)
         (r21:natural),
     ((to_int1 z) < (to_int1 y))%Z ->
     (((to_int o) = (ZArith.BinInt.Z.quot (to_int1 x) (to_int1 y))) ->
      ((r1 = o) ->
       ((r1 = r11) ->
        (((to_int o1) = (ZArith.BinInt.Z.quot (to_int1 x) (to_int1 z))) ->
         ((r2 = o1) -> ((r2 = r21) -> ((to_int r11) <= (to_int r21))%Z)))))).
  intros o o1 r1 r2 r11 r21 h1 h2 h3 h4 h5 h6 h7.

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

  1 subgoals, subgoal 1 (ID 331)

    o : natural
    o1 : natural
    r1 : natural
    r2 : natural
    r11 : natural
    r21 : natural
    h1 : (to_int1 z < to_int1 y)%Z
    h2 : to_int o = (to_int1 x ÷ to_int1 y)%Z
    h3 : r1 = o
    h4 : r1 = r11
    h5 : to_int o1 = (to_int1 x ÷ to_int1 z)%Z
    h6 : r2 = o1
    h7 : r2 = r21
    ============================
     (to_int r11 <= to_int r21)%Z

Some expresions are enclosed in ``()%Z``, which means that they are dealing
with relative integers. This is necessarily in order to use the operators
(e.g. ``<`` or ``+``) on relative integers instead of using the associated Coq
function or to declare a relative integer constant (e.g. ``0%Z``).

Next, we can use the ``subst`` tactic to automaticaly replace variables by
terms to which they are equal (as stated by the hypotheses in the current
environment) and clean the environment of replaced variables. Here, we can
get rid of ``r11``, ``r21``, ``r1`` and ``r2``: ``subst r11 r21 r1 r2.`` (note
the presence of the ``.`` at the end of each tactic). The new state is::

  1 subgoals, subgoal 1 (ID 343)

    o : natural
    o1 : natural
    h1 : (to_int1 z < to_int1 y)%Z
    h2 : to_int o = (to_int1 x ÷ to_int1 y)%Z
    h5 : to_int o1 = (to_int1 x ÷ to_int1 z)%Z
    ============================
     (to_int o <= to_int o1)%Z

We could not get rid of ``o`` and ``o1`` with ``subst`` because we don't know
their values, but we know a relation between ``to_int o``, ``to_int1 x`` and
``to_int1 y``. We can use the tactic ``rewrite`` to replace one side of an
equality by the other side. If we have an hypothesis ``H : a = b`` in the
environment, ``rewrite H.`` and ``rewrite -> H.`` will replace all occurences
of ``a`` by ``b`` in the current goal and ``rewrite <- H.`` will replace all
occurences of ``b`` by ``a`` (``a`` and ``b`` are terms, not necessarily just
variables). You can also rewrite terms in other hypotheses instead of the
current goal: ``rewrite H in H2.``. In this case, to replace ``to_int o`` and
``to_int o1``, we use ``rewrite h2. rewrite h5.``::

  1 subgoals, subgoal 1 (ID 345)

    o : natural
    o1 : natural
    h1 : (to_int1 z < to_int1 y)%Z
    h2 : to_int o = (to_int1 x ÷ to_int1 y)%Z
    h5 : to_int o1 = (to_int1 x ÷ to_int1 z)%Z
    ============================
     (to_int1 x ÷ to_int1 y <= to_int1 x ÷ to_int1 z)%Z

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
case, ``p`` is matched with ``to_int1 x``, ``q`` with ``to_int1 z`` and
``r`` with ``to_int1 y`` and the new state is::

  2 subgoals, subgoal 1 (ID 346)

    o : natural
    o1 : natural
    h1 : (to_int1 z < to_int1 y)%Z
    h2 : to_int o = (to_int1 x ÷ to_int1 y)%Z
    h5 : to_int o1 = (to_int1 x ÷ to_int1 z)%Z
    ============================
     (0 <= to_int1 x)%Z

  subgoal 2 (ID 347) is:
   (0 < to_int1 z <= to_int1 y)%Z

As expected, there are two subgoals, one per hypothesis of the theorem. Once
the first subgoal is proved, the rest of the script will automatically apply to
the second one.  Now, if we look back at the |SPARK| code, ``X`` is of type
``Positive`` so ``X`` is greater than 0 and ``to_intN`` (where N is a number)
are functions generated by |SPARK| to interpret a ranged type element as a
relative integer. Some axioms associated with these functions provide the range
bounds. ``SearchAbout <type>.`` should provide you with all the theorems and
functions defined for the desired type. Here, the axiom ``range_axiom1``
provides the property needed to prove the first subgoal which is that "All
elements of type positive have their integer interpretation in the range
1 .. (2³¹ - 1)".  However, the goal does not match exactly the axiom, because
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
that ``1 <= to_int1 x``::

  3 subgoals, subgoal 1 (ID 348)

    o : natural
    o1 : natural
    h1 : (to_int1 z < to_int1 y)%Z
    h2 : to_int o = (to_int1 x ÷ to_int1 y)%Z
    h5 : to_int o1 = (to_int1 x ÷ to_int1 z)%Z
    ============================
     (0 <= 1)%Z

  subgoal 2 (ID 349) is:
   (1 <= to_int1 x)%Z
  subgoal 3 (ID 347) is:
   (0 < to_int1 z <= to_int1 y)%Z

To prove that ``0 <= 1``, the theorem ``Lemma Zle_0_1 : (0 <= 1)%Z.`` is used.
``apply Zle_0_1`` will not generate any new subgoals since it does not contain
implications. Coq passes to the next subgoal::

  2 subgoals, subgoal 1 (ID 349)

    o : natural
    o1 : natural
    h1 : (to_int1 z < to_int1 y)%Z
    h2 : to_int o = (to_int1 x ÷ to_int1 y)%Z
    h5 : to_int o1 = (to_int1 x ÷ to_int1 z)%Z
    ============================
     (1 <= to_int1 x)%Z

  subgoal 2 (ID 347) is:
   (0 < to_int1 z <= to_int1 y)%Z

This goal is now adapted to the ``range_axiom1`` which does not introduce
subgoals, so the subgoal 1 is fully proved, and all that remains is subgoal 2::

  1 subgoals, subgoal 1 (ID 360)

    o : natural
    o1 : natural
    h1 : (to_int1 z < to_int1 y)%Z
    h2 : to_int o = (to_int1 x ÷ to_int1 y)%Z
    h5 : to_int o1 = (to_int1 x ÷ to_int1 z)%Z
    H : (1 <= to_int1 z)%Z
    H0 : (to_int1 z <= 2147483647)%Z
    ============================
     (0 < to_int1 z <= to_int1 y)%Z

Transitivity is needed again, as well as ``range_axiom1``.  In the previous
subgoal, every step was detailed in order to show how the tactic ``apply``
worked. Now, let's see that proof doesn't have to be this detailed. The first
thing to do is to add the fact that ``1 <= to_int1 z`` to the current
environment: ``destruct range_axiom1 with (x:= z).`` or ``destruct
(range_axiom1 z).`` will separate the conjunctions and add them as different
hypotheses in the environment::

  1 subgoals, subgoal 1 (ID 360)

    o : natural
    o1 : natural
    h1 : (to_int1 z < to_int1 y)%Z
    h2 : to_int o = (to_int1 x ÷ to_int1 y)%Z
    h5 : to_int o1 = (to_int1 x ÷ to_int1 z)%Z
    H : (1 <= to_int1 z)%Z
    H0 : (to_int1 z <= 2147483647)%Z
    ============================
     (0 < to_int1 z <= to_int1 y)%Z

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
  forall (o:natural) (o1:natural) (r1:natural) (r2:natural) (r11:natural)
         (r21:natural),
   ((to_int1 z) < (to_int1 y))%Z ->
   (((to_int o) = (ZArith.BinInt.Z.quot (to_int1 x) (to_int1 y))) ->
    ((r1 = o) ->
     ((r1 = r11) ->
      (((to_int o1) = (ZArith.BinInt.Z.quot (to_int1 x) (to_int1 z))) ->
       ((r2 = o1) -> ((r2 = r21) -> ((to_int r11) <= (to_int r21))%Z)))))).
  intros o o1 r1 r2 r11 r21 h1 h2 h3 h4 h5 h6 h7.
  subst r11 r21 r1 r2.
  rewrite h2. rewrite h5.
  apply Z.quot_le_compat_l.
    (* 0 <= x *)
    apply Zle_trans with (m := 1%Z).
      (* 0 <= 1 *)
      apply Zle_0_1.
      (* 1 <= x *)
      apply range_axiom1.
    (* 0 < z <= y *)
     destruct (range_axiom1 z).
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
