Manual Proof Examples
---------------------

This sections presents presents simple examples where Alt-Ergo isn't able to
prove some |SPARK| VCs which can be proved with an interactive prover like Coq.

Non-Linear Arithmetic
^^^^^^^^^^^^^^^^^^^^^

Here is a simple |SPARK| procedure::

  procedure Nonlinear (X, Y, Z : Positive; R1, R2 : out Natural) with
    SPARK_Mode,
    Pre  => Y > Z,
    Post => R1 <= R2
  is
  begin
    R1 := X / Y;
    R2 := X / Z;
  end Nonlinear;

when running |GNATprove|, we see that Alt-Ergo fails to prove the
post-condition of the procedure::

  nonlinear.adb:4:11: warning: postcondition might fail, requires R1 <= R2
  nonlinear.adb:7:12: info: range check proved
  nonlinear.adb:7:12: info: division check proved
  nonlinear.adb:8:12: info: range check proved
  nonlinear.adb:8:12: info: division check proved

The Coq file associated to this post-condition can be produced either selecting
:menuselection:`SPARK --> Prove Check` and specifying ``Coq`` as alternate
prover in GPS or by executing:

    ``gnatprove -P <prj_file>.gpr --limit-line=nonlinear.adb:4:11:VC_POSTCONDITION --prover=Coq``

The generated file contains many definitions and axioms that can be used in the
proof in addition to the ones in Coq's stantard library. At the end of the file
is the goal we want to prove::

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
be proved. The proof start right after it and is ended by the ``Qed`` keyword.
Proofs in Coq are done with the help of different tactics which will change the
state of the current goal. The first tactic (automatically added) here is
``intros``, it allows to "extract" variables (e.g. [ | forall (x : type), T]
will become [x : type | T]) and hypothesis (i.e. [ | T1 -> T2] will become
[ H : T1 | T2 ]) from the current goal and add them to the current environment,
each parameter to the intros tactic is the name the "extracted" element will
have in the environment.
The intros tactic here put all universally quantified variables and all
hypothesis in the environment allowing you to work on a "simple" goal with all
potentially usefull information in the environment.

So here's the state of the proof as can be seen in an adapted Coq IDE::

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

Some expresions are enclosed in ``()%Z``, this means that they are dealing with
relative integers, this is necessary in order to use the operators (e.g. ``<``
or ``+``) on relative integers instead of using the associated Coq function or
to declare a relative integer constant (e.g. ``0%Z``).

Next, we can use the ``subst`` tactic to automaticaly replace variables by
terms to which they are equal (as stated by the hypothesis in the current
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

We couldn't get rid of ``o`` and ``o1`` with subst because we don't know their
values, but we know a relation between ``(to_int o)`` and x and y. To use an
equality to replace one of its terms by the other we use the tactic
``rewrite``. If we have an hypothesis ``H : a = b`` in the environment,
``rewrite H.`` and ``rewrite -> H.`` will replace all occurences of ``a`` by
``b`` in the current goal and ``rewrite <- H.`` will replace all occurences of
``b`` by ``a`` (``a`` and ``b`` are terms, not necesarly just variables). You
can also rewrite terms in other hypothesis instead of the current goal:
``rewrite H in H2.``. In this case, to replace ``(to_int o)`` and
``(to_int o1)`` we use ``rewrite h2. rewrite h5.``::

  1 subgoals, subgoal 1 (ID 345)

    o : natural
    o1 : natural
    h1 : (to_int1 z < to_int1 y)%Z
    h2 : to_int o = (to_int1 x ÷ to_int1 y)%Z
    h5 : to_int o1 = (to_int1 x ÷ to_int1 z)%Z
    ============================
     (to_int1 x ÷ to_int1 y <= to_int1 x ÷ to_int1 z)%Z

At this state, the hypothesis alone are not enough to prove the goal without
proving properties about ``÷`` and ``<`` operators. It is wiser to use theorems
from the Coq standard library. Coq provides a command ``SearchAbout`` to find
theorems and definition concerning its argument. For instance, to find the
theorems refering to the operator ``÷``, we use ``SearchAbout Z.quot.``,
``Z.quot`` is the underlying function of the ``÷`` operator.
Among the theorems, the conclusion (the rightmost term separated
by ``->`` operator) of this one seems to fit our current goal::

  Z.quot_le_compat_l:
     forall p q r : int, (0 <= p)%Z -> (0 < q <= r)%Z -> (p ÷ r <= p ÷ q)%Z

The tactic ``apply`` allows the use of a theorem or a hypothesis on the current
goal: ``apply Z.quot_le_compat_l.``, this tactic will try to match the
different variables of the theorem with the terms present in the goal and if
it succeeds, one subgoal per hypothesis in the theorem will be generated to
verify that the terms matched with the theorem variables satify the hypothesis
on those variables that are required by the theorem.
In this case, ``p`` is matched with ``(to_int1 x)``, ``q`` with ``(to_int1 z)``
and ``r`` with ``(to_int1 y)`` and the new state is::

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

As expected, there are two subgoals. Once the first subgoal is proved, the rest
of the script will automatically apply to the second one.
Now, if we look back at the |SPARK| code, ``X`` is of type ``Positive`` so
``X`` is greater than 0 and ``to_intN`` (where N is a number) are functions
generated by |SPARK| to interpret a ranged type element as a relative integer,
associated with these functions are defined some axioms
(``SearchAbout <type>.`` should provide you with all the theorems and functions
defined for the desired type).
The axiom ``range_axiom1`` provides the property needed to prove the first
subgoal which is that "All elements of type positive have their integer
interpretation in the range 1 .. (2³¹ - 1)".
Here, the goal doesn't match the axiom, one is a comparision to 0, the other
to 1. Transitivity on "lesser or equal" relation is needed to prove this goal,
of course this is provided in Coq's standard library::

  Lemma Zle_trans : forall n m p:Z, (n <= m)%Z -> (m <= p)%Z -> (n <= p)%Z.

In the lemma, the conclusion contains only two of it's variables while it
uses three. Then, using tactic ``apply Zle_trans.`` will generate an error
stating that Coq wasn't able to find a term for its variable ``m``.
In this case, ``m`` is instantiated with the intermediate value 1:
``apply Zle_trans with (m:= 1%Z).``
There are two new subgoals, one to prove that ``0 <= 1`` and the other that
``1 <= to_int1 x``::

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
``apply Zle_0_1`` won't generate any new subgoals since it does not contain
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

The goal is adapted to the ``range_axiom1``, again, the application
``apply range_axiom1`` won't introduce subgoals::

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

Here, again transitivity will be needed as well as the ``range_axiom1``.
In the previous subgoal, every step was detailed in order to show how the
tactic ``apply`` worked. Now, let's see that proof doesn't have to be this
exhaustive. The first thing to do is to add the fact that ``1 <= to_int1 z`` to
the current environment: ``destruct range_axiom1 with (x:= z).`` or
``destruct (range_axiom1 z).`` will separate the conjunctions and add them as
different hypothesis in the environment::

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
``omega`` is a tactic made to facilitate the verification of properties
about relative integers equalities and inequalities. It uses it's predefined
set of theorems and the hypothesis present in the current environment and
tries to solve the current goal. ``omega`` either solves the goal or it fails
, it will not generate any subgoals.
The benefit of the latter way is that there are less steps than with the
previous subgoal for a more complicated goal (there are two inequalities in the
second subgoal) and we don't have to find the different theorems we need to
solve the goal without omega.

Finally, here is the final version of the proof script for the post-condition::

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
