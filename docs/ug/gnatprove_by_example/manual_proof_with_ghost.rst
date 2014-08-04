Manual Proof Using Ghost Code
-----------------------------

Guiding automatic solvers by adding intermediate assertions is a commonly used
technique. More generally, whole pieces of ghost code, that is, code that do not
affect the program's output, can be added to enhance automated reasoning. This section presents an example on which complex proofs involving in particular inductive reasoning can be verified automatically using ghost code.

This example focuses on proving the correctness of a sorting procedure on arrays
implementing a selection sort, and, more precisely, that it always returns a
permutation of the original array.

A common way to define permutations is to use the number of occurrences of
elements in the array, defined inductively over the size of its array parameter:

.. literalinclude:: gnatprove_by_example/examples/perm.ads
   :language: ada
   :linenos:

Note that Occ was introduced as a wrapper around the recursive definition of
Occ_Def. This is to work around a current limitation of the tool that only
introduces axioms for postconditions of non-recursive functions (to avoid
possibly introducing unsound axioms that would not be detected by the tool).

Two properties of the function Occ are required to prove that swapping two
elements of an array is in fact a permutation, namely, the preservation of Occ
on extensionally equal arrays (that is, arrays which are equal at every index)
and the way Occ is modified when updating a value of the array. 

There is no native construction for axioms in SPARK 2014. As a workaround, a
ghost subprogram, named "lemma subprogram", can be introduced with the desired
property as a postcondition. An instance of the axiom will then be available
whenever the subprogram is called. Notice that an explicit call to the lemma
subprogram with the proper arguments is required whenever an instance of the
axiom is needed, like in manual proofs in an interactive theorem prover. Here
is how lemma subprograms can be defined for the two desired properties of Occ:

.. literalinclude:: gnatprove_by_example/examples/perm-lemma_subprograms.ads
   :language: ada

These two "axioms" can then be used to prove an implementation of the selection
sort algorithm. Lemma subprograms need to be explicitely called for every
natural. To achieve that, a loop is introduced. The inductive proof necessary
to demonstrate the universally quantified formula is then achieved thanks to
the loop invariant, playing the role of an induction hypothesis:

.. literalinclude:: gnatprove_by_example/examples/sort.adb
   :language: ada

.. literalinclude:: gnatprove_by_example/examples/sort.ads
   :language: ada

The procedure Selection_Sort can be verified using |GNATprove|, with the
alternative prover CVC4, in less than 1 minute per verification condition. 
Notice that, for now, normal
variables and procedures must be used for implementing ghost code, resuling in
warnings about assignments being useless and procedures having no effects.
Indeed, ghost variables and procedures are not yet part of the language.

To complete the verification of our selection sort, the only remaining issue
is the correctness of the two axioms for Occ. They can be discharged using the
definition of Occ. Since this definition is recursive, these proofs require
induction, which is not normally in the reach of an automated prover. For
|GNATprove| to verify them, they must be implemented using recursive calls on
themselves to assert the induction hypothesis. Note that the proofs of the
lemmas are then conditioned to the termination of the lemma functions, which
currently cannot be verified by |GNATprove|. 

.. literalinclude:: gnatprove_by_example/examples/perm-lemma_subprograms.adb
   :language: ada

|GNATprove| proves automatically all checks on the final program, with a small
timeout of 5s for the automatic prover.

