.. _External Axiomatizations:

External Axiomatizations
========================

What is it?
----------------
It is a feature of the |SPARK| toolset that allows to manually supply a WhyMl
translation for the public specification of a library level package that is in
|SPARK|. This feature is still experimental.

Why is it useful?
-------------------------
- For features that cannot easily be described using contracts, like
  transitivity, counting, or summation
- To link functions to the logic world, like trigonometry functions
- To improve provability of client code, like for containers

How does it work?
----------------------------------
- To say that a library package has an external axiomatization, we annotate it
  using::

    pragma Annotate (GNATprove, External_Axiomatization);

- These packages should have SPARK_Mode On on their public specification and
  SPARK_Mode Off on their private part.
- The WhyMl translation for the package should be stored in a subdirectory
  named _theories of the proof directory specified for the project.

What should the translation look like?
-------------------------------------------------------------
- For each publicly visible entity E in the package P, it should provide the
  same elements (types as well as logic and program functions) as the automatic
  translation, all grouped in one single module named P__e. For example, the
  module for a function F should provide both a logic function declaration named
  f__logic and a program function declaration named f.
- For most types, a model module in defined in ada__model.mlw that can be cloned
  to get most of the required declarations.
- The manual translation may use any type, constant and function that is visible
  from the Ada package declaration.
- A good way to start an axiomatization file on a package is to launch the
  toolset on it and copy paste the modules created for each entity of the
  package. A WhyMl file created by the tool on a package P contains a module for
  every declaration visible from it, only declarations from P itself should be
  copied. The generated file usually contains two modules for each entity, one
  named P__e and one named P__e__axiom. Both should be put together in P__e for
  the manual translation. The toolset will replace statically known expressions
  with their value. Beware that they might be architecture dependent.

Example of standard package
---------------------------
For example, let us consider the following package, stored in a file sum.ads,
providing a summation function for slices of arrays of integers:

.. literalinclude:: /gnatprove_by_example/examples/sums.ads
   :language: ada
   :linenos:

We can provide the following Why3 translation for it, that we should store in a
file named sum.mlw:

.. literalinclude:: /gnatprove_by_example/examples/proof/_theories/sums.mlw
   :language: none

And for generic packages?
--------------------------
- External axiomatizations can also be used for a generic package P, with the
  restriction that P will then have to be instantiated at library level only.
- A generic package with external axiomatization can have type and function
  parameters, but they must be instantiated with pure functions only (that do
  not read global variables).
- If the package as a private type parameter that it used as in out or out
  parameter of a procedure, than this type cannot be instantiated with an array
  type whose bounds are not statically known.
- For now, when a package is instantiated with a function whose argument
  types or return type do not statically match the argument types or the return
  type of the parameter, it is the user responsibility to ensure that there can
  be no error during the conversions.
- The WhyMl translation for a generic package P can refer to its generic
  parameters as being translated in p__args.mlw. This file doesn't need
  to be provided.
- For practical reasons, the name of every module declared in p.mlw
  must be prefixed by P and modules of parameters can neither be
  imported nor exported.

Example of generic package
-----------------------------------------------
As an example, let us consider the formal doubly linked list package.
It has two generic parameters, the type of the elements that will be stored
in the list and the equality function that should be used over them:

.. code-block:: ada

  generic
     type Element_Type is private;

     with function "=" (Left, Right : Element_Type)
                        return Boolean is <>;

  package Ada.Containers.Formal_Doubly_Linked_Lists is
     pragma Annotate (GNATprove, External_Axiomatization);

The WhyMl translation for this package can refer to these parameters as
beging translated in the file
ada__containers__formal_doubly_linked_lists__args.mlw in the
following way::

  module Ada__containers__formal_doubly_linked_lists__element_type
      type base_type
      type element_type

      (* Translations of subprograms taking element_type as an argument will
         have an argument of type base_type.
         We therefore rely on the presence of conversion functions for it. *)
      function to_base element_type : base_type
      function of_base base_type : element_type
      predicate valid base_type
  end

  module Ada__containers__formal_doubly_linked_lists__oeq
    use Ada__containers__formal_doubly_linked_lists__element_type

    (* The name of operators is prefixed with o. Expects arguments of
       element_type's base_type. *)
    function oeq
           Ada__containers__formal_doubly_linked_lists__element_type.base_type
           Ada__containers__formal_doubly_linked_lists__element_type.base_type :
                     bool
  end

The  formal doubly linked list package for example provides on equality
function over lists:

.. code-block:: ada

   function "=" (Left, Right : List) return Boolean with
     Global => null;

Here is the module that we provide for it in
ada__containers__formal_doubly_linked_lists.mlw::

  (* The name of operators is prefixed with o. When a subprogram is overloaded,
     it must be desanbiguated using an integer. To get the expected name for
     an entity, the best way is to look at the automated translation. *)
  module Ada__containers__formal_doubly_linked_lists__oeq__2
    use import int.Int
    (* Do not import or export modules for a generic parameter. *)
    use  "ada__containers__formal_doubly_linked_lists__args".
           Ada__containers__formal_doubly_linked_lists__element_type
    use "ada__containers__formal_doubly_linked_lists__args".
           Ada__containers__formal_doubly_linked_lists__oeq
    use import Ada__containers__formal_doubly_linked_lists__list
    use import Ada__containers__formal_doubly_linked_lists__length
    use import Ada__containers__formal_doubly_linked_lists__cursor
    use import Ada__containers__formal_doubly_linked_lists__element

    function oeq__2__logic list list : bool

    (* Two lists that are equal have the same length... *)
    axiom oeq__2_length_:
     forall co1 co2 : list.
         oeq__2__logic co1 co2 = True -> length_ co1 = length_ co2

    (* ...and contain the same elements at the same position. *)
    axiom oeq__2_element:
     forall co1 co2 : list. oeq__2__logic co1 co2 = True ->
       forall cu1 : cursor [element co1 cu1]. position co1 cu1 > 0 ->
           Ada__containers__formal_doubly_linked_lists__oeq.oeq
            (Ada__containers__formal_doubly_linked_lists__element_type.to_base
              (element co2 (position_inv co2 (position co1 cu1))))
            (Ada__containers__formal_doubly_linked_lists__element_type.to_base
              (element co1 cu1)) = True

    (* Two lists that are not equal either do not have the same length or
       are different at some position. *)
    axiom oeq__2_inv:
     forall co1 co2 : list. oeq__2__logic co1 co2 <> True ->
     (length_ co1 <> length_ co2 \/
     exists i : int. 0 < i <= length_ co1 /\
      Ada__containers__formal_doubly_linked_lists__oeq.oeq
       (Ada__containers__formal_doubly_linked_lists__element_type.to_base
         (element co1 (position_inv co1 i)))
       (Ada__containers__formal_doubly_linked_lists__element_type.to_base
         (element co2 (position_inv co2 i))) = False)

    (* Symmetry axiom *)
    axiom oeq__2_sym :
     forall e1 e2 : list.
	  oeq__2__logic e1 e2 = True -> oeq__2__logic e2 e1 = True

    (* Transitivity axiom *)
    axiom oeq__2_trans :
     forall e1 e2 e3 : list.
	  oeq__2__logic e1 e2 = True -> oeq__2__logic e2 e3 = True ->
                oeq__2__logic e1 e3 = True

    val oeq__2 (co1:list) (co2:list) : bool
       ensures  { result  = oeq__2__logic co1 co2 }
  end
