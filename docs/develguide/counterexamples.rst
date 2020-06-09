.. _counterexamples:

###############
Counterexamples
###############

The counterexamples are a clever way of displaying the model results of
SMT-solvers.
Roughly, how it works:

- During ``proof`` translation to Why3, annotations (attributes) are added to
  the generated code together with locations,
- Then, WP generation: the attributes are kept and still associated to
  appropriate variables
- Then, a specific transformation for counterexamples will introduce new
  constants for all constants appearing inside the verification condition. This
  constant location will be the one of the VC. This will allow to have more
  counterexamples on the VC line (because no variable is defined at an overflow
  check for example).
- Then, the printer will collect the variables that have a ``model_trace``
  attribute (added during first phase). So, the printer prints the variables to
  smt2 and Why3 records the correspondance with ``model_trace``
- Then cvc4/z3 executes and gives its output
- A parser written in OCaml/menhir/Ocamllex will parse the model given and do
  some substitutions to try to recover most of it.
- A correspondance is done again between the ``model_trace`` and the actual
  values that were given by the prover.
- This correspondance is amended with information from gnatcounterexamples.ml
  ??? TODO
- Everything is transformed into JSON together with the rest of the results
- Send to gnat2why
- Gnat2why parses the JSON input from counterexamples and do some computation
  to display it.

Perhaps the easier way to explain this is to proceed with layers.

Provers layer
=============

From Why3, the smt solvers are called by transforming the task into an smt2
file by replacement of syntax and change the goal into its negation. That way,
if the prover is sure that the property is unsatisfiable then we are sure that
indeed the task is valid (meaning it was proved).
So, when provers are able to satisfy the task, they answer sat. In this case,
they found a model for the task (i.e. an instantiation of all constants that is
consistent with the task and does not negate the goal). In this case, we can
ask them for this task using:

.. TODO ??? Add smt2 language in pygments using the .el file availables online
.. code-block:: Ada

    (get-model)

After a sat/unknown answer from a ``(check-sat)`` command, when given a
``(get-model)`` command, the prover produce an assignment for every variable (a
model).
The way things are expressed in smt2 is defined in http://smtlib.cs.uiowa.edu/ .
This looks like the following example (S-expr style and prefix operators).
From task:

.. code-block:: Ada

    (declare-const a Int)

    (declare-const b Int)

    (assert (= b 2))

    (assert (= a (- 2 )))

    (assert
      (in_range (* a b)))
    (check-sat)
    (get-model)

yields the following model:

.. code-block:: Ada

     sat
     (model
     (define-fun a () Int (- 2))
     (define-fun b () Int 2)
     )


Parser for counterexamples
==========================


The first difficulty is to be able to parse the counterexample model
given. The parser/lexer are files
:download:`parse_smtv2_model_parser.mly <../../why3/src/driver/parse_smtv2_model_parser.mly>`
and
:download:`parse_smtv2_model_lexer.mll <../../why3/src/driver/parse_smtv2_model_lexer.mll>` .

The first file contains the parser and the second one contains the
lexer. Reading it should not be very difficult to the grammarly-trained eye. It
uses the same syntax as the parser of Why3.

The returned datatype is what we called a ``correspondence_table``
(from :download:`smt2_model_defs.mli
<../../why3/src/driver/smt2_model_defs.mli>`). As the comment advise, it is a
hashtable between names (string) and an associated definitions (types term
which can be an Integer, a Float, an Array etc). The associated definition can
itself contain constant (that are usually given in the model: Variable,
Cvc4_Variable ...).

This is the definition of correspondence_table:

.. code-block:: Ocaml

  type correspondence_table = (bool * definition) Mstr.t

A ``definition`` can be either a function with argument, a term or an error (no
element).

.. code-block:: Ocaml

  type definition =
  | Function of (variable * string option) list * term
  | Term of term
  | Noelement

A term (depending on its value in the model) is the following:
Integer, Float, Apply (application of an element to a list of term), an
Array (which contains other terms) etc. There are also specific cases for
variables: Cvc4_Variable is anything known to be an internal prover variable
like name containing a ``!`` (which is Z3 internal variable). A
``Function_Local_Variable`` can occur in the case of functions: it is one of
the parameter of the function.

??? TODO this recently changed to include simple values

.. code-block:: Ocaml

  type array =
  | Array_var of variable
  | Const of term
  | Store of array * term * term

  and term =
  | Integer of string
  | Decimal of (string * string)
  | Fraction of (string * string)
  | Float of Model_parser.float_type
  | Apply of (string * term list)
  | Other of string
  | Array of array
  | Bitvector of string
  | Boolean of bool
  | Cvc4_Variable of variable
  | Function_Local_Variable of variable
  | Variable of variable
  | Ite of term * term * term * term
  | Record of string * ((string * term) list)
  | To_array of term

  type variable = string

Convert parsed values to usable values
======================================

As you may have noticed, variables remain in the output counterexample we
have, and there are some treatment needed to get correct counterexample
model. The conversion between the original output of the parser and a list of
``model_element`` as defined in
:download:`model_parser.mli <../../why3/src/core/model_parser.mli>`
is done by function ``create_list`` from
:download:`collect_data_model.mli <../../why3/src/driver/collect_data_model.mli>`

This is done by successive refinements.
Note that additional arguments to this function ``create_list`` are the list of
projections (collected during transformations) and the list of records
correspondance (these just convert Apply to Record when the record had only one
constructor and started with "mk " which is the official
Why3 way of recognizing a record). Note that those two arguments are collected
during printing
:download:`smtv2.ml <../../why3/src/printer/smtv2.ml>`

into a variable of type ``Printer.printer_mapping`` (see :ref:`printing_cex`) .
This function is called in
:download:`parse_smtv2_model.ml <../../why3/src/driver/parse_smtv2_model.ml>`.
Note also that the parser is something that is registered. This means that it
is defined using ``register_model_parser`` and called using
``lookup_model_parser``.

Back to the ``create_list`` function. The first step is:

.. code-block:: Ocaml

  let list_records =
    Mstr.fold (fun key l acc ->
      Mstr.add key (List.map (fun (a, b) -> if b = "" then a else b) l) acc) list_records Mstr.empty
  in

These are a map from ``type_name`` to a list of couple
``(field_name, trace_name)`` which are collected when
printing the definition of the constructors of a type. For each constructor, we
record the field_name and the model_trace associated which is the trace_name
(in Why3 there is none).
This first function convert this list of couples to list of singles
by removing the one that is useless (in our case the ``field_name`` because all
constructors should have a ``model_trace``).

Then, we begin the refinement of the ``correspondence_table``. The first step
is to convert the elements that were parsed as applications into records using
``list_records``:

.. code-block:: Ocaml

  let table =
    Mstr.fold (fun key (b, value) acc ->
      let value = definition_apply_to_record list_records value in
      Mstr.add key (b, value) acc) table Mstr.empty
  in

As seen in function ``apply_to_record`` on called for ``Apply``, the objective
is to get a record type with every value corresponding to the right field.

.. code-block:: Ocaml

   | Apply (s, l) ->
        let l = List.map apply_to_record l in
        if Mstr.mem s list_records then
          Record (s, List.combine (Mstr.find s list_records) l)
        else
          Apply (s, l)

Actually, the function we use for SPARK is not ``default_apply_to_record``
because for some datatypes we need to do some additional treatment. So we
register another function through ``register_apply_to_records``. This function
called ``apply_to_record`` is defined and registered in
:download:`gnat_counterexamples.ml <../../why3/src/gnat/gnat_counterexamples.ml>`.

.. warning:: This is actually needed to register this function and not just
             define it so that we can use the same code in both Why3 and SPARK.

In this function, much more specific case are handled depending of the way
things are translated to Why3:

For unconstrained arrays which are "wrongly" translated to records:

.. code-block:: Ocaml

          | [x; y] when Strings.has_prefix "elts" x &&
                        Strings.has_prefix "rt" y ->
            (* This recognize records corresponding to unconstrained array. We
               only want the first part of the record (the array). *)
            List.hd l

For already defined "__content" stuff:

.. code-block:: Ocaml

          | [x] when Strings.has_prefix "map__content" x ->
            (* Corresponds to map *)
              List.hd l
          | [x] when Strings.has_prefix "t__content" x ->
            (* Corresponds to bv *)
              List.hd l
          | [x] when Strings.ends_with x "__content" ->
            (* Records for int__content, bool__content, real__content or
               anything content: we are only interested in the value (not in
               the record). *)
            List.hd l

For "split_fields" and "split_discrs" some hack is also necessary to properly
report values field by field with the correct field.

.. code-block:: Ocaml

          | _ ->
            (* For __split_fields and __split__discrs, we need to rebuild the
               whole term. Also, these can apparently appear anywhere in the
               record so we need to scan the whole record. *)
            let new_st =
                List.fold_left2 (fun acc s e ->
                  if Strings.has_prefix "us_split_fields" s ||
                     Strings.has_prefix "us_split_discrs" s
                  then
                    (match e with
                    | Record (_, a) -> acc @ a
                    | _ -> (s,e) :: acc)
                  else
                    if s = "attr__constrained" then
                      acc
                    else
                      (s, e) :: acc)
                  [] fields l
              in
              Record (s, new_st)

The second step is to collect all internal variables present in terms and add
them to the table at ``Term`` level.

.. code-block:: Ocaml

   let table = get_all_var table in


Now, we can use the functions returned for projections we defined in order to
get the value corresponding to internal variables of the provers.

.. code-block:: Ocaml

  let table =
    Mstr.fold (fun key value acc ->
      if Sstr.mem key projections_list then
        add_vars_to_table acc value
      else
        acc)
      table table in

This is done by inspecting the body of the function defined which is always of
the form:

.. code-block:: Ocaml

      fun x -> if x = intern_var_1 then 5 else if x = intern_var_2 then 42 else...

In this kind of function we associate ``intern_var_1`` to the value 5, ``intern_var_2``
to the value 42 etc...
Note that values here (42, 5) can very well be internal variables too.

The third step is to propagate the values of variables in terms:

.. code-block:: Ocaml

  let table =
    Mstr.fold (fun key v acc -> refine_variable_value acc key v) table table in

We use the booleans defined in ``table`` in order to mark variables that are
completely defined.

At the end, we convert all ``correct`` variables into
``raw_model_element``:

.. code-block:: Ocaml

  Mstr.fold
    (fun key value list_acc ->
      let t = match value with
      | (_, Term t) ->
          Some t
      | (_, Function ([], t)) ->
          Some t
      | _ -> None in
      try (convert_to_model_element key t :: list_acc)
      with Not_value when not (Debug.test_flag Debug.stack_trace) -> list_acc
      | e -> raise e)
    table
    []



Model_elements in Why3
======================

Model_elements in Why3 are defined in
:download:`model_parser.mli <../../why3/src/core/model_parser.mli>`.

First are defined the types model values:

.. code-block:: Ocaml

  type float_type =
  | Plus_infinity
  | Minus_infinity
  | Plus_zero
  | Minus_zero
  | Not_a_number
  | Float_value of string * string * string
  | Float_hexa of string * float

 type model_value =
 | Integer of string
 | Decimal of (string * string)
 | Fraction of (string * string)
 | Float of float_type
 | Boolean of bool
 | Array of model_array
 | Record of model_record
 | Bitvector of string
 | Apply of string * model_value list
 | Unparsed of string
 and  arr_index = {
  arr_index_key : string;
  arr_index_value : model_value;
 }
 and model_array = {
  arr_others  : model_value;
  arr_indices : arr_index list;
 }
 and model_record = (field_name * model_value) list
 and field_name = string

the element kind:

.. code-block:: Ocaml

  type model_element_kind =
  | Result
  | Old
  | Error_message
  | Other

the element name:

.. code-block:: Ocaml

  type model_element_name = {
    men_name   : string;
    men_kind   : model_element_kind;
    men_labels : Ident.Slab.t;
  }

and finally the ``model_element`` that are sent as JSON elements:

.. code-block:: Ocaml

  type model_element = {
    me_name     : model_element_name;
    me_value    : model_value;
    me_location : Loc.position option;
    me_term     : Term.term option;
  }

The conversion to JSON is also located in
:download:`model_parser.mli <../../why3/src/core/model_parser.mli>`.


WP/SP with counterexamples
==========================

??? TODO to be completed

Specific cases are done everywhere in WP for counterexample handling: so that
the new variables have correct model_trace, correct locations etc.

.. warning:: This includes the transformations that are silently applied after
             WP (eval_match etc).


Transformations of counterexamples
==================================

The main transformation used is called
:download:`prepare_for_counterexmp <../../why3/src/transform/prepare_for_counterexmp.ml>`: it is the
composition of
:download:`intro_vc_vars_counterexmp <../../why3/src/transform/intro_vc_vars_counterexmp.ml>`
and
:download:`intro_proj_counterexmp <../../why3/src/transform/intro_projections_counterexmp.ml>`.
We will most precisely describe the former here as the latter is mostly
deprecated and only used to generate constants corresponding to attribute
``First`` and ``Last`` (to my knowledge).

:download:`intro_vc_vars_counterexmp <../../why3/src/transform/intro_vc_vars_counterexmp.ml>`
is a transformation whose objective is to find constants that are inside the
``model_vc`` attributes (meaning inside the current check) and to duplicate
them with new constants that are defined at the location of the VC. In
practice, those new constants will hold the values of the counterexample on the
VC line.

For example, on the following VC (simplified):

.. code-block:: whyml

  constant x "model_trace:2342.int__content@assign" : int

  axiom H : x = 0

  goal WP_parameter def:
    "model_vc" "GP_Sloc:bar.adb:5:25" "GP_Reason:VC_ASSERT"
    "GP_Id:1"
    of_int x = True

The transformation will detect "model_vc" attribute then detect ``x`` inside
it. ``x`` is obviously not defined at the location of the VC so it will create
a new constant equal to ``x`` that is defined at location of the VC. That way,
we will get a counterexample for ``x`` at the location of the VC.

.. code-block:: whyml

  constant x "model_trace:2342.int__content@assign" : int

  axiom H : x = 0

  constant x_vc_constant "model_trace:2342.int__content@assign" : int

  axiom x_vc_axiom : x_vc_constant = x

  goal WP_parameter def:
  "model_vc" "GP_Sloc:bar.adb:5:25" "GP_Reason:VC_ASSERT"
  "GP_Id:1"
  of_int x = True


The part of the transformation handling this is contained in function called
``do_intro``.
Note that this transformation also introduce premises, and it tags some of the
quantified variables with a model so that their value can be printed (for
example when writing ``for all v`` in a contract).

.. _printing_cex:

Printing for counterexamples
============================

??? TODO details

During printing, the constants that will be used for the model are collected.
The projections are also collected together with known fields of records.
These are put into the printer_mapping.



Gnat2why translation to Why3 for counterexamples
================================================

This is quite simple. You just need to add a "model_trace:<entity_id>" for all
variables during the generation of the code. For definition of records, you
need to add a "model_trace:.<entity_id_of_current_field>". This should be
enough to get counterexamples working. All of this should be done in function
Get_Model_Trace_Label from
:download:`gnat2why-util.adb <../../src/why/gnat2why-util.ads>`.

.. warning:: Note that theories and external axiomatization should also contain
             model_trace attributes. Otherwise, the stuff relying on those will
             not have counterexamples.


Gnat2why: From Why3 counterex to Ada counterex
==============================================

The counterexamples are translated by Why3 to a JSON format which is part of
the JSON associated to each of the check in SPARK.


Translation from JSON
---------------------

This is done by functions From_JSON of the file
:download:`vc_kinds.ads <../../src/common/vc_kinds.ads>`. It translates the
counterexamples values to type ``Cntexample_File_Maps``:

.. code-block:: Ada

   package Cntexample_File_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps (Key_Type     => String,
                                             Element_Type => Cntexample_Lines,
                                             "<"          => "<",
                                             "="          => "=");

   Cntexample_File_Maps.Map


Note that the counterexamples themselves are typed:

.. code-block:: Ada

   type Cntexmp_Value (T : Cntexmp_Type := Cnt_Invalid) is record
      case T is
         when Cnt_Integer   => I  : Unbounded_String;
         when Cnt_Decimal   => D  : Unbounded_String;
         when Cnt_Float     => F  : Float_Value_Ptr;
         when Cnt_Boolean   => Bo : Boolean;
         when Cnt_Bitvector => B  : Unbounded_String;
         when Cnt_Unparsed  => U  : Unbounded_String;
         when Cnt_Record    =>
            Fi                    : Cntexmp_Value_Array.Map;
         when Cnt_Array     =>
            Array_Indices         : Cntexmp_Value_Array.Map;
            Array_Others          : Cntexmp_Value_Ptr;
         when Cnt_Invalid   => S  : Unbounded_String;
      end case;
   end record;


.. warning:: Thou shall not use integer type for counterexamples of type int
             because these prover-generated constants can overflow. Index can
             overflow too. Everything can overflow.


When trying to print the value for a counterexample we check that the
associated Entity_id has a compatible type. If the type is complex and the
counterexample was of records/arrays/arrays of records of arrays/etc, the code
tries to print the correct structure in ``Refine_*`` functions. These are
defined in :download:`gnat2why-counter_examples.ads <../../src/counterexamples/gnat2why-counter_examples.ads>`


If the counterexample type is not a record/array/etc but still the entity is
supposed to be a record, we try to remake a properly structured counterexample
in Get_CNT_Element_Value (from the else part of the if "Refined_Value is the
empty string") in :download:`gnat2why-counter_examples.adb <../../src/counterexamples/gnat2why-counter_examples.adb>`


If-branching special case
-------------------------

This feature is a recent improvement to counterexamples. The concept is to
avoid printing counterexamples values in either the "then" or the "else" branch
of an "if" (also done for case statement) (this is not done for if or case
expressions). This problem only occurs with the "fast_wp" which GNATprove uses:

.. code-block:: Ada

   function Test_If (A : Integer) return Integer
     with Post => Test_If'Result = 42
   is
      B : Integer;
   begin
      if A > 3 then
         B := 5;
      else
         B := 82;
      end if;
      return B;
   end Test_If;

Due to transformation of fast_wp which does not split the if-condition (it is
more complex, I think the variables are shared between the two branch ??? for
fast_wp, please read Flanagan and Saxe for more information), we
previously obtained counterexamples like this:


.. code-block:: Ada

   function Test_If (A : Integer) return Integer
     with Post => Test_If'Result = 42
     --  A = 4, B = 5
   is
      B : Integer;
   begin
      if A > 3 then
         B := 5;
         -- B = 5
      else
         B := 82;
         -- B = 5
      end if;
      return B;
   end Test_If;


The problem here is with the added counterexample for B in the "else" branch.

To avoid this counterexample in the "else" branch, the solution implemented is
to try to get a Boolean counterexample for the condition (here ``A > 3``) and
remove the branches that are not part of the counterexample.
To achieve that, we added a new variable called ``spark__branch`` in
:download:`_gnatprove_standard <../../share/spark/theories/_gnatprove_standard.mlw>`
of type ``bool__ref`` with a dummy "model_trace:0000" (but the model_trace is
needed to get the counterexample).

.. code-block:: whyml
   val spark__branch "model_trace:0000": bool__ref

The idea is now to replace every translated if statement to an assignment to
``spark__branch`` and then an if statement on the new value of spark__branch.
The function handling this new assignment of ``spark__branch`` is called
New_Counterexample_Assign which is defined in
:download:`why-gen-expr.adb <../../src/why/why-gen-expr.adb>`. This
function adds a specific attribute called "branch_id:<entity_id_of_if>" which
is used when getting the counterexample to know which if-entity the value
corresponds to.
In whyml, the translation done by adding New_Counterexample_Assign is:

.. code-block:: whyml

   if c then A ...

to

.. code-block:: whyml

   if (("branch_id:E" spark_branch).bool_content <- c; c) then A ...

So, we are sure that the counterexample given at that line is indeed the value
(in the model) of the if. The function New_Counterexample_Assign is used both
for ``if`` and ``case``
(:download:`gnat2why-expr.adb <../../src/why/gnat2why-expr.adb>` in
``Case_Expr_Of_Ada_Node`` and ``Transform_Statement_Or_Declaration``)
as ``case`` are translated to successions of ``if``.
Note that we don't need more than one variable like ``spark__branch`` because
the information of the current if is inside the locations and attributes
associated to the counterexample.


During the parsing of the counterexamples in gnat2why, we remove part of the
counterexamples. In
:download:`gnat2why-counter_examples.adb <../../src/counterexamples/gnat2why-counter_examples.adb>`
, function ``Remove_Irrelevant_Branches`` is used for this. It proceeds in two
steps:
First, it searches for the counterexamples for spark__branch:

.. code-block:: ada

         for Lines of Files.Other_Lines loop
            for Elt of Lines loop
               Search_Labels (Suppressed_Lines, Elt.Labels, Elt.Value);
            end loop;
         end loop;

It will populate a set of disjoint intervals (representing the removed lines
from counterexamples): it is defined in :download:`ce_interval_sets.ads <../../src/counterexamples/ce_interval_sets.ads>`.

The second part of this function will go through the counterexample removing
all counterexamples that are not relevant (by searching into the set
structure). A number of annex functions are used to get the appropriate range
of ``then`` and ``else`` branches.

.. warning:: When succeeding if are used, a number of if values cannot be
             trusted because they are part of the ``noise`` that should be
             removed. It is very possible that a value say to take a then
             branch which is inside an inaccessible branch. The current code
             handles correctly these potentially bad values.
