########
GNATWhy3
########

This section provides a quick description of GNATWhy3. GNATWhy3 is an
executable written in OCaml as an overcoat layer for Why3 (reusing part of its
API and most of the code). The submodule of spark2014 git repository called
Why3 follows the changes of Why3 branch master asynchronously (we usually
merge when a useful feature is available or a soundness issue appears).

GNATWhy3 Debug
==============

Useful debug flags
------------------

When gnatwhy3 fails, it can be useful to give it the option
``--debug-stack-trace`` in order to make it give the failing line and the
backtrace:
``gnatwhy3 <original_options> --debug-stack-trace <my_mlw_file>``

Debugging from GNATprove
------------------------

A way of passing debugging flags from GNATprove to gnatwhy3 was added:
``--why3-debug=my_why3_flag``

The behavior is to add the debug flag inside the commandline of gnatwhy3 using
gnatwhy3's option ``--debug-why3``. The possible flags are actually those of
Why3, you can query the exhaustive list using a Why3 executable such as
``why3ide --list-debug-flag``.

The error message will be packed inside the standard GNATprove debug
information.

For example, to get the stacktrace from gnatprove in a standard test, you can
do:
``gnatprove -P test.gpr --why3-debug=stack_trace``

Why3
====

Why3 is a platform for deductive program verification developped by researchers
from LRI and others (http://why3.lri.fr/). The tool used by GNATprove, GNATWhy3
is developped by Adacore/Altran and uses the Why3 API.

This first part will describe the source code of Why3: files/libraries that are
used. The objective is to provide a precise view of which part of the code does
what (it may be unclear at first sight).

Why3 behavior
-------------

Input:

- Source code .mlw (or .why which are deprecated) files, or other entry formats
  via the Ptree module (this is used by gnatwhy3)
- Session file why3session.xml (Why3 usually guess where it is: inside a \
  directory with the same basename as the .mlw).

Output:

- Updates to the session file why3session.xml

Why3 will parse and type its mlw file then generates the goals (WP generation)
and then allows the user to run provers (this will edit the session).

Why3 parsing
------------

The code for the parsing is done in files of the :file:`src/parser` directory.
This parser is using menhir as generator
(http://gallium.inria.fr/~fpottier/menhir/). The rules used in the source files
are quite common grammar definition and few knowledge of OCaml should be
necessary to edit them.
The main files are the :download:`lexer <../../why3/src/parser/lexer.mll>` and
the parser :download:`parser <../../why3/src/parser/parser.mly>`.
Menhir converts these files into automata written in OCaml (in files with the
same name but with extension .ml/.mli).
As common knowledge, the lexer transforms the text file into a list of tokens
which are then used in the grammar .mly file to define rules (look at
menhir reference manual).
The parser generates object of types defined in
:download:`ptree <../../why3/src/parser/ptree.ml>`. This represents an Abstract
Syntax Tree (AST) of the Why3 code which is then typed (relevant parts are
also in the :file:`src/parser` directory).

Why3 typing
-----------

??? TODO complete this section or not

Typing occurs in files typing.ml. Relevant files might include dterm.ml.


Weakest Precondition
--------------------

The next step is the Weakest Precondition (see Why3 documentation) / Strongest
Postcondition (for theorical concepts, see `Avoiding Exponential Explosion:
Generating Compact Verification Conditions` by Flanagan and Saxe) generation.
For SPARK, the generation used is SP (also called fast_wp in the source) and is
located in directory :file:`why3/src/whyml`.
The result of the WP generation is a list of goals to be proved which are
organized in a tree called the session.

The modules defining tasks (and its components), transformations etc are
located in the directory :file:`why3/src/core`. This is very useful when
writing transformations or trying to understand the logic used for tasks.

Core
----

The core directory (especially the .mli) is the most helpful source of
information for anyone willing to write transformations. This regroups files
that defines tasks, formulas and primitives to modify those. At this point,
everything is formula/term, the programs does not exist anymore.

Task
^^^^

A task (:download:`task.mli <../../why3/src/core/task.mli>`) is an ordered list
of declarations:

.. code-block:: Ocaml

     type task = task_hd option

     and task_hd = private {
        task_decl  : tdecl;        (** last declaration *)
        task_prev  : task;         (** context *)
        task_known : known_map;    (** known identifiers *)
        task_clone : clone_map;    (** cloning history *)
        task_meta  : meta_map;     (** meta properties *)
        task_tag   : Weakhtbl.tag; (** unique magical tag *)
     }

The task is an option to a record (chained list) defined as a task_hd on which
the user can access the current declarations ``task_decl``
(see :download:`decl.mli <../../why3/src/core/decl.mli>`),
the rest of the list ``task_prev``, the known identifiers (all identifiers
defined in the task(see :download:`ident.mli <../../why3/src/core/ident.mli>`),
the cloned theories of the task, meta and a unique tag.

It is rarely necessary to access the informations stored in ``task_known``,
``task_clone``, ``task_meta`` and ``task_tag``. If necessary, they can be
accessed using the function defined in
:download:`task.mli <../../why3/src/core/task.mli>`.
As a supporting example of this assertion, transformations are mostly written
by browsing the declarations in their definition order and changing each
declaration one by one.
The :download:`task.mli <../../why3/src/core/task.mli>` is rarely used to create
(recent) transformations. :download:`trans.mli <../../why3/src/core/trans.mli>`
should be preferred because it uses memoization (??? TODO check that Task does
not). Example justifying usefulness of memoization: A lot of transformations
are just editing the goal and leaving the rest of the context unchanged. When
the context is memoized, there is a global speedup.
:download:`trans.mli <../../why3/src/core/trans.mli>` has a monadic definition
(which can be quite difficult to handle at first). The primitives that are
given by this module are quite classic in the monadic style (bind/...) and the
rest are "duplicate" of :download:`task.mli <../../why3/src/core/task.mli>`
functions.
We will first describe (some) primitives contained in
:download:`task.mli <../../why3/src/core/task.mli>` and then go to
:download:`trans.mli <../../why3/src/core/trans.mli>`. These primitives should
allow you to write transformations with very few knowledge of the underlying
components:

.. code-block:: Ocaml

     val add_decl : task -> decl -> task
     val add_tdecl : task -> tdecl -> task

     val add_ty_decl : task -> tysymbol -> task
     val add_data_decl : task -> data_decl list -> task
     val add_param_decl : task -> lsymbol -> task
     val add_logic_decl : task -> logic_decl list -> task
     val add_ind_decl : task -> ind_sign -> ind_decl list -> task
     val add_prop_decl : task -> prop_kind -> prsymbol -> term -> task


We will assume understanding of this and we will get back to the definition of
``decl`` and ``tdecl`` later :ref:`gnatwhy3_decl`. ``add_decl`` simply adds a
declaration to the task at hand to generate a new task.

From there, primitives to browse the whole task are provided:

.. code-block:: Ocaml

     val task_fold : ('a -> tdecl -> 'a) -> 'a -> task -> 'a
     val task_iter : (tdecl -> unit) -> task -> unit

``task_fold`` and ``task_iter`` are the common operations which iterates on all
the declarations (in the right order) to produce a result or update a result.
Here is a small example that count the declarations of a task (it is of no
practical use):

.. code-block:: Ocaml

let count task =
  Task.task_fold (fun n decl -> n + 1) 0 task

.. warning:: some common mistakes in transformations:

- Forget about the goal special state during iteration
- Returning an ill-formed task: checks for that are dynamically done (the task
  has to end with a goal etc)
- Using high-level collections of elements like ``Trans.on_tagged_ls`` combined
  with ``Trans.decl`` and assume in the latter that the set of ls given in the
  former are all defined at the beginning (it is not the case).

Trans module
^^^^^^^^^^^^

??? TODO check this section

This is an high-level API for the task module. This implements operations on
transformations: ``task -> task``

.. code-block:: Ocaml

     type 'a trans (* = task -> 'a *)
     type 'a tlist = 'a list trans


The defintion of a transformation identity in this context use ``'a =
task``. The first type is for transformations that produce a single goal. The
second is for transformations that generates several goals (like ``split``) or
that can generate zero goals (like ``compute_in_goal``, in this case it means
the goal is proven).

Some "classical" monad transformations are provided so that you can
switch from ``decl`` code to ``trans`` code.

.. code-block:: Ocaml

     val store : (task -> 'a) -> 'a trans
     val apply : 'a trans -> (task -> 'a)

Some usual and composition functions are added such as ``bind`` which allows to
compose transformations:

.. code-block:: Ocaml

     val identity   : task trans
     val identity_l : task tlist

     val singleton : 'a trans -> 'a tlist
     val return    : 'a -> 'a trans
     val bind      : 'a trans -> ('a -> 'b trans) -> 'b trans
     val bind_comp : ('a * task) trans -> ('a -> 'b trans) -> 'b trans


There are also functions useful when iterating over a task such as:

.. code-block:: Ocaml

     val fold   : (task_hd -> 'a -> 'a     ) -> 'a -> 'a trans
     val decl  : (decl -> decl list     ) -> task -> task trans
     val decl_l : (decl -> decl list list) -> task -> task tlist
     val goal   : (prsymbol -> term -> decl list     ) -> task trans
     val rewrite : (term -> term) -> task -> task trans
     val on_meta : meta -> (meta_arg list list -> 'a trans) -> 'a trans
     val on_tagged_ls : meta -> (Sls.t -> 'a trans) -> 'a trans

The above are a few example of what can be found in
:download:`trans.mli <../../why3/src/core/trans.mli>`. ``fold`` gets its usual
definition. ``decl`` is an iteration over the declarations of the arguments
task. For each declarations, you chose which new declarations you want to add
in your new task. This can be useful, for example, to do a transformations that
split ``/\`` head constructors of declarations (you might want to read
:ref:`gnatwhy3_decl` to understand this code):

.. code-block:: Ocaml

     (* transformation not checked *)
     let transf : task trans (* = task -> task *) =
        Trans.decl (fun d ->
          match d.d_node with
          | Dprop (Paxiom, pr, t) ->
            begin match t.t_node with
            | Tbinop (Tand, t1, t2) ->
                (* The declaration is an axiom with head constructor being
                   t1 /\ t2. We create two declarations d1 (and d2) which
                   contains the logic t1 (respectively t2). *)
                 let d1 = simplified_create_decl (fresh name) t1 in
                 let d2 = simplified_create_decl (fresh name) t2 in
                 [d1; d2]
            | _ -> d
            )
            None (* Initial task with nothing inside it *)

The above builds a task from scratch reusing a task that is passed as
argument.


The function ``decl_l`` can be used to do a similar work except that it is more
powerful than ``decl`` in the sense that for each ``decl`` you return a list of
list declarations. The new level of list is used to create several new
goals. For example, you can use it to split on disjunctions: you want to create
two new goals on each encountered ``\/``:

.. code-block:: Ocaml

     (* transformation not checked *)
     let transf : task trans (* = task -> task *) =
        Trans.decl (fun d ->
          match d.d_node with
          | Dprop (Paxiom, pr, t) ->
            begin match t.t_node with
            | Tbinop (Tor, t1, t2) ->
                (* The declaration is an axiom with head constructor being
                   t1 \/ t2. We create two declarations d1 in the first task
                   and d2 in the second task. *)
                 let d1 = simplified_create_decl (fresh name) t1 in
                 let d2 = simplified_create_decl (fresh name) t2 in
                 [[d1]; [d2]]
            | _ -> d
            )
            None (* Initial task with nothing inside it *)


For example, applying this transformation on a task containing two disjunctions
in the context would produce 4 subgoals.
The transformations combinators ``goal`` and ``rewrite`` follow from their
name. The combinators beginning with ``on_tagged_*`` are providing a collection
of all specific constructs (ty returns all types defined in the task, ls
returns all lsymbols defined in the task etc).


The interface used inside :ref:`gnatwhy3_drivers` to apply transformations uses
the ``trans`` type so you either need to use
:download:`trans.mli <../../why3/src/core/trans.mli>` or use
:download:`task.mli <../../why3/src/core/task.mli>` and apply the
``Trans.store`` function on it.
For example:

.. code-block:: Ocaml

      let count : Task.task Trans.tran = Trans.store count

After that, you can register your transformation so that it is available in
drivers (or in manual proof):

.. code-block:: Ocaml

      val register_transform   : desc:Pp.formatted -> string -> task trans -> unit

      let () =
        Trans.register_transform "trans_name" count
          ~desc:"This is the description of my transformation"


Now, assuming that this code is executed, we are able to put this
transformation as "trans_name" inside both drivers and interactive proofs.


.. _gnatwhy3_decl:

Declarations
^^^^^^^^^^^^

Declarations are best described in the
:download:`decl.mli <../../why3/src/core/decl.mli>`: they are the main
constituent of the task (others exist see tdecl).

To pattern-match on ``decl``, use ``decl_node``:

.. code-block:: Ocaml

     and decl_node = private
     | Dtype  of tysymbol          (** abstract types and aliases *)
     | Ddata  of data_decl list    (** recursive algebraic types *)
     | Dparam of lsymbol           (** abstract functions and predicates *)
     | Dlogic of logic_decl list   (** defined functions and predicates (possibly recursively) *)
     | Dind   of ind_list          (** (co)inductive predicates *)
     | Dprop  of prop_decl         (** axiom / lemma / goal *)

To create new declarations, one can use the constructors provided:

.. code-block:: Ocaml

      val create_ty_decl : tysymbol -> decl
      val create_data_decl : data_decl list -> decl
      val create_param_decl : lsymbol -> decl
      val create_logic_decl : logic_decl list -> decl
      val create_ind_decl : ind_sign -> ind_decl list -> decl
      val create_prop_decl : prop_kind -> prsymbol -> term -> decl


Detailing the constituents of the declarations is probably beyond the scope of
this informal document (??? TODO document it anyway / also reformulate this
section).
As a note, you can remark that logic/ind/data constituent take a list of
arguments: this is for recursive or mutual definitions.


.. _gnatwhy3_drivers:

Drivers
-------

Drivers are text files (.drv) containing a set of statements which will call
transformations/printer/change elements of a task (they are all in
``why3/drivers`` or ``install/share/why3/drivers``). Drivers are tied
to a specific prover and they are typically called when a specific prover is
called. Drivers are mainly composed of:

- Amendements to the theories (for example, map the addition for a theory to the
  native addition of a prover),
- Imports of some specific other drivers parts,
- Applying transformations which will either simplify the task or remove the
  components that are not understood by the prover (``eliminate_algebraic``,
  ``eliminate_*``, etc)
- Call a specific printer used to output a specific formalism (for example,
  smtv2)
- A part containing how to parse the result message of the prover (example:
  "unsat" means "proved" etc) which is prover dependant

.. warning:: SPARK drivers are mainly shared with Why3 (except those containing
             gnatprove in their name, and some others). Any changes done to
             drivers should be pushed to Why3's corresponding drivers. Ideally,
             parts that cannot be pushed to Why3 should be in independant files
             and imported via the ``import`` primitive.
             Currently, too many differences exists: this makes merges and
             maintenance of drivers quite difficult.

To describe drivers, we will take the driver for cvc4 as example
:download:`cvc4 <../../why3/drivers/cvc4_16.drv>` : it is used to convert a
task into an .smt2 file understood by cvc4 (a different driver exists for z3
for example).

The prelude of the file: the prelude is printed at the top of the generated
file. In this case, it contains information about the logic that is being used
(there are several possible logic/theories in smt-lib cf
http://smtlib.cs.uiowa.edu/). It also gives information about the generation of
the VC (which is not essential).

.. code-block:: Ocaml

     (** Why3 driver for CVC4 >= 1.6 (with floating point support) *)

     prelude ";; produced by cvc4_16.drv ;;"
     prelude "(set-info :smt-lib-version 2.5)"
     prelude "(set-logic AUFBVFPDTNIRA)"
     (*
                A    : Array
                UF   : Uninterpreted Function
                BV   : BitVectors
                FP   : FloatingPoint
                DT   : Datatypes
                NIRA : NonLinear Integer+Real Arithmetic
      *)
      prelude "(set-info :source |VC generated by SPARK 2014|)"
      prelude "(set-info :category industrial)"
      prelude "(set-info :status unknown)"


The next part is a list of import:

.. code-block:: Ocaml

      import "smt-libv2.drv"
      import "smt-libv2-bv.gen"
      import "cvc4_bv.gen"
      import "smt-libv2-floats.gen"
      import "discrimination.gen"

We won't detail all of them. The first one imports a common driver used by
prover relying on smtv2 (in our case they are
Z3 at http://rise4fun.com/z3/tutorial and
CVC4 at http://cvc4.cs.stanford.edu/web/)

.. code-block:: Ocaml

       printer "smtv2"

This sets the printer used. In this case, this will use the printer that was
registered with name smtv2. For information, the code of all printers is inside
``why3/src/printer`` and this particular one is
:download:`smtv2.ml <../../why3/src/printer/smtv2.ml>`

It also sets how the name of files are generated (??? TODO I guess %f means the
name of the source file, %t is the name of the theory and %g the name of the
goal. The filename is then disambiguated to be unique):

.. code-block:: Ocaml

     filename "%f-%t-%g.smt2"

This next section gives some regular expressions that are used to recognize the
results output by the prover. Here, when the prover answers only ``sat`` on a
single line with nothing else on the line, it means that the result is invalid
(task is not proved):

.. code-block:: Ocaml

     invalid "^sat$"
     unknown "^\\(unknown\\|Fail\\)$" ""
     time "why3cpulimit time : %s s"
     valid "^unsat$"

The next section redefines a theory of the standard library originally defined
in :download:`int.mlw <../../why3/stdlib/int.mlw>`. In this case, the
theory for ``int`` is known by the prover so we map the elements of this theory
to the predefined operator (it is more efficient to rely on the prover
constructs than on Why3's):

.. code-block:: Ocaml

     theory int.Int

                prelude ";;; SMT-LIB2: integer arithmetic"

                syntax function zero "0"
                syntax function one  "1"

                syntax function (+)  "(+ %1 %2)"
                syntax function (-)  "(- %1 %2)"
                syntax function ( * )  "(* %1 %2)"
                syntax function (-_) "(- %1)"

                syntax predicate (<=) "(<= %1 %2)"
                syntax predicate (<)  "(< %1 %2)"
                syntax predicate (>=) "(>= %1 %2)"
                syntax predicate (>)  "(> %1 %2)"

                remove allprops
     end

``syntax function/predicate`` replace a function/predicate. ``remove`` is used
to remove hypothesis that the prover already knows. For example, cvc4 already
knows all about integer arithmetic: it does not need to know that (0,+)
is a group because cvc4 already knows this about its own logic.

Let's get back to :download:`cvc4_16.drv <../../why3/drivers/cvc4_16.drv>`
now. The next part is used to apply transformation before printing:

.. code-block:: Ocaml

     transformation "inline_trivial"
     transformation "eliminate_builtin"
     transformation "detect_polymorphism"
     transformation "eliminate_inductive"
     transformation "eliminate_algebraic_if_poly"
     transformation "eliminate_literal"
     transformation "eliminate_epsilon"

     transformation "simplify_formula"
     (*transformation "simplify_trivial_quantification"*)

     transformation "discriminate_if_poly"
     transformation "encoding_smt_if_poly"

     (* remove pointless quantifiers from the goal *)
     transformation "introduce_premises"

Transformations are applied in order.


The last part defined other possible output of the prover ``CVC4``:

.. code-block:: Ocaml

     (** Error messages specific to CVC4 *)

     outofmemory "(error \".*out of memory\")\\|Cannot allocate memory"
     timeout "interrupted by timeout"
     steps "smt::SmtEngine::resourceUnitsUsed, \\([0-9]+.?[0-9]*\\)" 1
     (**
     Unfortunately, there is no specific output message when CVC4 reaches its resource limit
     steplimitexceeded "??"
     *)


Sessions
--------

In this section, we will describe the mechanism of session that is used by
Why3. This is very well tight to the part on interactive proof as sessions are
the internal representation of the proof tree that one can see in manual proof
or in ``why3session.xml`` files.
Most of the files that describe sessions are located in ``why3/src/session``.
This part, by extension, will also describe most of the primitives used by
GNATWhy3 as the API is based on sessions and primitives given inside sessions.

The weakest precondition algorithm output a set of goals associated to
theories which is enough to build a session.
The session datatype is defined in :download:`session
<../../why3/src/session/session_itp.mli>` in a file named ``session_itp.ml``
(the ``itp`` inside the name is irrelevant). The precise internals of a session
is voluntarily hidden here.

.. code-block:: Ocaml

     type session
     type file
     type theory
     type proofNodeID
     type transID
     type proofAttemptID

The session is organized as a tree:

- A session is the root of the tree. Its children are of type files (nothing else).
- A file has to be in a session. Its children are of type theories (nothing else).
- A theory has to be in a file. Its children are of type proofNode also called
  goals (nothing else).
- A goal's parent is either a theory or a transformation. Its children are
  either transformations or proofattempts.
- A transformation's parent is a goal (and nothing else). Its children are a
  possibly empty list of goals.
- A proofAttempts' parent is a goal (and nothing else). It has no children.


Merging of session
^^^^^^^^^^^^^^^^^^

After WP is finished, the existing session is read and there is an effort done
to try to correlate the existing session with the one that has just been
generated: put the transformations/proofattempts under the right goals. This is
done using something called shapes which is a kind of clever summary of a
task. It also uses hash of theories (combined hash of the children tasks) to be
more efficient in matching that. SPARK (by choice) does not use
this mechanism which is mainly in the ``merge*`` function of
:download:`session <../../why3/src/session/session_itp.ml>`.
The flag ``session_pairing`` can be used to debug this.


Handling sessions
^^^^^^^^^^^^^^^^^

Several primitives are given to be able to interact and explore with the
session in :download:`session <../../why3/src/session/session_itp.mli>`.
From a user of API such as GNATWhy3, these functions should be used only to
move in/inspect the tree and access new nodes. An API user, is not supposed to
edit the tree using session function by herself (??? TODO to check that
everything needed can be done) : the controller has been made
to provide safe edition functions (launching prover, transformations, etc) to
use.
To access files or the directory where the session is located:

.. code-block:: Ocaml

                (* Get all the files in the session *)
                val get_files : session -> file Wstdlib.Hstr.t
                (* Get a single file in the session using its name *)
                val get_file: session -> string -> file
                (* Get directory containing the session *)
                val get_dir : session -> string

To access elements of a file node:

.. code-block:: Ocaml

                val file_name : file -> string
                val file_format : file -> string option
                val file_theories : file -> theory list

To access elements of a theory node:

.. code-block:: Ocaml

                val theory_name : theory -> Ident.ident
                val theory_goals : theory -> proofNodeID list
                val theory_parent : session -> theory -> file

To access a task/elements associated to a proof node:

.. code-block:: Ocaml

                val get_task : session -> proofNodeID -> Task.task
                val get_proof_name : session -> proofNodeID -> Ident.ident
                val get_proof_expl : session -> proofNodeID -> string

To access children/parent of a proof node:

.. code-block:: Ocaml

                val get_transformations : session -> proofNodeID -> transID list
                val get_proof_attempt_ids :
                   session -> proofNodeID -> proofAttemptID Whyconf.Hprover.t
                val get_proof_parent : session -> proofNodeID -> proof_parent


To access elements or children/parent of a transformation:

.. code-block:: Ocaml

                val get_sub_tasks : session -> transID -> proofNodeID list
                val get_trans_parent : session -> transID -> proofNodeID
                val get_transf_args : session -> transID -> string list
                val get_transf_name : session -> transID -> string

To access the definition of a ``proof_attempt``:

.. code-block:: Ocaml

                val get_proof_attempt_node : session -> proofAttemptID -> proof_attempt_node
                val get_proof_attempt_parent : session -> proofAttemptID -> proofNodeID


It can also be convenient to use the following type

.. code-block:: Ocaml

                type any =
                | AFile of file
                | ATh of theory
                | ATn of transID
                | APn of proofNodeID
                | APa of proofAttemptID

The session also holds the proved status of a node:

.. code-block:: Ocaml

                val th_proved : session -> theory -> bool
                val pn_proved : session -> proofNodeID -> bool
                val tn_proved : session -> transID -> bool
                val file_proved : session -> file -> bool
                val any_proved : session -> any -> bool

Controller
^^^^^^^^^^

The :download:`controller <../../why3/src/session/controller_itp.mli>` is the
high-level package that is supposed to be used for calling
transformations/provers.

``controller`` is the main data structure for the users of the API. It contains
both the configuration and the session (also usable provers, strategies and
running provers). Functions are also defined on this to update its session at a
high-level.

.. code-block:: Ocaml

                type controller = private
                { mutable controller_session : Session_itp.session;
                  mutable controller_config : Whyconf.config;
                  mutable controller_env : Env.env;
                  controller_provers : (Whyconf.config_prover * Driver.driver) Whyconf.Hprover.t;
                  controller_strategies : (string * string * string * Strategy.instruction array) Wstdlib.Hstr.t;
                  controller_running_proof_attempts : unit Hpan.t;
                }


At initialization, configuration is done then the session is loaded and these
parameters can be given to ``create_controller``. It is initialized with the
given session and configuration.

.. code-block:: Ocaml

                val create_controller: Whyconf.config -> Env.env -> Session_itp.session -> controller
                (** creates a controller for the given session.
                    The config and env is used to load the drivers for the provers. *)

An example of use can be found in ``init_cont`` from the code of GNATWhy3 in
:download:`gnat_objectives <../../why3/src/gnat/gnat_objectives.ml>`.
``init_cont`` shows how to load/initialize the Why3 API. We will briefly follow
the code of this function here:

Find the session directory and load the session (simplified):

.. code-block:: Ocaml

  let session_dir = get_session_dir () in
  let (session, use_shapes) =
    Session_itp.load_session session_dir
  in

Then, initialize a controller:

.. code-block:: Ocaml

  let c = Controller_itp.create_controller Gnat_config.config Gnat_config.env session in

Potentially add files to the session or reload the existing files and then
return the controller:

.. code-block:: Ocaml

                if b then
                  Controller_itp.add_file c Gnat_config.filename;
                if a then
                  Controller_itp.reload_files c ~use_shapes;
                c

The comments for ``add_files`` and ``reload_files`` should be enough to not add
more here.

So, this was the first part of
:download:`Controller <../../why3/src/session/controller_itp.mli>`. The second
part is actually a functor that takes a Scheduler as argument. This part will
have functions like ``schedule_proof_attempt`` (calls a prover) or
``schedule_transformation`` (calls a transformation) which are used to launch
the execution of transformation/proofs.

This controller part is shared between script tools (GNATWhy3) and interactive
tools (Manual proof). The functions used will be the same for both tools but
the underlying scheduler will be different. It is also this scheduling part of
the tool that is supposed to be exchanging informations with why3server (see
``why3/src/server``).

Scheduler
"""""""""

The Scheduler module type is defined in
:download:`Controller <../../why3/src/session/controller_itp.mli>`

.. code-block:: Ocaml

    module type Scheduler = sig

    val blocking: bool
    (** Set to true when the scheduler should wait for results of why3server
        (script), false otherwise (ITP which needs reactive scheduling) *)

    val multiplier: int
    (** Number of allowed task given to why3server is this number times the
        number of allowed proc on the machine.
    *)

    val timeout: ms:int -> (unit -> bool) -> unit
    (** [timeout ~ms f] registers the function [f] as a function to be
    called every [ms] milliseconds. The function is called repeatedly
    until it returns false. the [ms] delay is not strictly guaranteed:
    it is only a minimum delay between the end of the last call and
    the beginning of the next call.  Several functions can be
    registered at the same time. *)

    val idle: prio:int -> (unit -> bool) -> unit
    (** [idle prio f] registers the function [f] as a function to be
    called whenever there is nothing else to do. Several functions can
    be registered at the same time.  Several functions can be
    registered at the same time. Functions registered with higher
    priority will be called first. *)

    end

The interface is consistant with an interactive environment but this does not
mean that the scheduler used for GNATWhy3 is interactive. The used Scheduler
module for GNATWhy3 is used in the following two places
[short explanation: Part of
:download:`gnat_objectives.ml <../../why3/src/gnat/gnat_objectives.mli>` is
also a functor taking a Scheduler]:

.. code-block:: Ocaml

   (* From gnat_objectives.ml *)
   module Make (S: Controller_itp.Scheduler) = struct
   module C = Controller_itp.Make(S)
   (* [...] *)
   end

   (* From gnat_main.ml *)
   module C = Gnat_objectives.Make (Gnat_scheduler)

The scheduler used for GNATWhy3 can be found in
:download:`gnat_scheduler.ml <../../why3/src/gnat/gnat_scheduler.ml>`. A
chosen part of the module is shown here. It shows that any idle function that
is scheduled with function idle is actually immediately executed (this does not
correspond to an interactive behavior: it is more of a hack to use the same
interfaces).

.. code-block:: Ocaml

    module Gnat_scheduler = struct

      let blocking = true

      let multiplier = 50

      (* the private list of functions to call on idle. *)
      let idle_handler : (unit -> bool) list ref = ref []

      let insert_idle_handler f =
        idle_handler := !idle_handler @ [f]

      let idle ~(prio:int) f =
        insert_idle_handler f;
        wait_for_idle ()

    end

Scheduling prover/transformation with controller
""""""""""""""""""""""""""""""""""""""""""""""""

Getting back to the
:download:`Controller <../../why3/src/session/controller_itp.mli>` module, the
most important is to know that this module contains safe scheduling functions.
``schedule_proof_attempt`` is used to call a prover on a specific node:

.. code-block:: Ocaml

             schedule_proof_attempt :
                controller ->
                proofNodeID ->
                Whyconf.prover ->
                ?save_to:string ->
                limit:Call_provers.resource_limit ->
                callback:(proofAttemptID -> proof_attempt_status -> unit) ->
                notification:notifier -> unit

As expected, it takes the controller, the proofNode, the prover and the limit
you want to apply. When the loop queries begins the execution of a prover or
when it updates the status of the proofAttempt, it will call the ``callback``.
In GNATWhy3, the ``callback`` given would typically be a function called
``interpret_result`` from
:download:`gnat_main <../../why3/src/gnat/gnat_main.ml>`.

.. code-block:: Ocaml

   interpret_result c pa pas =
      (* callback function for the scheduler, here we filter if an interesting
         goal has been dealt with, and only then pass on to handle_vc_result *)
      match pas with
      | Controller_itp.Done r ->
        let session = c.Controller_itp.controller_session in
        let goal = Session_itp.get_proof_attempt_parent session pa in
        let answer = r.Call_provers.pr_answer in
        if answer = Call_provers.HighFailure && Gnat_config.debug &&
          not (Gnat_config.is_ce_prover session pa) then
           Gnat_report.add_warning r.Call_provers.pr_output;
        handle_vc_result c goal (answer = Call_provers.Valid)
      | _ ->
         ()

This function match on the ``proof_attempt_status`` and does nothing if the
prover did not finish its execution. If it does, it will update the status of
the corresponding ``objective`` (see gnat_objectives: objective is the pendant
of an high-level check from SPARK. Contrary to proofNodeid, those can contain
several goals).

In the context of manual proof, the callback given will be quite different (in
:download:`itp_server.ml <../../why3/src/session/itp_server.ml>`.

.. code-block:: Ocaml

  let callback_update_tree_proof cont panid pa_status =
    let ses = cont.controller_session in
    let node_id = (* corresponding node in the tree [...] *)
    in

    let pa = get_proof_attempt_node ses panid in
    let new_status =
      Proof_status_change (pa_status, pa.proof_obsolete, pa.limit)
    in
    P.notify (Node_change (node_id, new_status))

For manual proof, this ``callback`` will mainly be used to update the
interactive interface. Here, we see that it uses the status given ``pa_status``
to create a message to the ``ide`` that is notified through ``P.notify``. We
will get back to this in section :ref:`manual_proof`.

The possible ``proof_attempt_status`` are the following:

.. code-block:: Ocaml

  type proof_attempt_status =
  | Undone   (** prover was never called *)
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Done of Call_provers.prover_result (** external proof done *)
  | Interrupted (** external proof has never completed *)
  | Detached (** parent goal has no task, is detached *)
  | InternalFailure of exn (** external proof aborted by internal error *)
  | Uninstalled of Whyconf.prover (** prover is uninstalled *)
  | UpgradeProver of Whyconf.prover (** prover is upgraded *)

The notification argument is a special function used for interactive proof that
is not necessary for script programs. In interactive mode, it is used to notify
proved status in existing nodes.

(``save_to`` is a detail: it is an optional argument given by GNATWhy3 to
force the name of the produced .smt2 file)

The same kind of arguments are given for ``schedule_transformation`` (note that
transformations are actually never scheduled: they are always executed
directly).

.. code-block:: Ocaml

                schedule_transformation :
                  controller ->
                  proofNodeID ->
                  string ->
                  string list ->
                  callback:(transformation_status -> unit) ->
                  notification:notifier -> unit

Here, the first string is the name of the transformations and the list of
string in the arguments (potentially nil).

The transformation_status is the following:

.. code-block:: Ocaml

   type transformation_status =
     | TSscheduled
     | TSdone of transID
     | TSfailed of (proofNodeID * exn)


Internal Queue scheduling in controller
"""""""""""""""""""""""""""""""""""""""

.. warning:: ??? TODO This is a well known problem that the current way things
             are defined in the controller might be difficult to understand at
             first glance.

The behavior of the controller when launching a prover mainly relies on the
Queue of prover calls that are present in controller:

- Queue of scheduled proof attempts
- Queue of tasks in progress (tasks sent to why3server)
- Queue of edited proof task (for interactive use of Coq/Isabelle)

What it does internally when calling  ``schedule_proof_attempts`` is the
following:

- Add this new call to a Queue of waiting call present in ``Controller`` (it is
  put with all its arguments, callback etc),
- The code of this iteration in the queue is called on timeout by the scheduler
  regularly so that when there are less running proof, the proof_attempt can be
  send to ``why3server``,
- At some point, the code present in the ``Controller``, will execute it: it
  will generate the smt2 file and send a link to this file via a socket to the
  ``why3server``,
- The same loop will then do a wait (on timeout) regularly querying a result
  list to see if the ``why3server`` did answer something. It differs in the
  cases of a script and of interactive stuff
- When a result is given, the callback is called with its result so that
  GNATWhy3/IDE get to know about the result.


.. code-block:: Ocaml

  let scheduled_proof_attempts : sched_pa_rec Queue.t = Queue.create ()

  let prover_tasks_in_progress :
      (Call_provers.prover_call,tasks_prog_rec) Hashtbl.t =
    Hashtbl.create 17

  let prover_tasks_edited = Queue.create ()

  let number_of_running_provers = ref 0

The calls are handled by a procedure called ``timeout_handler`` which is called
as a timeout: called once but it then is called indefinitely by the scheduler
every ?? milliseconds. In GNATWhy3, the scheduler eventually decides
to stop executing when the observer raises the exception ``Exit`` during the
call to ``update_observer`` inside this ``timeout_handler`` function. As a
reminder, an observer is a part of the scheduler that can be registered. In
interactive proof, it is used to count the number of proof currently
executing. In GNATWhy3, it detects when no proofs are executing to trigger the
end of the execution (from last lines of gnat_objectives):

.. code-block:: Ocaml

  (* This register an observer that can monitor the number of provers
     scheduled/running/finished *)
  let (_: unit) = C.register_observer (fun x y z ->
    if x = 0 && y = 0 && z = 0 then
      raise Exit)

.. warning:: Perhaps we could use something more reliable (related to
             objectives for example). Here is an argument why it is correct:
             GNATWhy3 is sequential, transformations are sequential and when a
             proof ends a callback is supposed to trigger new ones if needed.
             So, this means that when no prover is executing anymore (and all
             proofs got through the ``handle_result`` callback), nothing is
             left to do for GNATWhy3. So, we exit.

The following code is the one of the ``timeout_handler`` from
:download:`controller_itp.ml <../../why3/src/session/controller_itp.ml>` which
is the only function used on ``timeout`` (from ``Scheduler``, only relevant
portions are taken: please refer to the code):

.. code-block:: Ocaml

  let timeout_handler () =
    if Hashtbl.length prover_tasks_in_progress != 0 then begin

The first part is querying the results if any prover was launched: if it was
``prover_tasks_in_progress`` should not be empty.

.. code-block:: Ocaml

      let results = Call_provers.get_new_results ~blocking:S.blocking in

``Call_provers.get_new_results`` (from
:download:`call_provers.mli <../../why3/src/driver/call_provers.mli>`)
is a low-level function which directly wait on the socket given by
``why3server``. Depending on the ``~blocking`` argument, it will block until
results are given or not.

.. code-block:: Ocaml

      List.iter (fun (call, prover_update) ->
        match Hashtbl.find prover_tasks_in_progress call with
        | ptp ->
          begin match prover_update with
          | Call_provers.ProverStarted ->
            assert (not ptp.tp_started);
            ptp.tp_callback Running;
            incr number_of_running_provers;
            Hashtbl.replace prover_tasks_in_progress ptp.tp_call
              {ptp with tp_started = true}
            (* [...] *)
        end
        | exception Not_found -> ()
    ) results;

The previous iterations on the results tries to find back the ``call`` result
in the ``Queue`` known to ``Controller`` (``prover_tasks_in_progress``) and to
call the ``callback`` with the current status of the proof: this will have the
effect to inform the IDE/GNATWhy3 because the callbacks are made so that they
have functions that have an effect on these.
The matching above can raise the ``Not_found`` exception because the list of
results is unordered: it is possible to have the ``Started`` information after
the ``Done`` information for a prover.

The following part is used for edition (Coq/Isabelle proof) and we will not
comment on it:

.. code-block:: Ocaml

  (* When blocking is activated, we are in script mode and we don't want editors
     to be launched so we don't need to go in this loop. *)
  if not S.blocking then begin
    (* Check for editor calls which are not finished *)
    let q = Queue.create () in
    while not (Queue.is_empty prover_tasks_edited) do
      (* call is an EditorCall *)
      let (callback,call,ores) as c =
        Queue.pop prover_tasks_edited in
      let prover_update = Call_provers.query_call call in
      match prover_update with
      | Call_provers.NoUpdates -> Queue.add c q
      | Call_provers.ProverFinished res ->
          (* res is meaningless for edition, we returned the old result *)
          (* inform the callback *)
          callback (match ores with None -> Done res | Some r -> Done r)
      | _ -> assert (false) (* An edition can only return Noupdates or finished *)
    done;
    Queue.transfer q prover_tasks_edited;
  end;


The below code is used to launch new provers from the scheduled ones (from
Queue ``scheduled_proof_attempts``: those are added when calling function
``schedule_proof_attempt``).
The function ``build_prover_call`` is used to make a call to the low-level
function which will build a .smt2 file with the right driver and send it to the
``why3server``. The low-level function used is ``Driver.prove_task`` from
:download:`driver.mli <../../why3/src/driver/driver.mli>`.

.. code-block:: Ocaml

      for _i = Hashtbl.length prover_tasks_in_progress
          to S.multiplier * !session_max_tasks do
        let spa = Queue.pop scheduled_proof_attempts in
        try build_prover_call spa
        with e when not (Debug.test_flag Debug.stack_trace) ->
          spa.spa_callback (InternalFailure e)
      done

This next part now updates the observer (which can be used to decide the end of
the process in GNATWhy3 or to display the number of prover running in the IDE of
Why3) according to the new status of ``scheduled_proof_attempts``
``prover_tasks_in_progress`` and ``number_of_running_provers``:

.. code-block:: Ocaml

    update_observer ();

The last part is used to notify the timeout function that we want this function
to be called again by the Scheduler (by returning true):

.. code-block:: Ocaml

    true
