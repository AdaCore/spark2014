------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             G N A T 2 W H Y                              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

------------------------------------------------------
-- Translation from GNAT AST to Why3: General Model --
------------------------------------------------------

--  Translation involves 4 phases:

--    Framing           The 'frame' or 'frame condition' of the current unit U
--                      is computed, based on the information stored in the
--                      SPARK sections of ALI files for all units on which U
--                      depends recursively. This means U and all units with'ed
--                      directly or indirectly by U. The frame for a subprogram
--                      consists in all variables which this subprogram may
--                      read and/or write.

--    Detection         Each entity declared in the current unit is classified
--                      as either in the SPARK subset that can be formally
--                      analyzed, or outside this subset.  For all entities,
--                      this classification is based solely on the declaration
--                      of the entity. Additionally, subprogram bodies are
--                      classified as in or out of SPARK, based on the
--                      subprogram spec classification, the constructs used in
--                      the body of the subprogram, and the classification of
--                      the entities used in the body of the subprogram. The
--                      result of this classification is a partitioning of the
--                      program between entities and subprogram bodies in
--                      SPARK, or not in SPARK.

--    Transformation    Entities and subprogram bodies classified as in SPARK
--                      in the previous phase are transformed into a Why3
--                      declarations. These declarations are dispatched into
--                      sections of a Why3 file, that any use of an entity is
--                      preceded by its declaration.  The mapping between Ada
--                      and Why3 entities is one-to-many, in order to comply
--                      with this declaration-before-use constraint in Why3,
--                      which is not present in the source Ada code (contrary
--                      to SPARK).

--    Printing          The Why3 file generated in the previous phase is
--                      printed on disk.

-----------------------------
-- Dispatching of Entities --
-----------------------------

--  For each Ada unit, a Why file is generated, which contains four sections
--  corresponding to the four values of Why.Inter.Why_Section_Enum. The table
--  below summarizes, for a unit defined in file 'u.ads' or 'u.adb', each of
--  the six values, the corresponding Ada entities that are translated and the
--  name of the generated file.

--     value               Ada entity
--     ----------------------------------------------
--  1. WF_Pure             types and pure functions
--  2. WF_Variables        variables
--  3. WF_Context          subprogram specs and aggregates
--  4. WF_Main             subprogram bodies for VC generation

--  Each SPARK entity defined in unit U or in one of the with'ed specs is
--  transformed into a set of Why3 declarations in the sections above. These
--  declarations are grouped in theories or modules, so that the context used
--  for generating VCs for a given module is minimized, which leads to smaller
--  (hence easier) VCs. This context is given by a set of includes between
--  theories and modules. All these modules are then dumped into a single
--  Why file "u.mlw", in the correct order as above.

--  The generation of theories/modules for an entity in SPARK proceeds as
--  follows:

--     . Constant (IN parameter, named number and constant object)
--         A logic function is created in the corresponding context file. For a
--         named number, or a constant object, a defining axiom is created in
--         the same file. For a deferred constant, the logic function is
--         defined in a theory when translating the partial view, and its
--         defining axiom is defined in a separate theory when translating the
--         complete view. Otherwise, the logic function and its defining axiom
--         are defined in the same theory. For all constant objects, a closure
--         theory is defined which includes all axioms for relevant functions
--         defining the constant.
--
--         For scalar constants, the Why base type (int for float) is used for
--         the declaration instead of the abstract type.

--     . Variable (non-constant object, IN OUT or OUT parameter)
--         A ref is created in the variable file, in its own module. A type
--         alias is created in the same module, so that the name of a
--         variable's type can be deduced from the variable's name. This is
--         used when creating logic functions from Ada functions which read
--         global variables that are not visible (say, declared in another
--         unit's body), so that we can name the type of the corresponding
--         additional parameter.

--     . Type
--         An abstract type is created, along with defining axioms, in its own
--         module, in the corresponding type file. See gnat2why-types.ads for
--         more details.

--     . Subprogram
--         A program function without definition is created in its own module,
--         in the corresponding context file. This program function has effects
--         corresponding to the frame computed for the subprogram, and a
--         contract (precondition and postcondition) corresponding to the
--         source Ada contract. This program function is used to translate
--         calls to the Ada subprogram in Why3 program expressions. This
--         program function has as many parameters as the Ada subprogram and
--         as many global reads/writes. As an optimization, IN parameters of
--         discrete types are translated as "int", and floating point
--         parameters are translated as "float".

--         For an Ada function, a logic function is created before the program
--         function in the same module.  The logic function is called in the
--         postcondition of the program function, to give a value to the
--         result. This logic function is also used to translate calls to the
--         Ada subprogram in Why3 logic expressions (assertions).

--         For a function or procedure without global reads or global writes,
--         the module above is created in the corresponding type file, instead
--         of the corresponding context file. This allows such subprograms to
--         be passed as parameters to generic instantiations of units whose Why
--         code is manually written. This is the case in particular for the
--         formal container library. Indeed, these instantiations are created
--         in type files, as they introduce both types and functions, so they
--         should come as early as possible in the chain of includes between
--         Why generated files.

--         For an expression function whose body is in SPARK, an additional
--         theory is created for the defining axiom of the logic function.
--         For every subprogram (both functions and procedures), an additional
--         theory is created for including all axioms of all expression
--         functions which participate in the definition of the subprogram
--         spec (the subprogram contract, which includes the body for
--         expression functions). These theories are created in the
--         corresponding context file, whether the theory they complete is
--         defined in the type or context file.

--         These theories are seen as completions of the theory defining the
--         subprogram. When translating code that uses the subprogram, the
--         completions theories are included only if they were previously
--         generated for the current unit, or if the subprogram belongs in
--         another unit. So axioms are available for proofs on code that has
--         visibility over the body of the expression function.

--         As an example, consider the following code:

--              p.ads           p.adb           q.ads           q.adb

--           fun F1 is (1);                  fun G1 is (1);
--           fun F2 is                       fun G2;         fun G2 is
--             (F1+G1-1);                                      (G1+G3-1);
--           fun F3;         fun F3 is (1);  fun G3;         fun G3 is (1);
--           fun F4 is                       fun G4 is
--             (F3+G3-1);                      (G1+G3-1);

--         For every function, 3 theories are generated, for example for F2:
--           - a theory F2 defining the logic function f2
--           - a theory F2__expr_fun_axiom defining the axiom for f2, namely
--             that: f2 = f1 + g1 - 1
--           - a theory F2__expr_fun_closure including all available axioms for
--             f2, namely here:
--               F2__expr_fun_axiom (f2 = f1 + g1 - 1)
--               F1__expr_fun_axiom (f1 = 1)
--               G1__expr_fun_axiom (g1 = 1)
--             This is only the case because the definitions of F1 and G1 are
--             visible in the unit where F2 is defined. For F4, the closure
--             only contains its own axiom, not the ones for F3 and G3,
--             because F4 is defined in the spec of P, which has no visibility
--             over the body of P (where F3 is defined) and the body of Q
--             (where G3 is defined).

--         The proof of a subprogram client unit of P and Q will have access to
--         the axioms for all expression functions defined in p.ads and q.ads
--         (whether in the public or the private part, but not in the body).
--         The order of declarations and definitions in p.ads and q.ads should
--         have no impact.

--         A parameterless program function with definition is created in its
--         own module, in the main file. The body of this program function is
--         the translation as a Why3 program expression of the precondition.
--         This program function has no contract. Accesses to the parameters
--         of the Ada subprogram are translated as accesses to the
--         corresponding global declarations. VCs generated for this
--         program function correspond to checking the absence of run-time
--         errors on the precondition of the subprogram in any context.

--         If the body of the subprogram is in SPARK, a parameterless program
--         function with definition is created in its own module, in the main
--         file. VCs generated for this program function correspond to
--         checking the absence of run-time errors and the contract of the
--         subprogram.

--         As described in the section about constants and variables, global
--         declarations are generated for all subprogram parameters. These
--         global variables are of the Why3 type that corresponds to the Ada
--         type.

--  Additionally, some Ada nodes lead to the definition of theories/modules as
--  follows:

--     . String literal
--         An uninterpreted logic function is created in its own module, in the
--         corresponding context file. The logic function takes no parameters.

--     . Array aggregate
--         A logic function and a defining axiom are created in their own
--         module, in the corresponding context file. The logic function takes
--         as parameters all the values of components of the (possibly
--         multidimensional) aggregate.

--  -------------------------------------------------
--  -- Translation of Specific Language Constructs --
--  -------------------------------------------------

--  Protected Types
--  ---------------
--
--  The frontend generated protected types even for proctected objects without
--  explicit type declaration. Protected types are handled just as records with
--  discriminants. The complex part are calls to subprograms of the protected
--  object.
--  * When translating the subprogram declaration: The protected subprogram's
--    first formal is an implicit "self" objects whose type is the protected
--    type.
--  * When translating the subprogram body: an extra "self" object is
--    introduced for internal calls and direct manipulation of fields.
--  * When translating calls: the self object (internal calls) or the prefix
--    (external calls) needs to be passed as first argument
--  * When translating references to fields: The self object needs to be
--    prepended

--  Global variables which are "part_of" a protected object are considered
--  fields of the corresponding protected type (and are generated as why3
--  fields). Variables "part_of" a task are handled just as other variables
--  in proof.

--  The checks related to pragma Attach_Handler (Ada RM C.3.1(10/3)) are done
--  on translation of the declaration of a protected object.

--  The checks related to the ceiling priority protocol are done when
--  processing a task type body. There, we analyze the "call graph" of the task
--  and check whether the call graph violates the ceiling protocol (Ada RM D.1
--  and D.3).

------------------------------------
-- Labels Interpreted by gnatwhy3 --
------------------------------------

--  In addition to the Why3 program, more information is sometimes needed,
--  for example for error reporting, showing VCs in a format close to Ada
--  syntax and so on. Why3 allows giving such extra information in the form
--  of labels, which can annotate terms/program expressions and identifier
--  declarations. This section is an exhaustive list of all labels that are
--  generated by gnat2why, and interpreted by gnatwhy3. Note that labels
--  should never influence the actual interpretation of the program, because
--  we want to guarantee that the standard Why3 tools can read programs
--  generated by gnat2why.

--  In the following description, labels are enclosed in quotes, and parts
--  of the labels that must be replaced by concrete strings are enclosed by
--  < >.
--
--  ----------------------
--  -- Labels for Terms --
--  ----------------------
--
--  "GP_Sloc:<file1:line1:col1:...:file_n:line_n:col_n>"
--  the encoding of a GNAT Source location. It is a list of triples, where
--  the elements of the list and the triples themselves are separated by a
--  colon. The first Sloc is the most generic, the last one is the last
--  instantiation.
--  For VCs, we use the prefix "GP_Sloc_VC" instead of "GP_Sloc" to
--  differentiate between VC positions and other SLOCs
--
--  "GP_Id:<Integer>" The number of the check. This is used a unique id
--     identifying a check in the Ada source. It is used to communicate results
--     back from gnatwhy3 to gnat2why.
--
--  "GP_Reason:<VC_Kind>"
--     The reason for a VC. <VC_Kind> should be obtained by VC_Kind'Image.
--     Required for all VC nodes.
--
--  "keep_on_simp"
--     Disallows simplification of that node. Required for all VC nodes.
--
--  "GP_Pretty_Ada:<integer>"
--     Is used for VCs which are a subgoal of some VC (like conjuncts of a
--     postcondition). The integer is the Node_Id of some node in the GNAT
--     tree. This node will be used for pretty-printing explanations for a VC
--
--  "GP_Shape:<string>"
--     labels a node as introducing a special Ada structure (like if, while,
--     loop etc). This is used for producing better filenames for manual proof
--

--  -----------------------------
--  -- Labels for Declarations --
--  -----------------------------

--  "GP_Subp:<file:line>"
--     This label is required for all subprograms that generate VCs. It is
--     used to easily filter the subprogram in VC selection.
--
--  "model"
--     This label identifies elements that should be included in the
--     counterexample model.
--
--  "model_projected"
--     This label identifies elements that should be included in the
--     counterexample model.
--     Unlike the label "model", the value of the element can be projected
--     using a projection function (specified using the meta model_projection)
--
--  "model_trace:name"
--      This label specifies the name that will be reported in a
--      counterexample for this element. If it labels projection function, it
--      specifies the name that should be added to the element name when the
--      element is projected.
--      Should be used either to for projection functions or together with
--      label "model" or "model_projected".
--
--  "vc:annotation"
--      This label identifies the construct that triggers the VC and it is not
--      postcondition.
--
--  "model_vc_post"
--      This label identifies the construct that triggers the VC and it is
--      postcondition.

-----------------------------------
-- Metas Interpreted by gnatwhy3 --
-----------------------------------

--  "model_projection"
--      This meta marks a function as projection. Projections functions project
--      values of why abstract types to concrete values.
--      The function F is projection function for abstract type T if it is
--      marked with the meta "model_projection" and has a single argument of
--      type T.
--      Note that there can be more projection functions for a single type T.
--      This is used when T is record type.

package Gnat2Why is

   type Transformation_Phase is
     (Generate_Logic,
      --  Generation of Why3 code for logic constructs.
      Generate_VCs_For_Contract,
      --  Generation of Why3 code to check absence of run-time errors in
      --  pre and post, and Contract_Cases, and that these guards are disjoint
      --  and complete.
      Generate_VCs_For_Assert,
      --  Generation of Why3 code to check absence of run-time errors in
      --  all assertions except precondition and postcondition.
      Generate_VCs_For_Body,
      --  Generation of Why3 code to check absence of run-time errors in
      --  the body of a subprogram, including the verification of all
      --  intermediate assertions (excluding the postcondition).
      Generate_Contract_For_Body
      --  Generation of Why3 code to check that a subprogram body implements
      --  its contract, that is, the postcondition can be proved.
     );
   --  Transformation phases, which impact the way code is transformed from Ada
   --  to Why3. For example, references to pre-state values (X'Old) are
   --  transformed differently in the context of generating VCs for run-time
   --  errors, or in the context of generating a postcondition in Why3.

   subtype Generate_VCs is Transformation_Phase range
     Generate_VCs_For_Contract ..
     --  Generate_VCs_For_Assert
     Generate_VCs_For_Body;
   --  Transformation phases for the generation of VCs

   subtype Generate_VCs_For_Assertion is Transformation_Phase range
     Generate_VCs_For_Contract ..
     Generate_VCs_For_Assert;
   --  Transformation phases for the generation of VCs to check absence of
   --  run-time errors in assertions.

   subtype Generate_For_Body is Transformation_Phase range
     Generate_VCs_For_Body ..
     Generate_Contract_For_Body;
   --  Transformation phases for the generation of Why3 code corresponding to
   --  the body of a subprogram.

end Gnat2Why;
