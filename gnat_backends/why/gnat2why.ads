------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             G N A T 2 W H Y                              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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
-- Translation From GNAT AST to Why3: General Model --
------------------------------------------------------

--  Translation involves 4 phases:

--    Framing           The 'frame' or 'frame condition' of the current unit U
--                      is computed, based on the information stored in the
--                      Alfa sections of ALI files for all units on which U
--                      depends recursively. This means U and all units with'ed
--                      directly or indirectly by U. The frame for a subprogram
--                      consists in all variables which this subprogram may
--                      read and/or write.

--    Detection         Each entity declared in the current unit is classified
--                      as either in the Alfa subset that can be formally
--                      analyzed, or outside this subset.  For all entities,
--                      this classification is based solely on the declaration
--                      of the entity. Additionally, subprogram bodies are
--                      classified as in or out of Alfa, based on the
--                      subprogram spec classification, the constructs used in
--                      the body of the subprogram, and the classification of
--                      the entities used in the body of the subprogram. The
--                      result of this classification is a partitioning of the
--                      program between entities and subprogram bodies in Alfa,
--                      or not in Alfa.

--    Transformation    Entities and subprogram bodies classified as in Alfa in
--                      the previous phase are transformed into a Why3
--                      declarations. These declarations are dispatched between
--                      a set of Why3 files, so that any use of an entity is
--                      preceded by its declaration.  The mapping between Ada
--                      and Why3 entities is one-to-many, in order to comply
--                      with this declaration-before-use constraint in Why3,
--                      which is not present in the source Ada code (contrary
--                      to SPARK).

--    Printing          Each Why3 file generated in the previous phase is
--                      printed on disk.

-----------------------------
-- Dispatching of Entities --
-----------------------------

--  For each Ada unit, six Why3 files are generated, which correspond to the
--  six values of Why.Inter.Why_File_Enum. The table below summarizes, for
--  a unit defined in file 'u.ads' or 'u.adb', each of the six values, the
--  corresponding Ada entities that are translated and the name of the
--  generated file.

--     value               Ada entity                Why3 file name
--     --------------------------------------------------------------------
--  1. WF_Types_In_Spec    types in spec             u__types_in_spec.mlw
--  2. WF_Types_In_Body    types in body             u__types_in_body.mlw
--  3. WF_Variables        variables in spec/body    u__variables.mlw
--  4. WF_Context_In_Spec  subprogram specs in spec  u__context_in_spec.mlw
--  5. WF_Context_In_Body  subprogram specs in body  u__context_in_body.mlw
--  6. WF_Main             subprogram bodies         u__package.mlw

--  Each Alfa entity defined in unit U is transformed into a set of Why3
--  declarations in the files above. These declarations are grouped in theories
--  or modules, so that the context used for generating VCs for a given module
--  is minimized, which leads to smaller (hence easier) VCs. This context is
--  given by a set of includes between theories and modules, which can belong
--  to the same or different files. Inclusion between theories/modules in the
--  same file respects the principle that any inclusion is preceded by the
--  definition of the included theory/module. Inclusion between
--  theories/modules in different files is only from a file of higher rank to
--  a file of lower rank, or to a file with same rank but avoiding cycles.

--  The generation of theories/modules for an entity in Alfa proceeds as
--  follows, where the corresponding type/context file of an entity is the
--  Type_/Context_ In_Spec file if the entity is declared in the unit spec,
--  Type_/Context_ In_Body file if the entity is declared in the unit body.

--     . Constant (IN parameter, named number and constant object)
--         A logic function is created in the corresponding context file. For a
--         named number, or a constant object, a defining axiom is created in
--         the same file. For a deferred constant, the logic function and its
--         defining axiom are defined in separate theories, so that the value
--         of the completion is only available for proofs on code inside the
--         unit that has visibility over the completion. Otherwise, the logic
--         function and its defining axiom are defined in the same theory.

--     . Variable (non-constant object)
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
--         source Ada contract.

--         For an Ada function, a logic function is created before the program
--         function in the same module.  The logic function is called in the
--         postcondition of the program function, to give a value to the
--         result. For an expression function, a defining axiom for the logic
--         function is created in a separate module. This axiom is only
--         available for proofs on code that has visibility over the body of
--         the expression function.

--         A program function with definition is created in its own module, in
--         the main file. VCs generated for this program function correspond to
--         checking the absence of run-time errors on the precondition of the
--         subprogram in any context.

--         If the body of the subprogram is in Alfa, a program function with
--         definition is created in its own module, in the main file. VCs
--         generated for this program function correspond to checking the
--         absence of run-time errors and the contract of the subprogram.

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

--     . Slice
--         A logic function and a defining axiom are created in their own
--         module, in the corresponding context file. The logic function takes
--         as parameters the prefix and bounds for the slice.

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
--  -- Labels for terms --
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
--  "GP_Reason:<VC_Kind>"
--     The reason for a VC. <VC_Kind> should be obtained by VC_Kind'Image.
--     Required for all VC nodes.
--
--  "keep_on_simp"
--     Disallows simplification of that node. Required for all VC nodes.
--  "GP_Pretty_Ada:<string>"
--     Gives the original Ada source for the Why3 term, as a string.
--     Is used for pretty printing explanations for a VC

--  -----------------------------
--  -- Labels for declarations --
--  -----------------------------

--  "GP_Subp:<file:line>"
--     This label is required for all subprograms that generate VCs. It is
--     used to easily filter the subprogram in VC selection.

package Gnat2Why is

   type Transformation_Phase is
     (Generate_Logic,
      --  Generation of Why3 code for logic constructs.
      Generate_VCs_For_Pre,
      --  Generation of Why3 code to check absence of run-time errors in
      --  preconditions.
      Generate_VCs_For_Post,
      --  Generation of Why3 code to check absence of run-time errors in
      --  postconditions (including Contract_Case).
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
     Generate_VCs_For_Pre ..
     --  Generate_VCs_For_Post
     --  Generate_VCs_For_Assert
     Generate_VCs_For_Body;
   --  Transformation phases for the generation of VCs

   subtype Generate_VCs_For_Assertion is Transformation_Phase range
     Generate_VCs_For_Pre ..
     --  Generate_VCs_For_Post
     Generate_VCs_For_Assert;
   --  Transformation phases for the generation of VCs to check absence of
   --  run-time errors in assertions.

   subtype Generate_For_Body is Transformation_Phase range
     Generate_VCs_For_Body ..
     Generate_Contract_For_Body;
   --  Transformation phases for the generation of Why3 code corresponding to
   --  the body of a subprogram.

end Gnat2Why;
