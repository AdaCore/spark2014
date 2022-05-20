------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--              Copyright (C) 2013-2022, Capgemini Engineering              --
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
------------------------------------------------------------------------------

--  This package looks at the produced graphs and emits error messages

with Sem_Util;         use Sem_Util;
with Sinfo.Nodes;      use Sinfo.Nodes;
with SPARK_Definition; use SPARK_Definition;

package Flow.Analysis is

   procedure Sanity_Check (FA   : in out Flow_Analysis_Graphs;
                           Sane :    out Boolean);
   --  Check the following basic properties:
   --     - is aliasing present (using the flag FA.Aliasing_Present)?
   --     - absence of variables in default initializations of record
   --       components and discriminants (SPARK LRM 4.4(2))
   --     - are all global variables used declared as such?
   --     - are we updating a variable we shouldn't (in parameter / global or
   --       package external state in an elaboration)
   --
   --  Complexity is O(N)

   procedure Find_Unwritten_Exports (FA : in out Flow_Analysis_Graphs);
   --  Find outputs which are never written to.
   --
   --  Complexity is O(N)

   procedure Find_Ineffective_Imports_And_Unused_Objects
     (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind in Kind_Subprogram | Kind_Task;
   --  Find all ineffective initial values and all unused objects.
   --
   --  Complexity is O(N^2) and O(N) respectively.

   procedure Find_Ineffective_Statements (FA : in out Flow_Analysis_Graphs);
   --  Find all ineffective statements.
   --
   --  Complexity is O(N^2)

   procedure Find_Dead_Code (FA : in out Flow_Analysis_Graphs);
   --  Find all obviously dead code.
   --
   --  Complexity is O(N)

   procedure Find_Use_Of_Uninitialized_Variables
     (FA : in out Flow_Analysis_Graphs);
   --  Check all variables read (explicit and implicit) and issue either info
   --  messages or low/med/high checks depending on whether the variable is
   --  initialized/default initialized.
   --
   --  Complexity is O(N^2)

   procedure Find_Input_Only_Used_In_Assertions
     (FA : in out Flow_Analysis_Graphs);
   --  Detect global inputs that are only used in assertions (and therefore
   --  should be Proof_In).

   procedure Find_Illegal_Reads_Of_Proof_Ins
     (FA : in out Flow_Analysis_Graphs);
   --  Detect Proof_In globals used in non-assertion expressions

   procedure Find_Stable_Conditions (FA : in out Flow_Analysis_Graphs);
   --  Find stable loop conditions

   procedure Find_Impossible_To_Initialize_State
     (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind = Kind_Package;
   --  Finds state abstractions that are not mentioned in an Initializes aspect
   --  and are not pure global outputs of any of the package's subprograms.
   --  This makes it impossible for users of these package's to initialize
   --  those state abstractions.
   --
   --  Complexity is O(N)

   procedure Check_Depends_Contract (FA : in out Flow_Analysis_Graphs);
   --  Check the given Depends contract against the reality; do nothing if
   --  there is no such contract.
   --
   --  Complexity is O(N^2)

   procedure Check_Initializes_Contract (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind = Kind_Package;
   --  Check if the Initializes contract has extra or missing dependencies.
   --
   --  Complexity is O(N^2)

   procedure Check_Refined_State_Contract (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind = Kind_Package;
   --  Check if the Refined_State references any constant without variable
   --  inputs and if so emits a check. This enforces SPARK RM 7.2.2(16).

   procedure Check_Potentially_Blocking (FA : in out Flow_Analysis_Graphs)
   with Pre => (if Ekind (FA.Spec_Entity) = E_Package
                then not Is_Library_Level_Entity (FA.Spec_Entity));
   --  Check for potentially blocking operations in protected actions
   --
   --  The current implementation emits a message for each statement that
   --  involves a potentially blocking operation. This is enough to easily
   --  identify delay statements and entry call statements (but frontend flags
   --  them with a warning anyway).
   --
   --  For a call on a subprogram whose body contains a potentially blocking
   --  operation the idea is that once AI12-0064, i.e. the Nonblocking aspect,
   --  is implemented, the users should annotate subprograms called directly
   --  in the statements flagged by this routine as Nonblocking. This way they
   --  will progressively arrive at the one with a potentially blocking
   --  statement.
   --
   --  ??? An external call on a protected subprogram with the same target
   --  object as that of the protected action deserves a dedicated diagnostics.

   procedure Check_Prefixes_Of_Attribute_Old (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind in Kind_Subprogram | Kind_Task;
   --  We issue a high check whenever a variable that serves as a prefix of a
   --  'Old attribute is NOT an import.
   --
   --  Complexity is O(N)

   procedure Check_Aliasing (FA : in out Flow_Analysis_Graphs);
   --  Check each procedure call for aliasing
   --
   --  Complexity is O(N^2)

   procedure Check_Output_Constant_After_Elaboration
     (FA : in out Flow_Analysis_Graphs);
   --  Enforce SPARK RM 6.1.4(2) for subprograms, i.e. check that:
   --  * a subprogram does not modify variables that have
   --    Constant_After_Elaboration set.

   procedure Check_Calls_With_Constant_After_Elaboration
     (FA : in out Flow_Analysis_Graphs);
   --  Enforce SPARK RM 6.1.4(2) for packages, i.e. check that:
   --  * a subprogram or entry having an Input or Proof_In global marked as
   --    Constant_After_Elaboration shall not be called during library unit
   --    elaboration.

   procedure Check_Function_For_Volatile_Effects
     (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind in Kind_Subprogram | Kind_Task;
   --  Checks that the subprogram does not have any volatile effects except if
   --  so specified. This check is only doing something when called on
   --  functions. We also issue a warning if we are dealing with a volatile
   --  function that has no volatile effects.
   --
   --  Complexity is O(N)

   procedure Check_Ghost_Procedure_Outputs (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind = Kind_Subprogram;
   --  Check if the ghost procedure has any non-ghost (global) outputs. This is
   --  to enforce SPARK RM 6.9(20).

   procedure Check_Hidden_State (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind = Kind_Package;
   --  Check state hidden in a package for restrictions that cannot be enforced
   --  in the frontend, i.e.:
   --
   --  * examine constants (because frontend can't determine whether they have
   --    variable inputs),
   --
   --  * re-examine hidden variables and states that are implicitly lifted to
   --    singleton abstract states (because frontend only deals with explicitly
   --    annotated code),
   --
   --  * check consistency between the Part_Of in a child unit and
   --    Refined_State in its parent unit (because frontend can see only one
   --    unit at a time).

   procedure Check_Concurrent_Accesses (GNAT_Root : Node_Id)
   with Pre => Nkind (GNAT_Root) = N_Compilation_Unit;
   --  Check exclusivity rules for concurrent accesses to library-level objects

   procedure Check_CAE_In_Preconditions (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind = Kind_Subprogram;
   --  Check that preconditions of protected operations only reference global
   --  variables that have Constant_After_Elaboration set.

   procedure Check_Terminating_Annotation (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind in Kind_Subprogram | Kind_Package;
   --  Checks if the terminating annotation is consistent with the results from
   --  flow analysis, emits a message if not.

   procedure Check_Constant_Global_Contracts (E : Entity_Id)
   with Pre => Ekind (E) in E_Function
                          | E_Procedure
                          | Entry_Kind
                          | E_Task_Type
               and then not Entity_Body_In_SPARK (E);
   --  Check if the global contracts directly reference any constant without
   --  variable inputs. This enforces SPARK RM 6.1.4(16).

private

   type Var_Use_Kind is (Use_Read, Use_Write, Use_Any);

   function First_Variable_Use (N        : Node_Id;
                                Scope    : Flow_Scope;
                                Var      : Flow_Id;
                                Precise  : Boolean;
                                Targeted : Boolean := False)
                                return Node_Id;
   --  Given a node N, traverse the tree to find the most deeply nested node
   --  which still uses Var. If Precise is True look only for Var (for example
   --  R.Y), otherwise also look for the entire variable represented by Var (in
   --  our example we'd also look for R).
   --
   --  When Targeted is set, we only search under specific nodes of the AST:
   --
   --    * For assignment statement, we only look at the right hand side of the
   --      assignment.
   --
   --    * For if statements we only check under the condition.
   --
   --  If we cannot find any suitable node we return N itself.

   function First_Variable_Use (FA      : Flow_Analysis_Graphs;
                                Var     : Flow_Id;
                                Kind    : Var_Use_Kind;
                                Precise : Boolean)
                                return Node_Id;
   --  Find a suitable node in the tree which uses the given variable. If
   --  Precise is True look only for Var (for example R.Y), otherwise we also
   --  look for the entire variable represented by Var (in our example we'd
   --  also look for R).
   --
   --  If no suitable node can be found we return FA.Spec_Entity as a fallback

end Flow.Analysis;
