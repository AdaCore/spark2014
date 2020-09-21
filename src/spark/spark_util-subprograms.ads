------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 S P A R K _ U T I L - S U B P R O G R A M S              --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2016-2020, AdaCore                     --
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

with Ada.Containers;
with Gnat2Why_Args;
with Sem_Disp;

use type Ada.Containers.Count_Type;

package SPARK_Util.Subprograms is

   --------------------------------------------
   -- General Queries related to subprograms --
   --------------------------------------------

   type Analysis_Status is
     (Not_In_Analyzed_Files,
      Not_The_Analyzed_Subprogram,
      Contextually_Analyzed,
      Analyzed);
   --  Reasons for analyzing or not a subprogram/package

   function Analysis_Requested
     (E            : Entity_Id;
      With_Inlined : Boolean) return Analysis_Status
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Package
                          | E_Procedure
                          | Type_Kind;
   --  @param E entity for which requesting an analysis is meaningful, e.g.
   --     using the GPS contextual menu.
   --  @param With_Inlined True if inlined subprograms should be analyzed
   --  @return Analyzed iff subprogram, task or package E must be analyzed,
   --     because it belongs to one of the analyzed units, and either the
   --     complete unit is analyzed, or E is the specific entity whose analysis
   --     was requested. Otherwise return the reason why it is not analyzed.
   --
   --  With_Inlined is set to False in proof to avoid analyzing when possible
   --  subprograms that are inlined, and to True in flow analysis to always
   --  analyze both the inlined code and the original subprogram, otherwise
   --  analysis may miss reads of uninitialized data due to the way inlining
   --  mechanism works.
   --
   --  Here is a case where a read of uninitialized data is missed when
   --  analyzing only the inlined code:
   --
   --     procedure Test2 (Done : out Boolean) is
   --     begin
   --        if Success then
   --           Done := ...;
   --        end if;
   --     end Test2;
   --
   --     procedure Test1 (I : Integer; Success : out Boolean) is
   --        Done : Boolean := False;
   --     begin
   --        Test2 (Done);
   --        Success := Success and Done;
   --     end Test1;
   --
   --  Here is a case where a read of uninitialized data is missed when
   --  analyzing only the original subprogram (and silencing flow analysis
   --  messages on the inlined code):
   --
   --     type R is record
   --        C : Integer;
   --     end record;
   --     X : R;
   --     procedure Local (Param : R) is
   --     begin
   --        Y := Param.C;
   --     end Local;
   --
   --     Local (X);

   function Analysis_Requested
     (E            : Entity_Id;
      With_Inlined : Boolean) return Boolean
   is (Analysis_Requested (E, With_Inlined) = Analyzed);
   --  Variant of Analysis_Requested that ignores the reason for no analysis

   function Call_Needs_Variant_Check
     (Call : Node_Id; Enclosing_Ent : Entity_Id) return Boolean
   with
     Pre => Nkind (Call) in N_Subprogram_Call
                          | N_Entry_Call_Statement
                          | N_Op;
   --  Return True if we need to check that variants progress on Call.
   --  Enclosing_Ent should be set as the entity enclosing Call.

   function Compatible_Variants (E1, E2 : Entity_Id) return Boolean with
     Pre => Is_Subprogram_Or_Entry (E1)
     and then Is_Subprogram_Or_Entry (E2);
   --  Return True if E1 and E2 have compatible variants. For now, this means
   --  that they have the same number of variants, which matching subtypes and
   --  modes.

   function Containing_Protected_Type (E : Entity_Id) return Entity_Id
   with Pre => (case Ekind (E) is
                   when E_Component    |
                        E_Discriminant =>
                      Is_Protected_Type (Scope (E)),

                   when E_Function  |
                        E_Procedure |
                        Entry_Kind  |
                        E_Package   =>
                      Within_Protected_Type (E),

                   when others =>
                      False),
   Post => Is_Protected_Type (Containing_Protected_Type'Result);
   --  @param E a subprogram or entry or field which is part of a protected
   --            type
   --  @return the enclosing protected type

   function Enclosing_Subprogram (E : Entity_Id) return Entity_Id
     with Pre  => Ekind (E) in E_Function
                             | E_Procedure
                             | E_Task_Type
                             | Entry_Kind
                             | E_Package,
          Contract_Cases =>
               ((Ekind (E) in E_Function
                           | E_Procedure
                           | E_Task_Type
                           | Entry_Kind)
                =>
                  Enclosing_Subprogram'Result = E,

                Ekind (E) = E_Package and then Is_Library_Level_Entity (E)
                =>
                  Enclosing_Subprogram'Result = Empty,

                Ekind (E) = E_Package and then not Is_Library_Level_Entity (E)
                =>
                  Ekind (Enclosing_Subprogram'Result) in E_Function
                                                       | E_Procedure
                                                       | E_Task_Type
                                                       | Entry_Kind,

                others => False);
   --  @param E is an entry, subprogram, task, package
   --  @return If E is an entry, subprogram or task, E is returned.
   --           If E is not a library-level package, the first enclosing
   --           subprogram, task or entry is returned. Otherwise, Empty is
   --           returned.

   function Find_Contract (E : Entity_Id; Prag : Pragma_Id) return Node_Id
   with Pre  => (case Prag is
                    when Pragma_Global
                       | Pragma_Depends
                       | Pragma_Refined_Global
                       | Pragma_Refined_Depends
                    =>
                       Ekind (E) in Entry_Kind
                                  | E_Function
                                  | E_Procedure
                                  | E_Task_Type
                                  | E_Subprogram_Type,

                    when others
                    =>
                        False),
        Post => (if Present (Find_Contract'Result)
                 then Nkind (Find_Contract'Result) = N_Pragma);
   --  Contract pragmas might be attached to non-obvious entities, e.g. for
   --  single concurrent types they are attached to the corresponding anonymous
   --  concurrent object and "refined" pragmas are attached to the body. This
   --  wrapper hides this details and should be used instead of the low-level
   --  Get_Pragma.
   --
   --  Note: for contracts that can be repeated use Find_Contracts (plural).
   --
   --  ??? perhaps here we should support Classwide and Inherited arguments too
   --
   --  @param E unique entity to which a contract applies
   --  @param Prag contract identified
   --  @return pragma node or empty if no contract is present

   function Find_Contracts
     (E         : Entity_Id;
      Name      : Pragma_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Node_Lists.List
   with Pre => Ekind (E) in E_Function
                          | E_Package
                          | E_Procedure
                          | Entry_Kind
                          | E_Subprogram_Type
               and then Name in Pragma_Precondition
                              | Pragma_Postcondition
                              | Pragma_Refined_Post
                              | Pragma_Initial_Condition
               and then not (Classwide and Inherited),
     Post => (for all Expr of Find_Contracts'Result =>
                Nkind (Expr) in N_Subexpr
                and then Is_Boolean_Type (Etype (Expr)))
             and then
             (if Name not in Pragma_Precondition | Pragma_Postcondition
              then Find_Contracts'Result.Length <= 1);
   --  @param E entry, subprogram, package, task or protected type
   --  @param Name contract pragma identifier
   --  @param Classwide True when asking for the classwide version of contract
   --  @param Inherited True when asking only for inherited contracts
   --  @return list of Boolean-valued expressions for pragma Name of E
   --
   --  Note: the return value is a list and not a single expression, because
   --  pragmas Precondition/Postcondition (as opposed to Pre/Post) can be
   --  repeated. In particular, frontend splits expressions of pragma Pre/Post
   --  into individual conjuncts of the AND THEN operators for a more precise
   --  diagnostics of a failed contract.
   --
   --  ??? The returned list is only needed for Preconditions and
   --  Postconditions; for other contracts we could have simpler
   --  API (especially since they can't be classwide nor inherited).
   --
   --  ??? contract should detect invalid combinations of Ekind (E) and Name,
   --      just like it is done in Find_Contract.

   function Get_Body (E : Entity_Id) return Node_Id
   with Pre  => Ekind (E) in Entry_Kind       |
                             E_Function       |
                             E_Procedure      |
                             E_Protected_Type |
                             E_Task_Type      |
                             E_Subprogram_Type,
        Post => (if Present (Get_Body'Result)
                 then Nkind (Get_Body'Result) =
                   (case Ekind (E) is
                       when Entry_Kind       => N_Entry_Body,
                       when E_Function |
                            E_Procedure      => N_Subprogram_Body,
                       when E_Protected_Type => N_Protected_Body,
                       when E_Task_Type      => N_Task_Body,
                       when others           => raise Program_Error));
   --  @param E is an entry, subprogram or task
   --  @return the body for the given entry/subprogram/task. This is a wrapper
   --    around Entry_Body, Subprogram_Body and Task_Body.

   function Get_Body_Entity (E : Entity_Id) return Entity_Id
   with Pre  => Ekind (E) in Entry_Kind  |
                             E_Function  |
                             E_Procedure |
                             E_Task_Type,
        Post => No (Get_Body_Entity'Result)
                or else
                  (case Ekind (E) is
                      when E_Entry        =>
                         Ekind (Get_Body_Entity'Result) = E_Entry,
                      when E_Entry_Family =>
                         Ekind (Get_Body_Entity'Result) = E_Entry_Family,
                      when E_Function     =>
                         Ekind (Get_Body_Entity'Result) in E_Function |
                                                           E_Subprogram_Body,
                      when E_Procedure    =>
                         Ekind (Get_Body_Entity'Result) in E_Procedure |
                                                           E_Subprogram_Body,
                      when E_Task_Type    =>
                         Ekind (Get_Body_Entity'Result) = E_Task_Body,
                      when others         => raise Program_Error);
   --  @param E is an entry, subprogram or task
   --  @return the body entity for the given entry/subprogram/task.
   --    This is a wrapper around Entry_Body_Entity, Subprogram_Body_Entity
   --    and Task_Body_Entity.

   function Get_Execution_Kind
     (E        : Entity_Id;
      After_GG : Boolean := True) return Execution_Kind_T
   with Pre  => Ekind (E) = E_Procedure and then No_Return (E),
        Post => Get_Execution_Kind'Result in Abnormal_Termination
                                           | Infinite_Loop;
   --  @param E is a non-returning procedure
   --  @param After_GG True if this call is made after generation of globals,
   --     so we can query the globals computed for E if not specified by the
   --     user.
   --  @return the kind of execution for E
   --
   --  Infer whether a call to E ends abnormally or loops infinitely. If a
   --  subprogram has an output, we assume that it contains an infinite loop.
   --  If it does not, we assume it is a thinly veiled wrapper around an
   --  exception raising program.
   --
   --  Certainly, if you have a procedure that never returns due to an
   --  exception, and it is implemented in SPARK, then you will run into
   --  trouble unless there is nothing of interest going on in it.
   --
   --  If we get this wrong, it is not the end of the world, as failure is
   --  safe:
   --
   --  A) If the procedure throws an exception, but we think it loops
   --     forever (because it has outputs), then you might get *extra*
   --     data dependencies.
   --
   --  B) If the procedure loops forever, and:
   --     i) it has no outputs, its indistinguishable from an exception
   --     ii) it has outputs we classify it correctly
   --
   --  C) If the procedure loops forever but is not in SPARK and we have
   --     lied about contracts (as in, stated it has no outputs), then
   --     this is not a "new" failure.

   function Get_Expression_Function (E : Entity_Id) return Node_Id
   with Pre  => Is_Expression_Function_Or_Completion (E),
        Post => Nkind (Get_Expression_Function'Result) = N_Expression_Function;
   --  @param E entity of an expression function (or a function declaration
   --     completed by an expression_function)
   --  @return the corresponding N_Expression_Function original node

   function Get_Expr_From_Check_Only_Proc (E : Entity_Id) return Node_Id
   with Pre => Is_DIC_Procedure (E)
                 or else
               Is_Invariant_Procedure (E)
                 or else
               Is_Partial_Invariant_Procedure (E);
   --  @param E a Default_Initial_Condition or Type_Invariant procedure
   --  @return the expression in the first pragma Check found in the body of E,
   --     if any, or Empty otherwise
   --  Extract a condition checked for aspect Default_Initialization and
   --  Type_Invariant.

   function Get_Expr_From_Return_Only_Func (E : Entity_Id) return Node_Id
   with Pre => Is_Predicate_Function (E);
   --  @param E a predicate function
   --  @return the expression in the first return statement found in the body
   --     of E, if any, or Empty otherwise
   --  Extract a condition checked by a function generated for aspect
   --  [Dynamic_]Predicate.

   function Get_Priority_Or_Interrupt_Priority (E : Entity_Id) return Node_Id
   with Pre => Ekind (E) in Protected_Kind |
                            E_Function     |
                            E_Procedure    |
                            E_Task_Type;
   --  @param E the entity of a concurrent type or subprogram
   --  @return The Ada node of the expression for the Priority or
   --  Interrupt_Priority specified on E if any
   --
   --  Note that if pragma Interrupt_Priority with no expression is present
   --  then Empty is returned but it really means Interrupt_Priority'Last.

   function Has_Contracts
     (E         : Entity_Id;
      Name      : Pragma_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Boolean
   with Pre => Ekind (E) in E_Function
                          | E_Package
                          | E_Procedure
                          | Entry_Kind
                          | E_Subprogram_Type
             and then Name in Pragma_Precondition
                            | Pragma_Postcondition
                            | Pragma_Refined_Post
                            | Pragma_Initial_Condition;
   --  @param E subprogram or package
   --  @param Name contract name
   --  @param Classwide True when asking for the classwide version of contract
   --  @param Inherited True when asking only for inherited contracts
   --  @return True iff there is at least one contract Name for E

   function Has_Extensions_Visible (E : Entity_Id) return Boolean
   with Pre =>
       Ekind (E) in E_Function | E_Procedure | Entry_Kind | E_Subprogram_Type;
   --  @param E subprogram
   --  @return True iff Extensions_Visible is specified for E

   function Has_Subprogram_Variant (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Procedure
                          | E_Task_Type;
   --  @param E is a subprogram, entry or task
   --  @return True iff E is annotated with the Subprogram_Variant aspect

   function Has_User_Supplied_Globals (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Function  |
                            E_Procedure |
                            Entry_Kind  |
                            E_Task_Type;
   --  @param E subprogram
   --  @return True iff E has a data dependencies (Global) or flow
   --     dependencies (Depends) contract, or is classified as Pure (either
   --     because of pragma Pure_Function or pragma Pure), which means an
   --     implicit Global => null.

   function Includes_Current_Task (Calls : Node_Sets.Set) return Boolean
   with Pre => (for all Call of Calls => Ekind (Call) in Entry_Kind
                                                       | E_Function
                                                       | E_Package
                                                       | E_Procedure);
   --  @param callable entities
   --  @return True iff Calls include Ada.Task_Identification.Current_Task

   function Is_Function_Type (E : Entity_Id) return Boolean is
     (Ekind (E) = E_Subprogram_Type and then Is_Type (Etype (E)));

   function Is_Borrowing_Traversal_Function (E : Entity_Id) return Boolean;
   --  Return true if E is a borrowing traversal function

   function Is_Error_Signaling_Procedure (E : Entity_Id) return Boolean is
     (No_Return (E)
      and then
      Get_Execution_Kind (E, After_GG => True) = Abnormal_Termination)
    with Pre => not Gnat2Why_Args.Global_Gen_Mode;
   --  @param E any entity
   --  @return True iff E is a procedure annotated with No_Return
   --     and is considered to always terminate abnormally.
   --  Note: this routine is meant to be only used in phase 2

   function Is_Integer_Literal_Aspect_Parameter (E : Entity_Id) return Boolean;
   --  Return True if E is a function associated with the Integer_Literal
   --  aspect of a type.

   function Is_Intrinsic (E : Entity_Id) return Boolean
   is
     (Ekind (E) in E_Function | E_Procedure
      and then Is_Intrinsic_Subprogram (E));
   --  @param E subprogram
   --  @return True iff E is an intrinsic subprogram

   function Is_Local_Subprogram_Always_Inlined (E : Entity_Id) return Boolean;
   --  @param E subprogram
   --  @return True iff E is a local subprogram that is always inlined by the
   --     frontend in GNATprove mode

   function Is_Possibly_Nonreturning_Procedure (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Package
                          | E_Procedure
                          | E_Task_Type,
        Post => (if Is_Possibly_Nonreturning_Procedure'Result
                 then Ekind (E) = E_Procedure);
   --  @param E either a procedure that might have a No_Return or
   --           Might_Not_Return contract, or a program unit that might call
   --           such a procedure
   --  @return True iff E has aspect No_Return or annotation Might_Not_Return

   function Is_Predefined_Potentially_Blocking (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Function | E_Procedure;
   --  @param E subprogram
   --  @return True iff E is a predefined potentially blocking subprogram

   function Is_Requested_Subprogram_Or_Task (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is a subprogram/task whose analysis was specifically
   --     requested, so it should be analyzed even if otherwise inlined

   function Is_Simple_Shift_Or_Rotate (E : Entity_Id) return Boolean;
   --  @param E subprogram
   --  @return True iff Subp is an intrisic shift or rotate for a modular type
   --     of modulus smaller or equal to 2 ** 64, with no functional contract
   --     (precondition, postcondition or contract cases).

   function Is_Traversal_Function (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is a traversal function

   function Is_Unchecked_Deallocation_Instance (E : Entity_Id) return Boolean
   with Pre => Is_Subprogram_Or_Entry (E)
     or else Ekind (E) in E_Task_Type | E_Subprogram_Type;
   --  Return True iff E is an instance of Ada.Unchecked_Deallocation

   procedure Is_Valid_Recursive_Call
     (Call          : Node_Id;
      Analyzed_Unit : Entity_Id;
      Result        : out Boolean;
      Explanation   : out Unbounded_String)
   with Pre => Nkind (Call) in N_Subprogram_Call
                             | N_Entry_Call_Statement
                             | N_Op;
   --  Return True if we are in a case where we support checking progress on
   --  the variants of the called entity.

   function Is_Volatile_For_Internal_Calls (E : Entity_Id) return Boolean
   with Pre => Is_Subprogram (E);
   --  @param E any subprogram
   --  @return True iff E is volatile for internal calls, see SPARK RM 7.1.2

   function Might_Be_Main (E : Entity_Id) return Boolean
   with Pre => Is_Subprogram (E) and then Is_In_Analyzed_Files (E);
   --  @param E subprogram from the current compilation unit (because this
   --     property should be only relevant for subprogram that are analysed
   --     and irrelevant for subprograms that are merely referenced from the
   --     current compilation unit)
   --
   --  @return True iff E is a compilation unit subprogram, has no formal
   --     parameters (E is allowed to have global parameters), and is either a
   --     procedure or a function that returns an integer type
   --
   --  Note: this check is equivalent to rules enforced by GNAT and is more
   --  restrictive than Ada RM (which allows pretty much every subprogram to
   --  be main). See Ada 95 Quality and Style Guide, 7.1.4 for details.

   generic
      with procedure Process (E : Entity_Id; Kind : Formal_Kind);
   procedure Process_Referenced_Entities (E : Entity_Id)
   with Pre => Ekind (E) in E_Function       |
                            E_Package        |
                            E_Procedure      |
                            E_Entry          |
                            E_Task_Type      |
                            E_Protected_Type |
                            E_Subprogram_Type;
   --  Retrieve the set of entities referenced from an entity's spec and body.
   --  It uses flow analysis and ignores entities which are opaque for proof
   --  (abstract states with invisible constituents and entities not in SPARK).

   function Subprogram_Is_Ignored_For_Proof (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Function  |
                            E_Procedure |
                            E_Task_Type |
                            Entry_Kind;
   --  @param E subprogram
   --  @return True iff E should not be translated into Why3

   function Subp_Body_Location (E : Entity_Id) return String
   with Pre => Ekind (E) in Subprogram_Kind |
                            E_Package       |
                            Type_Kind       |
                            Entry_Kind;
   --  @param E subprogram, package, type or entry
   --  @return a String of the form GP_Subp:foo.adb:12 pointing to the file and
   --    line where the body for this entity is declared, or "" if there is
   --    no body. This allows to identify the entity by its source position and
   --    is used e.g. for the --limit-subp switch of GNATprove.

   function Subp_Location (E : Entity_Id) return String
   with Pre => Ekind (E) in Subprogram_Kind |
                            E_Package       |
                            Type_Kind       |
                            Entry_Kind;
   --  @param E subprogram, package, type or entry
   --  @return a String of the form GP_Subp:foo.ads:12 pointing to the file and
   --    line where this entity is declared. This allows to identify the entity
   --    by its source position and is used e.g. for the --limit-subp switch of
   --    GNATprove.

   function Subp_Needs_Invariant_Checks (E : Entity_Id) return Boolean;
   --  @param E subprogram or entry
   --  @return True whenever an invariant check may be needed when calling E
   --          from inside the current compilation unit.

   function Suspends_On_Suspension_Object (E : Entity_Id) return Boolean;
   --  Return True iff E suspends on a suspension object, i.e. it is either
   --  Ada.Synchronous_Task_Control.Suspend_Until_True or
   --  Ada.Synchronous_Task_Control.EDF.Suspend_Until_True_And_Set_Deadline.

   ------------------------------------------------
   --  Queries related to dispatching operations --
   ------------------------------------------------

   function Corresponding_Primitive (Subp, Ty : Entity_Id) return Entity_Id
   with
       Pre  => Is_Dispatching_Operation (Subp)
               and then Present (Find_Dispatching_Type (Subp)),
       Post => Is_Dispatching_Operation (Corresponding_Primitive'Result);
   --  @params Subp a dispatching operation
   --  @params Ty a descendant of the dispatching type of Subp
   --  @return the primitive of Ty that corresponds to Subp

   function Find_Dispatching_Parameter (E : Entity_Id) return Entity_Id with
     Pre  => Ekind (E) = E_Procedure
             and then Is_Dispatching_Operation (E)
             and then Present (Find_Dispatching_Type (E)),
     Post => Present (Find_Dispatching_Parameter'Result);
   --  @param E a dispatching procedure
   --  @return a parameter of E which has the dispatching type

   function Find_Dispatching_Type (E : Entity_Id) return Entity_Id with
     Pre => Is_Dispatching_Operation (E);
   --  @param E a dispatching operation
   --  @return type on which E dispatches. It can return empty if E is not
   --     considered to be dispatching in SPARK, either because the Retysp of
   --     its dispatching type is not tagged or because it is an invisible
   --     dispatching operation.
   --  @param E any entity
   --  @return True if E is a dispatching operation visible in SPARK

   subtype Subprogram_List is Sem_Disp.Subprogram_List;

   package Inheritance_Utilities_Inst is new
     Sem_Disp.Inheritance_Utilities (Find_Dispatching_Type);
   --  The frontend version of Find_Dispatching_Type should not be used as it
   --  does not handle visibility correctly after semantic analysis. Do
   --  instances of frontend inheritance utilities with our own
   --  Find_Dispatching_Type.

   function Inherited_Subprograms
     (S               : Entity_Id;
      No_Interfaces   : Boolean := False;
      Interfaces_Only : Boolean := False;
      One_Only        : Boolean := False) return Subprogram_List renames
     Inheritance_Utilities_Inst.Inherited_Subprograms;

   function Is_Invisible_Dispatching_Operation
     (E : Entity_Id) return Boolean
   with Pre => Is_Dispatching_Operation (E);
   --  @param E subprogram
   --  @return True iff E has is a public operation on a private type whose
   --     public view is not tagged. Hence, Pre'Class and Post'Class cannot be
   --     declared on such a subprogram.

   function Is_Overriding_Subprogram (E : Entity_Id) return Boolean renames
     Inheritance_Utilities_Inst.Is_Overriding_Subprogram;

   --------------------------------
   -- Queries related to entries --
   --------------------------------

   function Entry_Body (E : Entity_Id) return Node_Id
   with Pre  => Ekind (E) in Entry_Kind and then
                Nkind (Parent (E)) = N_Entry_Declaration,
        Post => (if Present (Entry_Body'Result)
                 then Nkind (Entry_Body'Result) = N_Entry_Body);
   --  @param E entry
   --  @return the entry body for the given entry, similar to what
   --    Subprogram_Body might produce.

   function Entry_Body_Entity (E : Entity_Id) return Node_Id
   with Pre  => Ekind (E) in Entry_Kind and then
                Nkind (Parent (E)) = N_Entry_Declaration,
        Post => (if Present (Entry_Body_Entity'Result)
                 then Ekind (Entry_Body_Entity'Result) in Entry_Kind and then
                      Nkind (Parent (Entry_Body_Entity'Result)) =
                        N_Entry_Body);
   --  @param E entry
   --  @return the entry body entity for the given entry

   ---------------------------------
   -- Queries related to packages --
   ---------------------------------

   function In_Private_Declarations (Decl : Node_Id) return Boolean;
   --  @param Decl declaration node
   --  @return True iff Decl belongs to the list of private declarations of a
   --     package.

   function In_Visible_Declarations (Decl : Node_Id) return Boolean;
   --  @param Decl declaration node
   --  @return True iff Decl belongs to the list of visible declarations of a
   --     package.

   function In_Body_Declarations (Decl : Node_Id) return Boolean;
   --  @param Decl declaration node
   --  @return True iff Decl belongs to the list of declarations of a package
   --     body.

end SPARK_Util.Subprograms;
