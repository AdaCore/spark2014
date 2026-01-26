------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2013-2026, Capgemini Engineering              --
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

with Ada.Containers; use Ada.Containers;
with Ada.Containers.Hashed_Maps;

with Aspects;        use Aspects;
with Errout_Wrapper; use Errout_Wrapper;
with Ghost;          use Ghost;
with Namet;          use Namet;
with Nlists;         use Nlists;
with Output;         use Output;
with Rtsfind;        use Rtsfind;
with Sem_Aggr;       use Sem_Aggr;
with Sem_Prag;       use Sem_Prag;
with Sem_Type;       use Sem_Type;
with Sinfo.Utils;    use Sinfo.Utils;
with Sprint;         use Sprint;
with Treepr;         use Treepr;
with Uintp;          use Uintp;

with Common_Iterators;          use Common_Iterators;
with Gnat2Why_Args;
with Gnat2Why.Util;
with SPARK_Definition;          use SPARK_Definition;
with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;
with SPARK_Frame_Conditions;    use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms;    use SPARK_Util.Subprograms;
with SPARK_Util.Types;          use SPARK_Util.Types;
with Why;

with Flow_Classwide;
with Flow_Debug;                      use Flow_Debug;
with Flow_Generated_Globals.Phase_2;  use Flow_Generated_Globals.Phase_2;
with Flow_Refinement;                 use Flow_Refinement;
with Flow_Utility.Initialization;     use Flow_Utility.Initialization;
with Flow_Utility.Proof_Dependencies; use Flow_Utility.Proof_Dependencies;

package body Flow_Utility is

   use type Flow_Id_Sets.Set;

   ----------------------------------------------------------------------
   --  Debug
   ----------------------------------------------------------------------

   Debug_Trace_Get_Global : constant Boolean := False;
   --  Enable this to debug Get_Global.

   Debug_Trace_Flatten : constant Boolean := False;
   --  Enable this for tracing in Flatten_Variable.

   Debug_Trace_Untangle : constant Boolean := False;
   --  Enable this to print the tree and def/use sets in each call of
   --  Untangle_Assignment_Target.

   Debug_Trace_Untangle_Fields : constant Boolean := False;
   --  Enable this to print detailed traces in Untangle_Record_Fields.

   Debug_Trace_Untangle_Record : constant Boolean := False;
   --  Enable this to print traces for Untangle_Record_Assignemnt.

   ----------------------------------------------------------------------
   --  Loop information
   ----------------------------------------------------------------------

   package Loop_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Entity_Id,
        Element_Type    => Flow_Id_Sets.Set,
        Hash            => Node_Hash,
        Equivalent_Keys => "=");

   Loop_Info_Frozen : Boolean := False
   with Ghost;
   Loop_Info        : Loop_Maps.Map := Loop_Maps.Empty_Map;

   ----------------------------------------------------------------------
   --  Local
   ----------------------------------------------------------------------

   function Ancestor (Typ : Entity_Id) return Entity_Id
   with
     Pre  => Is_Type (Typ),
     Post => (if Present (Ancestor'Result) then Is_Type (Ancestor'Result));
   --  Helper function to iterate over a type ancestors. If Typ is a
   --  subtype, then skip the immediate ancestor. If no more ancestors
   --  are present, then return Empty.

   function Unique_Components (E : Entity_Id) return Node_Lists.List
   with
     Pre  => Is_Type (E),
     Post =>
       (for all C of Unique_Components'Result => Is_Unique_Component (C));
   --  Return components in SPARK of the given entity E, similar to
   --  {First,Next}_Component_Or_Discriminant, with the difference that any
   --  components of private ancestors are included.
   --  @param E a type entity
   --  @return all unique components and discriminants of type E that are in
   --    SPARK or the empty list if none exists.

   function First_Name_Node (N : Node_Id) return Node_Id
   with
     Pre  => Nkind (N) in N_Identifier | N_Expanded_Name,
     Post => Nkind (First_Name_Node'Result) = N_Identifier;
   --  Returns the first node that represents a (possibly qualified) entity
   --  name, i.e. for "X" it will be the node of X itself and for "P.X" it will
   --  be the node of P.
   --
   --  This is a helper routine for putting error messages within the Depends,
   --  Refined_Depends and Initializes contract. Note: it is similar to the
   --  Errout.First_Node, but doesn't rely on slocs thus avoids possible
   --  problems with generic instances (as described in Safe_First_Sloc).

   procedure Pick_Generated_Info_Internal
     (N                  : Node_Id;
      Scop               : Flow_Scope;
      Function_Calls     : in out Call_Sets.Set;
      Indirect_Calls     : in out Node_Sets.Set;
      Proof_Dependencies : in out Node_Sets.Set;
      Locks              : in out Protected_Call_Sets.Set;
      Types_Seen         : in out Node_Sets.Set;
      Constants_Seen     : in out Node_Sets.Set;
      Generating_Globals : Boolean)
   with Post => Proof_Dependencies'Old.Is_Subset (Proof_Dependencies);
   --  Like Pick_Generated_Info, with additional parameters Types_Seen and
   --  Constants_Seen that allows to track which type predicates and constant
   --  expressions we already traversed to pick proof dependencies.

   procedure Process_Expression
     (Expr               : Node_Id;
      Scop               : Flow_Scope;
      Proof_Dependencies : in out Node_Sets.Set;
      Types_Seen         : in out Node_Sets.Set;
      Constants_Seen     : in out Node_Sets.Set)
   with Post => Proof_Dependencies'Old.Is_Subset (Proof_Dependencies);
   --  Extract proof dependencies and functions calls from Expr and add
   --  them to Proof_Dependencies.

   function Is_Ancestor
     (Anc : Entity_Id; Ty : Entity_Id; Scope : Flow_Scope) return Boolean;
   --  Return True if Anc is visibly an ancestor of Ty

   function Introduces_Private_Fields
     (Ty : Entity_Id; Anc : Entity_Id; Scope : Flow_Scope) return Boolean
   with Pre => Is_Ancestor (Anc, Ty, Scope);
   --  Return True if Ty has private fields that are not in Anc

   function Component_Visible_In_Type
     (C : Entity_Id; T : Type_Kind_Id; S : Flow_Scope) return Boolean
   is (Is_Visible (C, S)
       and then
         (not Is_Tagged_Type (T) or else Is_Ancestor (Scope (C), T, S)));
   --  C is visible in T if it is visible, and T is visibly derived from C's
   --  scope in S.

   function Get_Specific_Type_From_Classwide
     (E : Class_Wide_Kind_Id; Scop : Flow_Scope) return Type_Kind_Id
   is (Get_Type (Etype (Base_Type (E)), Scop));
   --  Get the specific type from a classwide type

   function Join (A, B : Flow_Id; Offset : Natural := 0) return Flow_Id
   with
     Pre  =>
       A.Kind in Direct_Mapping | Record_Field
       and then B.Kind in Direct_Mapping | Record_Field,
     Post => Join'Result.Facet = B.Facet;
   --  Glues components of B to A, starting at offset. For example
   --  consider A = Obj.X and B = R.X.Y and Offset = 1. Then joining
   --  will return Obj.X.Y.
   --
   --  Similarly, if A = Obj.X and B = R.X'Private_Part and Offset = 1,
   --  then joining will produce Obj.X'Private_Part.

   ----------------------------------------------------------------------
   -- Constants with variable inputs --
   ----------------------------------------------------------------------

   function Has_Variable_Input_Internal (C : Entity_Id) return Boolean
   with Pre => Ekind (C) = E_Constant;
   --  To decide whether a constant has variable inputs we need to traverse its
   --  initialization expression. This involves Get_Variables, which itself
   --  calls Has_Variable_Input to filter "pure" constants. This might cause
   --  repeated traversals of the AST and might be inefficient.
   --
   --  We solve this by deciding the actual result in this routine and
   --  momoizing it in Has_Variable_Input.

   package Entity_To_Boolean_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Entity_Id,
        Element_Type    => Boolean,
        Hash            => Node_Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   Variable_Input_Map : Entity_To_Boolean_Maps.Map;
   --  Map from constants to their memoized property of having variable inputs

   ------------------------
   -- Classwide_Pre_Post --
   ------------------------

   function Classwide_Pre_Post
     (E : Entity_Id; Contract : Pragma_Id) return Node_Lists.List
   is (Find_Contracts
         (E         => E,
          Name      => Contract,
          Classwide => No (Overridden_Operation (E)),
          Inherited => Present (Overridden_Operation (E))))
   with
     Pre =>
       Is_Dispatching_Operation (E)
       and then Contract in Pragma_Precondition | Pragma_Postcondition;
   --  Return the list of the classwide pre- or post-conditions for entity E

   ---------------------
   -- Add_Loop_Writes --
   ---------------------

   procedure Add_Loop_Writes (Loop_E : Entity_Id; Writes : Flow_Id_Sets.Set) is
   begin
      pragma Assert (not Loop_Info_Frozen);
      Loop_Info.Insert (Loop_E, Writes);
   end Add_Loop_Writes;

   --------------
   -- Ancestor --
   --------------

   function Ancestor (Typ : Entity_Id) return Entity_Id is
      Parent_Typ : constant Entity_Id := Etype (Typ);
   begin
      if Ekind (Typ) = E_Record_Subtype then
         return Ancestor (Parent_Typ);
      else
         if Parent_Typ = Typ or else Full_View (Parent_Typ) = Typ then
            return Empty;
         else
            pragma Assert (Present (Parent_Typ));
            return Parent_Typ;
         end if;
      end if;
   end Ancestor;

   ----------------------------------
   -- Pick_Generated_Info_Internal --
   ----------------------------------

   procedure Pick_Generated_Info_Internal
     (N                  : Node_Id;
      Scop               : Flow_Scope;
      Function_Calls     : in out Call_Sets.Set;
      Indirect_Calls     : in out Node_Sets.Set;
      Proof_Dependencies : in out Node_Sets.Set;
      Locks              : in out Protected_Call_Sets.Set;
      Types_Seen         : in out Node_Sets.Set;
      Constants_Seen     : in out Node_Sets.Set;
      Generating_Globals : Boolean)
   is
      function Proc (N : Node_Id) return Traverse_Result;
      --  If the node being processed is an N_Function_Call, store a
      --  corresponding Entity_Id; for protected functions store the
      --  read-locked protected object.

      procedure Process_Constant_Expression (E : Entity_Id)
      with Pre => Ekind (E) = E_Constant;
      --  Pull proof dependencies from the expression of constant E

      procedure Process_Predicate_Expression
        (Type_Instance : Formal_Kind_Id; Pred_Expression : Node_Id);
      --  Merge predicate function for the given type

      procedure Process_Predicates is new
        Iterate_Applicable_Predicates (Process_Predicate_Expression);

      ----------------------------------
      -- Process_Predicate_Expression --
      ----------------------------------

      procedure Process_Predicate_Expression
        (Type_Instance : Formal_Kind_Id; Pred_Expression : Node_Id)
      is
         pragma Unreferenced (Type_Instance);
      begin
         Pick_Generated_Info
           (N                  => Pred_Expression,
            Scop               => Scop,
            Function_Calls     => Function_Calls,
            Indirect_Calls     => Indirect_Calls,
            Proof_Dependencies => Proof_Dependencies,
            Locks              => Locks,
            Generating_Globals => Generating_Globals);
      end Process_Predicate_Expression;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
         P : Node_Id;
      begin
         if Is_Specialized_Actual (N) then
            Function_Calls.Include
              (Subprogram_Call'(N => N, E => Entity (Prefix (N))));
         end if;

         case Nkind (N) is
            when N_Function_Call                            =>
               declare
                  Called_Func : constant Entity_Id := Get_Called_Entity (N);
                  pragma
                    Assert
                      (Ekind (Called_Func) in E_Function | E_Subprogram_Type);

               begin

                  --  Ignore calls to predicate functions and don't descend
                  --  into their predicate expressions.

                  if Ekind (Called_Func) = E_Function
                    and then Is_Predicate_Function (Called_Func)
                  then

                     --  We return OK to traverse the predicate function
                     --  parameter. If we returned Skip, we would ignore the
                     --  call entirely.

                     return OK;

                  --  Likewise for the generated dispatching equality

                  elsif Is_Tagged_Predefined_Eq (Called_Func) then

                     Indirect_Calls.Include (N);
                     return OK;

                  --  Likewise for calls to unchecked conversion, except we
                  --  keep track of the call for proof dependencies.

                  elsif Is_Unchecked_Conversion_Instance (Called_Func) then
                     Proof_Dependencies.Include (Called_Func);
                     return OK;
                  end if;

                  Function_Calls.Include
                    (Subprogram_Call'(N => N, E => Called_Func));

                  if Generating_Globals
                    and then Flow_Classwide.Is_Dispatching_Call (N)
                  then
                     Process_Dispatching_Call (N, Proof_Dependencies);
                  end if;

                  --  Only external calls to protected functions trigger
                  --  priority ceiling protocol checks; internal calls do not.

                  if Generating_Globals
                    and then Ekind (Scope (Called_Func)) = E_Protected_Type
                    and then Is_External_Call (N)
                  then
                     Register_Protected_Call (N, Locks);
                  end if;
               end;

            when N_Membership_Test                          =>
               if Present (Right_Opnd (N)) then
                  --  x in t
                  P := Right_Opnd (N);
                  if Is_Entity_Name (P) and then Is_Type (Entity (P)) then

                     --  The predicate is processed separately for proof
                     --  dependencies because only the predicate on type P
                     --  is executed, whereas proof pulls the entire set of
                     --  predicates that apply to P.

                     Process_Type_Contracts_Internal
                       (Typ                => Etype (P),
                        Scop               => Scop,
                        Include_Invariant  => False,
                        Proof_Dependencies => Proof_Dependencies,
                        Types_Seen         => Types_Seen,
                        Constants_Seen     => Constants_Seen);
                     Process_Predicates (Get_Type (P, Scop));

                  --  If the membership test involves a call to equality, then
                  --  we add N to the set of indirect calls.

                  elsif Alternative_Uses_Eq (P) then
                     Indirect_Calls.Include (N);
                  end if;
               else
                  --  x in t | 1 .. y | u
                  P := First (Alternatives (N));
                  loop
                     if Is_Entity_Name (P) and then Is_Type (Entity (P)) then
                        Process_Type_Contracts_Internal
                          (Typ                => Etype (P),
                           Scop               => Scop,
                           Include_Invariant  => False,
                           Proof_Dependencies => Proof_Dependencies,
                           Types_Seen         => Types_Seen,
                           Constants_Seen     => Constants_Seen);
                        Process_Predicates (Get_Type (P, Scop));
                     elsif Alternative_Uses_Eq (P) then
                        Indirect_Calls.Include (N);
                     end if;
                     Next (P);

                     exit when No (P);
                  end loop;
               end if;

            --  Operator nodes represent calls to intrinsic subprograms, which
            --  we assume to be free from any side effects. We store equality
            --  in the set of indirect calls to include the appropriate
            --  primitives in the call set.

            when N_Op                                       =>

               if Nkind (N) in N_Op_Eq | N_Op_Ne then
                  Indirect_Calls.Include (N);
               else
                  pragma Assert (Is_Intrinsic_Subprogram (Entity (N)));
               end if;

            --  Detect calls via Iterable aspect specification, if present

            when N_Iterator_Specification                   =>
               declare
                  Typ : constant Entity_Id := Etype (Name (N));

                  procedure Process_Iterable_Primitive (Nam : Name_Id);
                  --  Process implicit call to iterable primitive function Nam

                  --------------------------------
                  -- Process_Iterable_Primitive --
                  --------------------------------

                  procedure Process_Iterable_Primitive (Nam : Name_Id) is
                  begin
                     Function_Calls.Include
                       (Subprogram_Call'
                          (N => N,
                           E => Get_Iterable_Type_Primitive (Typ, Nam)));
                  end Process_Iterable_Primitive;

               begin

                  --  At execution, Has_Element (optionally Element),
                  --  First/Next or Last/Previous are called in the expansion
                  --  of the loop.

                  if Has_Aspect (Typ, Aspect_Iterable) then

                     --  Has_Element is called always

                     Process_Iterable_Primitive (Name_Has_Element);

                     --  Element is called when OF keyword is present

                     if Of_Present (N) then
                        Process_Iterable_Primitive (Name_Element);
                     end if;

                     --  First/Next and Last/Previous are called depening on
                     --  the REVERSE keyword.

                     if Reverse_Present (N) then
                        Process_Iterable_Primitive (Name_Last);
                        Process_Iterable_Primitive (Name_Previous);
                     else
                        Process_Iterable_Primitive (Name_First);
                        Process_Iterable_Primitive (Name_Next);
                     end if;

                     Process_Iterable_For_Proof_Annotation
                       (N, Proof_Dependencies);

                  else
                     pragma
                       Assert
                         (Of_Present (N)
                          and then Has_Array_Type (Etype (Name (N)))
                          and then Number_Dimensions (Etype (Name (N))) = 1);
                  end if;
               end;

            --  Predicates applying to entities referenced in the expression
            --  are analyzed to fill Proof_Dependencies.

            when N_Identifier | N_Expanded_Name             =>
               declare
                  E : constant Entity_Id := Entity (N);
               begin
                  if Present (E) and then Ekind (E) in E_Constant | E_Variable
                  then
                     Process_Type_Contracts_Internal
                       (Typ                => Etype (E),
                        Scop               => Scop,
                        Include_Invariant  =>
                          not Scope_Within_Or_Same
                                (Outer => Scop.Ent, Inner => E),
                        Proof_Dependencies => Proof_Dependencies,
                        Types_Seen         => Types_Seen,
                        Constants_Seen     => Constants_Seen);

                     if Generating_Globals and then Ekind (E) = E_Constant then
                        Process_Constant_Expression (E);
                     end if;
                  end if;
               end;

            --  Predicates applying to the target type involved in a type
            --  conversion or qualified expression are analyzed to fill
            --  Proof_Dependencies.

            when N_Type_Conversion | N_Qualified_Expression =>
               Process_Type_Contracts_Internal
                 (Typ                => Etype (N),
                  Scop               => Scop,
                  Include_Invariant  => False,
                  Proof_Dependencies => Proof_Dependencies,
                  Types_Seen         => Types_Seen,
                  Constants_Seen     => Constants_Seen);

            --  Pull subprograms referenced through 'Access in the proof
            --  dependencies.

            when N_Attribute_Reference                      =>
               if Attribute_Name (N) = Name_Access then
                  Process_Access_Attribute (N, Proof_Dependencies);
               end if;

            --  Pull implicit calls and proof dependencies from container
            --  aggregates.

            when N_Aggregate                                =>
               --  Ignore aggregates that are not really subexpressions, e.g.
               --  those occurring inside 'Update attribute reference.

               if Present (Etype (N))
                 and then Sem_Util.Is_Container_Aggregate (N)
               then
                  declare
                     Annot : constant Aggregate_Annotation :=
                       Get_Aggregate_Annotation (Etype (N));

                     procedure Add_Proof_Dependency (E : Entity_Id)
                     with Pre => (if Present (E) then Ekind (E) = E_Function);
                     --  Add proof dependency on E, if it is specified for
                     --  the container type.

                     --------------------------
                     -- Add_Proof_Dependency --
                     --------------------------

                     procedure Add_Proof_Dependency (E : Entity_Id) is
                     begin
                        if Present (E) then
                           Proof_Dependencies.Include (E);
                        end if;
                     end Add_Proof_Dependency;

                  begin
                     if Present (Annot.Empty_Function) then
                        Function_Calls.Include
                          (Subprogram_Call'
                             (N => N, E => Annot.Empty_Function));
                     end if;

                     if Present (Annot.Add_Procedure) then
                        Function_Calls.Include
                          (Subprogram_Call'(N => N, E => Annot.Add_Procedure));
                     end if;

                     Add_Proof_Dependency (Annot.Capacity);

                     case Annot.Kind is
                        when Sets  =>
                           Add_Proof_Dependency (Annot.Contains);
                           Add_Proof_Dependency (Annot.Equivalent_Elements);
                           Add_Proof_Dependency (Annot.Sets_Length);

                        when Maps  =>
                           Add_Proof_Dependency (Annot.Has_Key);
                           Add_Proof_Dependency (Annot.Default_Item);
                           Add_Proof_Dependency (Annot.Equivalent_Keys);
                           Add_Proof_Dependency (Annot.Maps_Length);
                           Add_Proof_Dependency (Annot.Maps_Length);

                        when Seqs  =>
                           Add_Proof_Dependency (Annot.Seqs_Get);
                           Add_Proof_Dependency (Annot.First);
                           Add_Proof_Dependency (Annot.Last);

                        when Model =>
                           Add_Proof_Dependency (Annot.Model);
                     end case;
                  end;
               end if;

            when others                                     =>
               null;
         end case;

         return OK;
      end Proc;

      ---------------------------------
      -- Process_Constant_Expression --
      ---------------------------------

      procedure Process_Constant_Expression (E : Entity_Id) is
         Decl     : constant N_Object_Declaration_Id :=
           Enclosing_Declaration
             (if Is_Partial_View (E) and then Entity_In_SPARK (Full_View (E))
              then Full_View (E)
              else E);
         Expr     : constant Opt_N_Subexpr_Id := Expression (Decl);
         Position : Node_Sets.Cursor;
         Inserted : Boolean;
      begin
         Constants_Seen.Insert (E, Position, Inserted);

         --  Process the expression of E
         if Inserted then
            Process_Expression
              (Expr, Scop, Proof_Dependencies, Types_Seen, Constants_Seen);
         end if;
      end Process_Constant_Expression;

      procedure Traverse is new Traverse_More_Proc (Process => Proc);
      --  AST traversal procedure

      --  Start of processing for Pick_Generated_Info_Internal

   begin
      Traverse (N);
   end Pick_Generated_Info_Internal;

   -------------------------
   -- Pick_Generated_Info --
   -------------------------

   procedure Pick_Generated_Info
     (N                  : Node_Id;
      Scop               : Flow_Scope;
      Function_Calls     : in out Call_Sets.Set;
      Indirect_Calls     : in out Node_Sets.Set;
      Proof_Dependencies : in out Node_Sets.Set;
      Locks              : in out Protected_Call_Sets.Set;
      Generating_Globals : Boolean)
   is
      Types_Unused, Const_Unused : Node_Sets.Set;
   begin
      Pick_Generated_Info_Internal
        (N,
         Scop,
         Function_Calls,
         Indirect_Calls,
         Proof_Dependencies,
         Locks,
         Types_Unused,
         Const_Unused,
         Generating_Globals);
   end Pick_Generated_Info;

   ------------------------
   -- Process_Expression --
   ------------------------

   procedure Process_Expression
     (Expr               : Node_Id;
      Scop               : Flow_Scope;
      Proof_Dependencies : in out Node_Sets.Set;
      Types_Seen         : in out Node_Sets.Set;
      Constants_Seen     : in out Node_Sets.Set)
   is
      Funcalls     : Call_Sets.Set;
      Indcalls     : Node_Sets.Set;
      Unused_Locks : Protected_Call_Sets.Set;
   begin
      Pick_Generated_Info_Internal
        (N                  => Expr,
         Scop               => Scop,
         Function_Calls     => Funcalls,
         Indirect_Calls     => Indcalls,
         Proof_Dependencies => Proof_Dependencies,
         Locks              => Unused_Locks,
         Types_Seen         => Types_Seen,
         Constants_Seen     => Constants_Seen,
         Generating_Globals => True);

      --  Direct function calls in expressions are also treated
      --  as proof dependencies.

      for Call of Funcalls loop

         --  This avoids picking references of an access-to-function in the
         --  case of an access-to-function subtype referencing the result of
         --  said function in its predicate or invariant.
         --
         --  ??? Is it possible to create a proof cycle using enclosing
         --  E_Subprogram_Type entities?

         if Ekind (Call.E) /= E_Subprogram_Type then
            Proof_Dependencies.Include (Call.E);
         end if;
      end loop;
   end Process_Expression;

   -------------------------------------
   -- Process_Type_Contracts_Internal --
   -------------------------------------

   procedure Process_Type_Contracts_Internal
     (Typ                : Type_Kind_Id;
      Scop               : Flow_Scope;
      Include_Invariant  : Boolean;
      Proof_Dependencies : in out Node_Sets.Set;
      Types_Seen         : in out Node_Sets.Set;
      Constants_Seen     : in out Node_Sets.Set)
   is
      procedure Add_Predicates_To_Proof_Deps
        (Type_Instance : Formal_Kind_Id; Pred_Expression : Node_Id)
      with Pre => Nkind (Pred_Expression) in N_Subexpr;
      --  Analyzes the predicate expression to fill Proof_Dependencies

      function Pull_Proof_Dependencies (Typ : Type_Kind_Id) return Test_Result;
      --  Pull proof dependencies from predicates and invariants of type Typ

      procedure Get_Invariant_From_Parents (Typ : Type_Kind_Id);
      --  Traverse the subtype chain of a type to pull proof dependencies
      --  from the invariants of its parent types.

      procedure Get_Predicate_From_Parents is new
        Iterate_Applicable_Predicates (Add_Predicates_To_Proof_Deps);
      --  Traverse the subtype chain of a type to pull proof dependencies
      --  from the predicates of its parent types.

      function Visit_Subcomponents is new
        Traverse_Subcomponents (Pull_Proof_Dependencies);
      --  Traverse a type to pull all proof dependencies related to predicates
      --  and invariants applying to its subcomponents and their parent types.

      ----------------------------------
      -- Add_Predicates_To_Proof_Deps --
      ----------------------------------

      procedure Add_Predicates_To_Proof_Deps
        (Type_Instance : Formal_Kind_Id; Pred_Expression : Node_Id)
      is
         pragma Unreferenced (Type_Instance);
      begin
         Process_Expression
           (Pred_Expression,
            Scop,
            Proof_Dependencies,
            Types_Seen,
            Constants_Seen);
      end Add_Predicates_To_Proof_Deps;

      ---------------------------------
      --  Get_Invariant_From_Parents --
      ---------------------------------

      procedure Get_Invariant_From_Parents (Typ : Type_Kind_Id) is
         Current : Entity_Id := Retysp (Typ);
         Parent  : Entity_Id;
      begin
         loop
            --  Include invariants which are assumed globally or locally in
            --  Scop plus local invariant if Include_Invariant is set.

            if Has_Invariants_In_SPARK (Current)
              and then
                (Invariant_Assumed_In_Main (Current)
                 or else Invariant_Assumed_In_Scope (Current, Scop.Ent)
                 or else Include_Invariant)
            then
               for Expr of
                 Get_Exprs_From_Check_Only_Proc (Invariant_Procedure (Current))
               loop
                  Process_Expression
                    (Expr,
                     Scop,
                     Proof_Dependencies,
                     Types_Seen,
                     Constants_Seen);
               end loop;
            end if;

            --  Explore the subtype chain of the type
            Parent := Retysp (Etype (Current));
            exit when Current = Parent;
            Current := Parent;
         end loop;
      end Get_Invariant_From_Parents;

      -----------------------------
      -- Pull_Proof_Dependencies --
      -----------------------------

      function Pull_Proof_Dependencies (Typ : Type_Kind_Id) return Test_Result
      is
      begin
         Get_Predicate_From_Parents (Typ);
         Get_Invariant_From_Parents (Typ);
         return Continue;
      end Pull_Proof_Dependencies;

      --  Local variables

      Discard  : Boolean;
      Position : Node_Sets.Cursor;
      Inserted : Boolean;

      --  Start of processing for Process_Type_Contracts_Internal

   begin
      --  If we didn't analyze Typ yet, and it is not an access-to-subprogram
      --  type, then we add Typ to Types_Seen and explore it.

      Types_Seen.Insert (Typ, Position, Inserted);

      if Inserted then
         --  Access-to-subprogram types might be annotated with Pre and Post
         --  contracts. We process their expressions for proof dependencies.

         if Is_Access_Subprogram_Type (Typ) and then No (Parent_Retysp (Typ))
         then
            Process_Access_To_Subprogram_Contracts
              (Typ, Scop, Proof_Dependencies, True);
         end if;

         Discard := Visit_Subcomponents (Typ);
      end if;
   end Process_Type_Contracts_Internal;

   ---------------------------------
   -- Called_Primitive_Equalities --
   ---------------------------------

   function Called_Primitive_Equalities
     (Ty : Entity_Id; Force_Predef : Boolean := False) return Node_Sets.Set
   is
      Calls : Node_Sets.Set;

      function Do_Comp (Comp_Ty : Node_Id) return Test_Result;
      --  Include the user-defined equality on Comp_Ty in Calls if it exists
      --  and stop searching. If not, continue the search.

      -------------
      -- Do_Comp --
      -------------

      function Do_Comp (Comp_Ty : Node_Id) return Test_Result is
      begin
         if Is_Access_Type (Comp_Ty) then
            return Fail;

         --  If Comp_Ty does not use the predefined equality, and we don't
         --  force the use of predefined equality on Ty, then we include
         --  the user-defined equality on Comp_Ty and stop searching.

         elsif not Use_Predefined_Equality_For_Type (Comp_Ty)
           and then (not Force_Predef or else Comp_Ty /= Retysp (Ty))
         then
            Calls.Include (Get_User_Defined_Eq (Comp_Ty));
            return Fail;
         else
            return Continue;
         end if;
      end Do_Comp;

      function Do_Components is new Traverse_Subcomponents (Do_Comp);
      --  Explore the subcomponents of type Ty to include all primitive
      --  equalities in Calls.

      Discard : constant Boolean :=
        Do_Components (Ty, Skip_Discr => True, Traverse_Ancestors => True);
   begin
      return Calls;
   end Called_Primitive_Equalities;

   -----------------------
   -- Unique_Components --
   -----------------------

   function Unique_Components (E : Entity_Id) return Node_Lists.List is
   begin
      if Is_Record_Type (E)
        or else Is_Concurrent_Type (E)
        or else Is_Incomplete_Or_Private_Type (E)
        or else Has_Discriminants (E)
      then
         declare
            --  Local variables

            Ptr : Entity_Id;
            T   : Entity_Id := E;
            L   : Node_Lists.List := Node_Lists.Empty_List;
            S   : Node_Sets.Set;

         begin
            loop
               Ptr := First_Component_Or_Discriminant (T);
               while Present (Ptr) loop
                  declare
                     Inserted : Boolean;
                     Unused   : Node_Sets.Cursor;

                  begin
                     if Component_Is_Visible_In_SPARK (Ptr) then
                        S.Insert
                          (New_Item => Unique_Component (Ptr),
                           Position => Unused,
                           Inserted => Inserted);
                        if Inserted then
                           L.Append (Unique_Component (Ptr));
                        end if;
                     end if;
                  end;
                  Next_Component_Or_Discriminant (Ptr);
               end loop;

               T := Ancestor (T);
               exit when No (T);
            end loop;

            return L;
         end;

      --  No components or discriminants to return

      else
         return Node_Lists.Empty_List;
      end if;
   end Unique_Components;

   ----------------------------
   -- Expand_Abstract_States --
   ----------------------------

   function Expand_Abstract_States
     (Vars : Flow_Id_Sets.Set) return Flow_Id_Sets.Set
   is
      Expanded : Flow_Id_Sets.Set;

   begin
      for Var of Vars loop
         Expanded.Union (Expand_Abstract_State (Var));
      end loop;

      return Expanded;
   end Expand_Abstract_States;

   ------------------------
   -- Extensions_Visible --
   ------------------------

   function Extensions_Visible
     (E : Entity_Id; Scope : Flow_Scope) return Boolean
   is
      T : constant Entity_Id := Get_Type (E, Scope);
   begin
      return
        Is_Formal (E)
        and then Is_Tagged_Type (T)
        and then not Is_Class_Wide_Type (T)
        and then Has_Extensions_Visible (Sinfo.Nodes.Scope (E));
   end Extensions_Visible;

   function Extensions_Visible (F : Flow_Id; Scope : Flow_Scope) return Boolean
   is
   begin
      case F.Kind is
         when Direct_Mapping                                    =>
            return Extensions_Visible (Get_Direct_Mapping_Id (F), Scope);

         when Record_Field                                      =>
            --  Record fields themselves cannot be classwide
            return False;

         when Null_Value | Synthetic_Null_Export | Magic_String =>
            --  These are just blobs which we don't know much about, so no
            --  extensions here.
            return False;
      end case;
   end Extensions_Visible;

   --------------------
   -- Get_Components --
   --------------------

   function Get_Components
     (F : Flow_Id; Scope : Flow_Scope) return Flow_Id_Sets.Set is
   begin
      if F.Kind in Direct_Mapping | Record_Field and then F.Facet = Normal_Part
      then
         pragma Annotate (Xcov, Exempt_On, "Debugging code");
         if Debug_Trace_Flatten then
            Write_Str ("Get components: ");
            Print_Flow_Id (F);
         end if;
         pragma Annotate (Xcov, Exempt_Off);

         --  Special-case abstract state, which lack's a type to branch on

         if Ekind (Get_Direct_Mapping_Id (F)) = E_Abstract_State then
            return Flow_Id_Sets.To_Set (F);
         else
            declare
               T : Entity_Id := Get_Type (F, Scope);
               --  Type of F

               Classwide : constant Boolean := Is_Class_Wide_Type (T);
               --  True iff F has a classwide type

               Results : Flow_Id_Sets.Set;

               Contains_Non_Visible : Boolean := False;

               subtype Private_Nonrecord_Kind is Private_Kind
               with
                 Static_Predicate =>
                   Private_Nonrecord_Kind
                   not in E_Record_Type_With_Private
                        | E_Record_Subtype_With_Private;
               --  Non-record private types

               procedure Debug (Msg : String);
               --  Output debug message

               -----------
               -- Debug --
               -----------

               pragma Annotate (Xcov, Exempt_On, "Debugging code");
               procedure Debug (Msg : String) is
               begin
                  if Debug_Trace_Flatten then
                     Write_Line (Msg);
                  end if;
               end Debug;
               pragma Annotate (Xcov, Exempt_Off);

            begin
               pragma Annotate (Xcov, Exempt_On, "Debugging code");
               if Debug_Trace_Flatten then
                  Indent;
               end if;
               pragma Annotate (Xcov, Exempt_Off);

               if Is_Class_Wide_Type (T) then
                  T := Get_Specific_Type_From_Classwide (T, Scope);
               end if;

               pragma Assert (Is_Type (T));

               pragma Annotate (Xcov, Exempt_On, "Debugging code");
               if Debug_Trace_Flatten then
                  Write_Str ("Branching on type: ");
                  Sprint_Node_Inline (T);
                  Write_Line (" (" & Ekind (T)'Img & ")");
               end if;
               pragma Annotate (Xcov, Exempt_Off);

               --  If the type is not in SPARK we return the variable itself

               if not Entity_In_SPARK (T) then
                  return Flow_Id_Sets.To_Set (F);
               end if;

               case Type_Kind'(Ekind (T)) is
                  when Private_Nonrecord_Kind
                  =>
                     Debug ("processing private type");

                     pragma Assert (not Is_Tagged_Type (T));

                     if Has_Discriminants (T) then
                        for C of Unique_Components (T) loop
                           if Is_Visible (C, Scope) then
                              Results.Insert (Add_Component (F, C));
                           else
                              Contains_Non_Visible := True;
                           end if;
                        end loop;
                        Results.Insert ((F with delta Facet => Private_Part));
                     else
                        Results := Flow_Id_Sets.To_Set (F);
                     end if;

                  when Concurrent_Kind
                  =>
                     Debug
                       ("processing "
                        & (case Ekind (T) is
                             when Protected_Kind => "protected",
                             when Task_Kind      => "task",
                             when others         => raise Program_Error)
                        & " type");

                     --  From the inside of a concurrent object include
                     --  discriminants, components and constituents which are a
                     --  Part_Of. From the outside all that we see is the
                     --  object itself.

                     if Nested_Within_Concurrent_Type (T, Scope) then
                        declare
                           C : Entity_Id;
                        begin
                           C := First_Component_Or_Discriminant (T);
                           while Present (C) loop
                              Results.Insert (Add_Component (F, C));
                              Next_Component_Or_Discriminant (C);
                           end loop;
                        end;

                        declare
                           Anon_Obj : constant Entity_Id :=
                             Anonymous_Object (T);
                        begin
                           if Present (Anon_Obj) then
                              for C of Iter (Part_Of_Constituents (Anon_Obj))
                              loop
                                 Results.Insert (Add_Component (F, C));
                              end loop;
                           end if;
                        end;
                     end if;

                     --  Concurrent type represents the "current instance", as
                     --  defined in SPARK RM 6.1.4; they are represented either
                     --  as a collection of discriminants/components/parts_of
                     --  or by a single vertex if that collection would be
                     --  empty (just like null records).

                     if Results.Is_Empty then
                        Results.Insert (F);
                     end if;

                  when Record_Kind
                  =>
                     Debug ("processing record type");

                     --  If T is not visible in Scope, add a private part.
                     --  Ideally, this should never occur.

                     Contains_Non_Visible := not Is_Visible (T, Scope);

                     --  We add each visible component

                     for C of Unique_Components (T) loop

                        if Component_Visible_In_Type (C, T, Scope) then
                           Results.Insert (Add_Component (F, C));
                        else
                           --  We set Contains_Non_Visible to True when the
                           --  type of F has a non null private part.

                           Contains_Non_Visible := True;
                        end if;
                     end loop;

                     --  We iterate over the ancestors of type T to check
                     --  whether it derives from a private type (whose full
                     --  view is potentially not in SPARK, e.g. with private
                     --  extensions for tagged types).

                     declare
                        Typ : Entity_Id := T;
                     begin
                        loop
                           --  We set Contains_Non_Visible to True when the
                           --  ancestor is private and its full view is not
                           --  visible from Scope. This can happen if we derive
                           --  from a private type in the private part where it
                           --  is fully declared.

                           Typ := Get_Type (Base_Type (Typ), Scope);

                           if Is_Private_Type (Typ) then
                              Contains_Non_Visible := True;
                              exit;
                           end if;

                           Typ := Ancestor (Typ);
                           exit when No (Typ);
                        end loop;
                     end;

                     if Contains_Non_Visible then
                        Results.Insert ((F with delta Facet => Private_Part));
                     end if;

                     --  For types which don't have any visible component or
                     --  non null private part, whether or not they are tagged
                     --  or classwide, we add the variable itself.

                     if Results.Is_Empty then
                        Results.Insert (F);
                     end if;

                     if Classwide then
                        --  Ids.Insert ((F with delta Facet => The_Tag)); ???
                        Results.Insert
                          ((F with delta Facet => Extension_Part));
                     end if;

                  when Access_Kind | Array_Kind | Scalar_Kind
                  =>
                     Debug ("processing access or array or scalar type");

                     Results := Flow_Id_Sets.To_Set (F);

                     --  For top-level unconstrained array objects the
                     --  flattened view also includes their bounds.

                     if F.Kind = Direct_Mapping
                       and then Is_Array_Type (T)
                       and then not Is_Constrained (T)
                     then
                        Results.Insert ((F with delta Facet => The_Bounds));
                     end if;

                  when E_Exception_Type | E_Subprogram_Type | Incomplete_Kind
                  =>
                     raise Program_Error;

               end case;

               pragma Annotate (Xcov, Exempt_On, "Debugging code");
               if Debug_Trace_Flatten then
                  Outdent;
               end if;
               pragma Annotate (Xcov, Exempt_Off);

               return Results;
            end;
         end if;
      else
         pragma Annotate (Xcov, Exempt_On, "Debugging code");
         if Debug_Trace_Flatten then
            Write_Str ("Get components: ");
            Print_Flow_Id (F);
         end if;
         pragma Annotate (Xcov, Exempt_Off);

         return Flow_Id_Sets.To_Set (F);
      end if;
   end Get_Components;

   ----------------------
   -- Flatten_Variable --
   ----------------------

   function Flatten_Variable
     (F : Flow_Id; Scope : Flow_Scope) return Flow_Id_Sets.Set
   is
      Subcomponents : Flow_Id_Sets.Set;
      Components    : constant Flow_Id_Sets.Set := Get_Components (F, Scope);

   begin
      --  F is a leaf of the tree representing its type iff its components
      --  contain the F itself. Checking membership instead of set equality
      --  is important, for example because components could also contain
      --  an extension part if F was classwide and didn't have any component.

      if Components.Contains (F) then
         return Components;
      else
         for Component of Components loop
            Subcomponents.Union (Flatten_Variable (Component, Scope));
         end loop;

         return Subcomponents;
      end if;
   end Flatten_Variable;

   ----------------------
   -- Freeze_Loop_Info --
   ----------------------

   procedure Freeze_Loop_Info is
   begin
      pragma Assert (not Loop_Info_Frozen);
      Loop_Info_Frozen := True;
   end Freeze_Loop_Info;

   --------------------------------------
   -- Get_Assignment_Target_Properties --
   --------------------------------------

   procedure Get_Assignment_Target_Properties
     (N                  : Node_Id;
      Scope              : Flow_Scope;
      Partial_Definition : out Boolean;
      View_Conversion    : out Boolean;
      Map_Root           : out Flow_Id;
      Seq                : out Node_Lists.List)
   is
      subtype Interesting_Nodes is Valid_Assignment_Kinds
      with
        Static_Predicate =>
          Interesting_Nodes not in N_Identifier | N_Expanded_Name;

      Root_Node   : Node_Id := N;
      Root_Entity : Entity_Id;
      --  To avoid repeated calls to Entity on the Root_Node

      Root_Overlaid : Boolean;
      --  If the root entity is overlaid, we handle it as a partial assignemt

   begin
      --  First we turn the tree into a more useful sequence. We also determine
      --  the root node which should be an entire variable.

      Seq := Node_Lists.Empty_List;
      while Nkind (Root_Node) in Interesting_Nodes loop
         Seq.Prepend (Root_Node);

         Root_Node :=
           (case Interesting_Nodes (Nkind (Root_Node)) is
              when N_Type_Conversion | N_Unchecked_Type_Conversion =>
                Expression (Root_Node),

              when others                                          =>
                Prefix (Root_Node));
      end loop;

      pragma Assert (Nkind (Root_Node) in N_Identifier | N_Expanded_Name);

      Root_Entity := Entity (Root_Node);
      Root_Overlaid := False;

      if Is_Protected_Component (Root_Entity) then
         Map_Root :=
           Add_Component
             (Direct_Mapping_Id (Sinfo.Nodes.Scope (Root_Entity)),
              Root_Entity);

      elsif Is_Part_Of_Concurrent_Object (Root_Entity) then
         Map_Root :=
           Add_Component
             (Direct_Mapping_Id (Etype (Encapsulating_State (Root_Entity))),
              Root_Entity);

      elsif Ekind (Root_Entity) = E_Variable
        and then Present (Ultimate_Overlaid_Entity (Root_Entity))
      then
         Map_Root :=
           Direct_Mapping_Id (Ultimate_Overlaid_Entity (Root_Entity));

         Root_Overlaid := True;

      else
         Map_Root := Direct_Mapping_Id (Root_Entity);
      end if;

      --  We now work out which variable (or group of variables) is actually
      --  defined, by following the selected components. If we find an array
      --  slice or index we stop and note that we are dealing with a partial
      --  assignment (the defined variable is implicitly used).

      Partial_Definition := False;

      for N of Seq loop
         case Interesting_Nodes (Nkind (N)) is
            when N_Selected_Component                                   =>
               if Root_Overlaid then
                  Partial_Definition := True;
                  exit;
               else
                  declare
                     Field      : constant Entity_Id :=
                       Unique_Component (Entity (Selector_Name (N)));
                     Components : constant Flow_Id_Sets.Set :=
                       Get_Components (Map_Root, Scope);
                     New_Comp   : constant Flow_Id :=
                       Add_Component (Map_Root, Field);
                  begin
                     if Components.Contains (New_Comp) then
                        Map_Root := New_Comp;
                     else
                        --  If Map_Root's type is an ancestor of the type
                        --  declaring Field, then Field is necessarily part of
                        --  the extension. Otherwise, we are in presence of
                        --  invisible private derivations. Assume partial
                        --  definition of the whole object.

                        if Is_Ancestor
                             (Get_Type (Map_Root, Scope),
                              Get_Type (Sinfo.Nodes.Scope (Field), Scope),
                              Scope)
                        then
                           Map_Root :=
                             (Map_Root with delta Facet => Extension_Part);
                        end if;
                        Partial_Definition := True;
                        exit;
                     end if;
                  end;
               end if;

            when N_Type_Conversion | N_Unchecked_Type_Conversion        =>
               null;

            when N_Indexed_Component | N_Slice | N_Explicit_Dereference =>
               Partial_Definition := True;
               exit;
         end case;
      end loop;

      View_Conversion :=
        Nkind (N) = N_Type_Conversion
        and then Is_Tagged_Type (Get_Type (Etype (N), Scope));

      --  On view conversions, if the root type and the ultimately written
      --  types are not visibly descendants of each others we won't be able to
      --  properly track which parts are written.

      if View_Conversion
        and then not Partial_Definition
        and then not Is_Class_Wide_Type (Get_Type (Etype (N), Scope))
      then
         declare
            Old_Ty : constant Entity_Id := Get_Type (Map_Root, Scope);
            New_Ty : constant Entity_Id := Get_Type (Etype (N), Scope);

         begin
            if not Is_Ancestor (Old_Ty, New_Ty, Scope)
              and then not Is_Ancestor (New_Ty, Old_Ty, Scope)
            then
               Partial_Definition := True;
            end if;
         end;
      end if;

      --  Sanity-check: the Map_Root part of the results should be the same as
      --  what would be returned by Path_To_Flow_Id.

      pragma
        Assert (Root_Overlaid or else Map_Root = Path_To_Flow_Id (N, Scope));
   end Get_Assignment_Target_Properties;

   -----------------
   -- Get_Depends --
   -----------------

   procedure Get_Depends
     (Subprogram           : Runnable_Kind_Id;
      Scope                : Flow_Scope;
      Classwide            : Boolean;
      Depends              : out Dependency_Maps.Map;
      Use_Computed_Globals : Boolean := True)
   is
      pragma Unreferenced (Classwide);
      --  For now we assume classwide globals are the same as the actual
      --  globals.

      Depends_N : constant Node_Id :=
        Get_Contract_Node (Subprogram, Scope, Depends_Contract);

      Contract_Relation : constant Dependency_Maps.Map :=
        Parse_Depends (Depends_N);
      --  Step 1: Parse the appropriate dependency relation

      Trimming_Required : constant Boolean :=
        Get_Pragma_Id (Depends_N) = Pragma_Depends
        and then Subprogram_Refinement_Is_Visible (Subprogram, Scope)
        and then Mentions_State_With_Ambiguous_Refinement (Depends_N, Scope);
      --  True iff the down-projected Depends need to be trimmed using
      --  Refined_Global aspect.

      Globals : Global_Flow_Ids;

   begin
      ----------------------------------------------------------------------
      --  Step 2: Expand out any abstract state for which the refinement is
      --  visible, similar to what we do for globals. During this step we also
      --  trim the generated refined depends according to the user-provided
      --  Refined_Global contract.
      ----------------------------------------------------------------------

      --  Initialize Depends map

      Depends := Dependency_Maps.Empty_Map;

      --  Use the Refined_Global to trim the down-projected Depends

      if Trimming_Required then
         pragma
           Assert
             (Present (Find_Contract (Subprogram, Pragma_Depends))
              and then
                No (Find_Contract (Subprogram, Pragma_Refined_Depends)));

         --  Collect all global Proof_Ins, Outputs and Inputs

         Get_Globals
           (Subprogram          => Subprogram,
            Scope               => Scope,
            Classwide           => False,
            Globals             => Globals,
            Use_Deduced_Globals => Use_Computed_Globals,
            Ignore_Depends      => True);

         --  Change all variants to Normal_Use

         Globals :=
           (Proof_Ins => Change_Variant (Globals.Proof_Ins, Normal_Use),
            Inputs    => Change_Variant (Globals.Inputs, Normal_Use),
            Outputs   => Change_Variant (Globals.Outputs, Normal_Use));

         --  Add formal parameters

         for Param of Get_Formals (Subprogram) loop
            declare
               Formal_Param : constant Flow_Id := Direct_Mapping_Id (Param);

            begin
               case Ekind (Param) is
                  when E_In_Parameter                 =>
                     Globals.Inputs.Insert (Formal_Param);
                     Globals.Proof_Ins.Insert (Formal_Param);

                  when E_In_Out_Parameter             =>
                     Globals.Proof_Ins.Insert (Formal_Param);
                     Globals.Inputs.Insert (Formal_Param);
                     Globals.Outputs.Insert (Formal_Param);

                  when E_Out_Parameter                =>
                     Globals.Outputs.Insert (Formal_Param);

                  when E_Protected_Type | E_Task_Type =>
                     Globals.Inputs.Insert (Formal_Param);
                     Globals.Proof_Ins.Insert (Formal_Param);
                     if Ekind (Subprogram) /= E_Function then
                        Globals.Outputs.Insert (Formal_Param);
                     end if;

                  when others                         =>
                     raise Program_Error;
               end case;
            end;
         end loop;

         --  If Subprogram is a function then we need to add it to the
         --  Globals.Writes set so that Subprogram'Result can appear on the LHS
         --  of the Refined_Depends.

         if Ekind (Subprogram) = E_Function then
            Globals.Outputs.Insert (Direct_Mapping_Id (Subprogram));
         end if;

         for C in Contract_Relation.Iterate loop
            declare
               Output : Flow_Id renames Dependency_Maps.Key (C);
               Input  : Flow_Id_Sets.Set renames Contract_Relation (C);

               Refined_Input : constant Flow_Id_Sets.Set :=
                 Down_Project (Input, Scope);

               Trimmed_Output : constant Flow_Id_Sets.Set :=
                 (if Present (Output)
                  then Down_Project (Output, Scope) and Globals.Outputs
                  else Flow_Id_Sets.To_Set (Null_Flow_Id));
               --  If the LHS of a dependency relation is null, then keep it;
               --  otherwise, down-project and trim it.

            begin
               for O of Trimmed_Output loop
                  declare
                     Trimmed_Input : constant Flow_Id_Sets.Set :=
                       Refined_Input.Intersection
                         (if O = Null_Flow_Id
                          then Globals.Proof_Ins
                          else Globals.Inputs);

                  begin
                     Depends.Insert (O, Trimmed_Input);
                  end;
               end loop;
            end;
         end loop;

      --  Simply add the dependencies as they are

      else
         for C in Contract_Relation.Iterate loop
            declare
               D_Out : constant Flow_Id_Sets.Set :=
                 (if Present (Dependency_Maps.Key (C))
                  then Down_Project (Dependency_Maps.Key (C), Scope)
                  else Flow_Id_Sets.To_Set (Null_Flow_Id));

               D_In : constant Flow_Id_Sets.Set :=
                 Down_Project (Contract_Relation (C), Scope);

            begin
               for O of D_Out loop
                  Depends.Insert (O, D_In);
               end loop;
            end;
         end loop;
      end if;

      ----------------------------------------------------------------------
      --  Step 3: We add all Proof_Ins of the [Refined_]Global contract to the
      --  RHS of the "null => RHS" dependence. This is an implicit dependency.
      ----------------------------------------------------------------------

      Get_Globals
        (Subprogram          => Subprogram,
         Scope               => Scope,
         Classwide           => False,
         Globals             => Globals,
         Use_Deduced_Globals => Use_Computed_Globals,
         Ignore_Depends      => True);

      if not Globals.Proof_Ins.Is_Empty then

         --  Create new dependency with "null => Globals.Proof_Ins" or extend
         --  the existing "null => ..." with Globals.Proof_Ins.

         declare
            Position : Dependency_Maps.Cursor;
            Unused   : Boolean;

         begin
            Depends.Insert
              (Key => Null_Flow_Id, Position => Position, Inserted => Unused);

            --  Change variant of Globals.Proof_Ins to Normal_Use

            Depends (Position).Union
              (Change_Variant (Globals.Proof_Ins, Normal_Use));
         end;
      end if;

      ----------------------------------------------------------------------
      --  Step 4: If we are dealing with a task unit T then, as per SPARK RM
      --  6.1.4. in the section Global Aspects, we assume an implicit
      --  specification of T => T. In practice, we add this dependency into
      --  the Depends map in case is not already there.
      ----------------------------------------------------------------------

      if Ekind (Subprogram) = E_Task_Type then
         declare
            Current_Task_Type : constant Flow_Id :=
              Direct_Mapping_Id (Subprogram);

            Position : Dependency_Maps.Cursor;
            Inserted : Boolean;

         begin
            --  Attempt to insert a default, i.e. empty, dependency or do
            --  nothing if Current_Task_Type was already on the LHS.
            Depends.Insert
              (Key      => Current_Task_Type,
               Position => Position,
               Inserted => Inserted);

            --  Extend the dependency with Current_Task_Type or do nothing if
            --  if was already on the RHS.
            Depends (Position).Include (Current_Task_Type);
         end;
      end if;

      for RHS of Depends loop
         Map_Generic_In_Formals (Scope, RHS);
      end loop;

   end Get_Depends;

   -----------------
   -- Get_Flow_Id --
   -----------------

   function Get_Flow_Id
     (Name : Entity_Name; View : Flow_Id_Variant := Normal_Use) return Flow_Id
   is
      E : constant Entity_Id := Find_Entity (Name);
   begin
      if Present (E) then
         --  We found an entity, now we make some effort to canonicalize
         return Direct_Mapping_Id (E, View);
      else
         --  If Entity_Id is not known then fall back to the magic string
         return Magic_String_Id (Name, View);
      end if;
   end Get_Flow_Id;

   -------------------
   -- Get_Functions --
   -------------------

   function Get_Functions
     (N : Node_Id; Include_Predicates : Boolean) return Node_Sets.Set
   is
      Funcalls     : Call_Sets.Set;
      Indcalls     : Node_Sets.Set;
      Proofdeps    : Node_Sets.Set;
      Unused_Locks : Protected_Call_Sets.Set;
   begin
      Pick_Generated_Info
        (N,
         Scop               => Get_Flow_Scope (N), --  ??? could be parameter
         Function_Calls     => Funcalls,
         Indirect_Calls     => Indcalls,
         Proof_Dependencies => Proofdeps,
         Locks              => Unused_Locks,
         Generating_Globals => Include_Predicates);
      return To_Subprograms (Funcalls);
   end Get_Functions;

   ---------------------------
   -- Parse_Global_Contract --
   ---------------------------

   function Parse_Global_Contract
     (Subprogram : Entity_Id; Global_Node : Node_Id) return Raw_Global_Nodes
   is
      Globals : Raw_Global_Nodes;

      subtype Global_Name_Id is Name_Id
      with
        Static_Predicate =>
          Global_Name_Id
          in Name_Input | Name_In_Out | Name_Output | Name_Proof_In;

      procedure Process (The_Mode : Global_Name_Id; The_Global : Entity_Id);
      --  Add the given global to Reads, Writes or Proof_Ins, depending
      --  on the mode.

      -------------
      -- Process --
      -------------

      procedure Process (The_Mode : Global_Name_Id; The_Global : Entity_Id) is
         E : constant Entity_Id := Canonical_Entity (The_Global, Subprogram);

      begin
         case The_Mode is
            when Name_Input    =>
               if not Is_Generic_Actual_Without_Variable_Input (E) then
                  Globals.Inputs.Insert (E);
               end if;

            when Name_In_Out   =>
               Globals.Inputs.Insert (E);
               Globals.Outputs.Insert (E);

            when Name_Output   =>
               Globals.Outputs.Insert (E);

            when Name_Proof_In =>
               if not Is_Generic_Actual_Without_Variable_Input (E) then
                  Globals.Proof_Ins.Insert (E);
               end if;
         end case;
      end Process;

      --  Local variables

      pragma
        Assert (List_Length (Pragma_Argument_Associations (Global_Node)) = 1);

      PAA : constant Node_Id :=
        First (Pragma_Argument_Associations (Global_Node));
      pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

      --  Start of processing for Parse_Global_Contract

   begin
      if Nkind (Expression (PAA)) = N_Null then
         --  global => null
         --  No globals, nothing to do.
         null;

      elsif Nkind (Expression (PAA)) = N_Aggregate
        and then Present (Expressions (Expression (PAA)))
      then
         --  global => foo
         --  global => (foo, bar)
         --  One or more inputs

         declare
            RHS : Node_Id := First (Expressions (Expression (PAA)));

         begin
            loop
               pragma Assert (Nkind (RHS) in N_Identifier | N_Expanded_Name);

               Process (Name_Input, Entity (RHS));

               Next (RHS);

               exit when No (RHS);
            end loop;
         end;

      elsif Nkind (Expression (PAA)) = N_Aggregate
        and then Present (Component_Associations (Expression (PAA)))
      then
         --  global => (mode => foo,
         --             mode => (bar, baz))
         --  A mixture of things.

         declare
            Row : Node_Id := First (Component_Associations (Expression (PAA)));

         begin
            loop
               pragma Assert (List_Length (Choices (Row)) = 1);

               declare
                  Mode : Name_Id renames Chars (First (Choices (Row)));
                  RHS  : Node_Id renames Expression (Row);

               begin
                  case Nkind (RHS) is
                     when N_Null                         =>
                        null;

                     when N_Identifier | N_Expanded_Name =>
                        Process (Mode, Entity (RHS));

                     when N_Aggregate                    =>
                        declare
                           Item : Node_Id := First (Expressions (RHS));

                        begin
                           loop
                              pragma
                                Assert
                                  (Nkind (Item)
                                   in N_Identifier | N_Expanded_Name);

                              Process (Mode, Entity (Item));

                              Next (Item);

                              exit when No (Item);
                           end loop;
                        end;

                     when others                         =>
                        raise Program_Error;

                  end case;
               end;

               Next (Row);

               exit when No (Row);
            end loop;
         end;

      else
         raise Program_Error;
      end if;

      return Globals;

   end Parse_Global_Contract;

   ----------------------------
   -- Map_Generic_In_Formals --
   ----------------------------

   procedure Map_Generic_In_Formals
     (Scop    : Flow_Scope;
      Objects : in out Flow_Id_Sets.Set;
      Entire  : Boolean := True)
   is
      Mapped : Flow_Id_Sets.Set;

   begin
      --  Iterate over Objects and either map them into anything referenced
      --  in their generic actual parameter expression or keep as they are.

      for Object of Objects loop
         case Object.Kind is
            when Direct_Mapping | Record_Field =>
               declare
                  E : constant Entity_Id := Get_Direct_Mapping_Id (Object);

               begin
                  if Ekind (E) = E_Constant and then In_Generic_Actual (E) then
                     if Scope_Within_Or_Same
                          (Inner => Scop.Ent, Outer => Scope (E))
                     then
                        Mapped.Include (Object);
                     else
                        declare
                           Inputs : constant Flow_Id_Sets.Set :=
                             Get_Variables
                               (Expression (Declaration_Node (E)),
                                Scope                => Scop,
                                Target_Name          => Null_Flow_Id,
                                Fold_Functions       => Flow_Types.Inputs,
                                Use_Computed_Globals => False);

                        begin
                           --  Retain the variant of the original Object, which
                           --  is either In_View for those coming from
                           --  Get_Global or Normal_Use for those coming from
                           --  other contexts.

                           if Entire then
                              Mapped.Union
                                (Change_Variant
                                   (To_Entire_Variables (Inputs),
                                    Object.Variant));
                           else
                              Mapped.Union (Inputs);
                           end if;
                        end;
                     end if;
                  else
                     Mapped.Include (Object);
                  end if;
               end;

            when Magic_String                  =>
               Mapped.Include (Object);

            when others                        =>
               raise Program_Error;
         end case;
      end loop;

      Flow_Id_Sets.Move (Target => Objects, Source => Mapped);
   end Map_Generic_In_Formals;

   -----------------
   -- Get_Globals --
   -----------------

   procedure Get_Globals
     (Subprogram          : Runnable_Kind_Id;
      Scope               : Flow_Scope;
      Classwide           : Boolean;
      Globals             : out Global_Flow_Ids;
      Use_Deduced_Globals : Boolean := True;
      Ignore_Depends      : Boolean := False)
   is
      Global_Node  : constant Node_Id :=
        Get_Contract_Node (Subprogram, Scope, Global_Contract);
      Depends_Node : constant Node_Id :=
        Get_Contract_Node (Subprogram, Scope, Depends_Contract);

      Use_Generated_Globals : constant Boolean :=
        Rely_On_Generated_Global (Subprogram, Scope);

      procedure Debug (Msg : String);
      --  Write message Msg to debug output

      procedure Debug (Label : String; S : Flow_Id_Sets.Set);
      --  Write Label followed by elements of S to debug output

      -----------
      -- Debug --
      -----------

      pragma Annotate (Xcov, Exempt_On, "Debugging code");

      procedure Debug (Msg : String) is
      begin
         if Debug_Trace_Get_Global then
            Indent;
            Write_Line (Msg);
            Outdent;
         end if;
      end Debug;

      procedure Debug (Label : String; S : Flow_Id_Sets.Set) is
      begin
         if Debug_Trace_Get_Global then
            Write_Line (Label);
            Indent;
            for F of S loop
               Sprint_Flow_Id (F);
               Write_Eol;
            end loop;
            Outdent;
         end if;
      end Debug;

      pragma Annotate (Xcov, Exempt_Off);

      --  Start of processing for Get_Globals

   begin
      Globals.Proof_Ins := Flow_Id_Sets.Empty_Set;
      Globals.Inputs := Flow_Id_Sets.Empty_Set;
      Globals.Outputs := Flow_Id_Sets.Empty_Set;

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Debug_Trace_Get_Global then
         Write_Str ("Get_Global (");
         Sprint_Node (Subprogram);
         Write_Str (", ");
         Print_Flow_Scope (Scope);
         Write_Line (")");
      end if;
      pragma Annotate (Xcov, Exempt_Off);

      if Present (Global_Node) and then not Use_Generated_Globals then
         Debug ("using user annotation");

         declare
            ---------------------------------------------------------------
            --  Step 1: Process global annotation
            ---------------------------------------------------------------

            Raw_Globals : constant Raw_Global_Nodes :=
              Parse_Global_Contract
                (Subprogram => Subprogram, Global_Node => Global_Node);

         begin
            ---------------------------------------------------------------
            --  Step 2: Expand any abstract state that might be too refined for
            --  our given scope; also, convert to Flow_Ids in preparation for
            --  the next step, where objects only known by Magic_String might
            --  appear.
            ---------------------------------------------------------------

            Globals :=
              (Proof_Ins =>
                 To_Flow_Id_Set
                   (Down_Project (Raw_Globals.Proof_Ins, Scope), In_View),
               Inputs    =>
                 To_Flow_Id_Set
                   (Down_Project (Raw_Globals.Inputs, Scope), In_View),
               Outputs   =>
                 To_Flow_Id_Set
                   (Down_Project (Raw_Globals.Outputs, Scope), Out_View));

            ---------------------------------------------------------------
            --  Step 3: If this query refers to Global of a subprogram that is
            --  inside of a generic instance, then substitute generic actuals
            --  of mode IN in that contract with objects referenced in their
            --  corresponding generic actual parameter expressions.
            ---------------------------------------------------------------

            Map_Generic_In_Formals (Scope, Globals.Proof_Ins);
            Map_Generic_In_Formals (Scope, Globals.Inputs);

            ---------------------------------------------------------------
            --  Step 4: Trim constituents based on the Refined_Depends.
            --  Only the Inputs are trimmed. Proof_Ins cannot be trimmed
            --  since they do not appear in Refined_Depends and Outputs
            --  cannot be trimmed since all constituents have to be
            --  present in the Refined_Depends.
            --
            --  ??? quite likely trimming should happen before mapping the
            --  generic IN formal parameters; but the mapping happens in
            --  Get_Depends too, so at least now we operate on the same view,
            --  i.e. only on objects visible from the outside of generic.
            ---------------------------------------------------------------

            --  Check if the projected Global constituents need to be
            --  trimmed (based on a user-provided Refined_Depends aspect).
            if not Ignore_Depends
              and then Present (Depends_Node)
              and then Pragma_Name (Global_Node) = Name_Global
              and then Pragma_Name (Depends_Node) = Name_Refined_Depends
              and then
                Mentions_State_With_Ambiguous_Refinement (Global_Node, Scope)
            then
               declare
                  D_Map          : Dependency_Maps.Map;
                  Refined_Inputs : Flow_Id_Sets.Set;

               begin
                  --  Read the Refined_Depends aspect
                  Get_Depends
                    (Subprogram           => Subprogram,
                     Scope                => Scope,
                     Classwide            => Classwide,
                     Depends              => D_Map,
                     Use_Computed_Globals => Use_Deduced_Globals);

                  --  Gather all inputs
                  for RHS of D_Map loop
                     Refined_Inputs.Union (RHS);
                  end loop;

                  --  Do the trimming
                  Globals.Inputs.Intersection
                    (Change_Variant (Refined_Inputs, In_View));
               end;
            end if;

         end;

         Debug ("proof ins", Globals.Proof_Ins);
         Debug ("reads", Globals.Inputs);
         Debug ("writes", Globals.Outputs);

      --  If we have no Global, but we do have a depends, we can
      --  reverse-engineer the Global. This also solves the issue where the
      --  (computed) global is inconsistent with the depends. (See M807-032
      --  for an example.)

      elsif Present (Depends_Node)
        and then not Use_Generated_Globals
        and then not Ignore_Depends
      then
         declare
            D_Map  : Dependency_Maps.Map;
            Params : constant Node_Sets.Set := Get_Formals (Subprogram);
            --  We need to make sure not to include our own parameters in the
            --  globals we produce here. Note that the formal parameters that
            --  we collect here will also include implicit formal parameters of
            --  subprograms that belong to concurrent types.

         begin
            Debug ("reversing depends annotation");

            Get_Depends
              (Subprogram           => Subprogram,
               Scope                => Scope,
               Classwide            => Classwide,
               Depends              => D_Map,
               Use_Computed_Globals => Use_Deduced_Globals);

            --  Always OK to call direct_mapping here since you can't refer
            --  to hidden state in user-written depends contracts.

            for C in D_Map.Iterate loop
               declare
                  Output : Flow_Id renames Dependency_Maps.Key (C);
                  Inputs : Flow_Id_Sets.Set renames D_Map (C);
               begin
                  --  Filter function'Result and parameters
                  if Present (Output) then
                     declare
                        E : constant Entity_Id :=
                          Get_Direct_Mapping_Id (Output);
                     begin
                        if E /= Subprogram and then not Params.Contains (E)
                        then
                           Globals.Outputs.Include
                             (Change_Variant (Output, Out_View));
                        end if;
                     end;
                  end if;

                  for Input of Inputs loop
                     pragma
                       Assert
                         (Input.Kind
                          in Null_Value | Magic_String | Direct_Mapping);
                     --  Unlike Output, which is either a Null_Value or a
                     --  Direct_Mapping, Input might be also a Magic_String,
                     --  when an extra "null => proof_in" dependency is added
                     --  from a generated Refined_Global.

                     if Input.Kind = Magic_String
                       or else
                         (Input.Kind = Direct_Mapping
                          and then
                            not Params.Contains
                                  (Get_Direct_Mapping_Id (Input)))
                     then
                        Globals.Inputs.Include
                          (Change_Variant (Input, In_View));

                        --  A volatile with effective reads is always an output
                        --  as well (this should be recorded in the depends,
                        --  but the front-end does not enforce this).
                        if Has_Effective_Reads (Input) then
                           Globals.Outputs.Include
                             (Change_Variant (Input, Out_View));
                        end if;
                     end if;
                  end loop;
               end;
            end loop;

            Debug ("reads", Globals.Inputs);
            Debug ("writes", Globals.Outputs);
         end;

      --  Assume abstract subprograms to be pure, because currently they can't
      --  be annotated with Global/Depends contracts.

      elsif Is_Overloadable (Subprogram)
        and then Is_Abstract_Subprogram (Subprogram)
      then

         Debug ("giving null globals for an abstract entity");

      --  SPARK RM 6.1.4(4):
      --
      --  "If a subprogram's Global aspect is not otherwise specified and
      --  either:
      --
      --    * the subprogram is a library-level subprogram declared in a
      --      library unit that is declared pure (i.e., a subprogram to which
      --      the implementation permissions of Ada RM 10.2.1 apply); or
      --
      --    * a Pure_Function pragma applies to the subprogram
      --
      --  then a Global aspect of null is implicitly specified for the
      --  subprogram."
      --
      --  The frontend flag Is_Pure is set on exactly on those subprograms that
      --  are specified in the SPARM RM rule.

      elsif Is_Pure (Subprogram) then

         Debug ("giving null globals for a pure entity");

      elsif Use_Deduced_Globals then

         --  We don't have a global or a depends aspect so we look at the
         --  generated globals.

         Debug ("using generated globals");

         GG_Get_Globals (Subprogram, Scope, Globals);

      --  We don't have user globals and we're not allowed to use computed
      --  globals (i.e. we're trying to compute globals).

      else
         Debug ("defaulting to null globals");

      end if;
   end Get_Globals;

   ---------------------
   -- Get_Loop_Writes --
   ---------------------

   function Get_Loop_Writes (E : Entity_Id) return Flow_Id_Sets.Set
   renames Loop_Info.Element;

   ------------------------------------
   --  Get_Outputs_From_Program_Exit --
   ------------------------------------

   function Get_Outputs_From_Program_Exit
     (E : Entity_Id; Scope : Flow_Scope; Use_Computed_Globals : Boolean)
      return Flow_Id_Sets.Set
   is
      Prag : constant Node_Id := Get_Pragma (E, Pragma_Program_Exit);

   begin
      if Present (Prag) then
         declare
            Assoc : constant List_Id := Pragma_Argument_Associations (Prag);

            pragma Assert (No (Assoc) or else List_Length (Assoc) = 1);
            --  Pragma has one optional argument

         begin
            --  Collect variables read in the expression.

            if Present (Assoc) then
               return
                 Get_All_Variables
                   (Expression (First (Assoc)),
                    Scope                => Scope,
                    Target_Name          => Null_Flow_Id,
                    Use_Computed_Globals => Use_Computed_Globals,
                    Skip_Old             => True);
            end if;
         end;
      end if;

      return Flow_Id_Sets.Empty_Set;
   end Get_Outputs_From_Program_Exit;

   -----------------------------------
   -- Get_Outputs_From_Program_Exit --
   -----------------------------------

   function Get_Outputs_From_Program_Exit
     (E : Entity_Id; Scop : Node_Id) return Flow_Id_Sets.Set
   is
      Prag : constant Node_Id := Get_Pragma (E, Pragma_Program_Exit);
      Res  : Flow_Id_Sets.Set;

   begin
      if No (Prag) then
         return Res;
      end if;

      declare
         Assoc         : constant List_Id :=
           Pragma_Argument_Associations (Prag);
         pragma Assert (No (Assoc) or else List_Length (Assoc) = 1);
         Post          : Node_Id;
         Reads, Writes : Flow_Id_Sets.Set;

      begin
         if No (Assoc) then
            return Res;
         end if;

         Post := Expression (First (Assoc));

         --  Collect all variables read in Post (except under 'Old)

         Res.Union (Get_Variables_For_Proof (Post, Scop, Skip_Old => True));

         --  Only keep E's outputs

         Get_Proof_Globals
           (Subprogram      => E,
            Reads           => Reads,
            Writes          => Writes,
            Erase_Constants => True,
            Scop            => Get_Flow_Scope (Scop));

         --  Include the protected type for procedures and entries declared
         --  directly within protected types. They are handled in flow as if
         --  they had an implicit self parameter of mode in out.

         if Present (Scope (E))
           and then Ekind (Scope (E)) = E_Protected_Type
           and then Ekind (E) in E_Procedure | E_Entry
         then
            Writes.Include (Direct_Mapping_Id (Scope (E)));
         end if;

         Res.Intersection (Writes);
      end;

      return Res;
   end Get_Outputs_From_Program_Exit;

   -----------------------------------
   -- Get_Postcondition_Expressions --
   -----------------------------------

   function Get_Postcondition_Expressions
     (E : Entity_Id; Refined : Boolean) return Node_Lists.List
   is
      P_Expr : Node_Lists.List;
      P_CC   : Node_Lists.List;
   begin
      case Ekind (E) is
         when Entry_Kind | E_Function | E_Procedure | E_Subprogram_Type =>
            if Refined then
               P_Expr := Find_Contracts (E, Pragma_Refined_Post);
            else
               P_Expr := Find_Contracts (E, Pragma_Postcondition);
               P_CC := Find_Contracts (E, Pragma_Contract_Cases);

               if Is_Dispatching_Operation (E) then
                  for Post of Classwide_Pre_Post (E, Pragma_Postcondition) loop
                     P_Expr.Append (Post);
                  end loop;
               end if;

               --  If a Contract_Cases aspect was found then we pull out
               --  every right-hand-side.
               for Aggr of P_CC loop
                  declare
                     Contract_Case : Node_Id :=
                       First (Component_Associations (Aggr));
                  begin
                     loop
                        P_Expr.Append (Expression (Contract_Case));
                        Next (Contract_Case);

                        exit when No (Contract_Case);
                     end loop;
                  end;
               end loop;
            end if;

         when E_Package                                                 =>
            if Refined then
               P_Expr := Node_Lists.Empty_List;
            else
               P_Expr := Find_Contracts (E, Pragma_Initial_Condition);
            end if;

         when others                                                    =>
            raise Program_Error;

      end case;

      return P_Expr;
   end Get_Postcondition_Expressions;

   ----------------------------------
   -- Get_Precondition_Expressions --
   ----------------------------------

   function Get_Precondition_Expressions (E : Entity_Id) return Node_Lists.List
   is
      Precondition_Expressions : Node_Lists.List :=
        Find_Contracts (E, Pragma_Precondition);

      Contract_Cases     : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Contract_Cases);
      Subprogram_Variant : constant Node_Id :=
        Get_Pragma (E, Pragma_Subprogram_Variant);
      Exit_Cases         : constant Node_Id :=
        Get_Pragma (E, Pragma_Exit_Cases);

   begin
      if Is_Dispatching_Operation (E) then
         for Pre of Classwide_Pre_Post (E, Pragma_Precondition) loop
            Precondition_Expressions.Append (Pre);
         end loop;
      end if;

      --  If a Contract_Cases aspect was found then we pull every condition
      --  apart from the others.

      for Aggr of Contract_Cases loop
         declare
            Contract_Case : Node_Id := First (Component_Associations (Aggr));
            Case_Guard    : Node_Id;

         begin
            loop
               Case_Guard := First (Choices (Contract_Case));

               if Nkind (Case_Guard) /= N_Others_Choice then
                  Precondition_Expressions.Append (Case_Guard);
               end if;

               Next (Contract_Case);

               exit when No (Contract_Case);
            end loop;
         end;
      end loop;

      --  If a Subprogram_Variant aspect was found then we add every
      --  expression to the returned list. Subprogram variants are treated
      --  as preconditions because they are read at the program entry.
      if Present (Subprogram_Variant) then
         declare
            Aggr : constant Node_Id :=
              Expression
                (First (Pragma_Argument_Associations (Subprogram_Variant)));

            Variant : Node_Id := First (Component_Associations (Aggr));
         begin
            loop
               Precondition_Expressions.Append (Expression (Variant));
               Next (Variant);

               exit when No (Variant);
            end loop;
         end;
      end if;

      --  If a Exit_Cases aspect was found then we pull every condition apart
      --  from the others.

      if Present (Exit_Cases) then
         declare
            Exit_Case : Node_Id :=
              First
                (Component_Associations
                   (Expression
                      (First (Pragma_Argument_Associations (Exit_Cases)))));

            Case_Guard : Node_Id;

         begin
            loop
               Case_Guard := First (Choices (Exit_Case));

               if Nkind (Case_Guard) /= N_Others_Choice then
                  Precondition_Expressions.Append (Case_Guard);
               end if;

               Next (Exit_Case);

               exit when No (Exit_Case);
            end loop;
         end;
      end if;

      return Precondition_Expressions;

   end Get_Precondition_Expressions;

   -----------------------
   -- Get_Proof_Globals --
   -----------------------

   procedure Get_Proof_Globals
     (Subprogram      : Runnable_Kind_Id;
      Reads           : out Flow_Id_Sets.Set;
      Writes          : out Flow_Id_Sets.Set;
      Erase_Constants : Boolean;
      Scop            : Flow_Scope := Null_Flow_Scope)
   is

      function Only_Mutable
        (Objects : Flow_Id_Sets.Set) return Flow_Id_Sets.Set
      with
        Pre  => Erase_Constants,
        Post =>
          Flow_Id_Sets.Is_Subset
            (Subset => Only_Mutable'Result, Of_Set => Objects);
      --  Returns those of Objects that are mutable in Why3

      ------------------
      -- Only_Mutable --
      ------------------

      function Only_Mutable
        (Objects : Flow_Id_Sets.Set) return Flow_Id_Sets.Set
      is
         Mutable : Flow_Id_Sets.Set;

      begin
         for Object of Objects loop
            if Object.Kind = Direct_Mapping then
               --  Entities translated as constants in Why3 should not
               --  be considered as effects for proof. This includes,
               --  in particular, formal parameters of mode IN.

               --  Otherwise the effect is significant for proof, keep it

               if Gnat2Why.Util.Is_Mutable_In_Why
                    (Get_Direct_Mapping_Id (Object))
               then
                  Mutable.Insert (Object);
               end if;

            --  ??? Entities not in SPARK are represented as Magic_String;
            --  for now, consider them as mutable. The only other objects
            --  represented as Magic_String are abstract, which are always
            --  mutable.

            else
               pragma Assert (Object.Kind = Magic_String);
               Mutable.Insert (Object);
            end if;
         end loop;

         return Mutable;
      end Only_Mutable;

      E : Entity_Id;
      --  The entity whose Global contract will be queried from the flow
      --  analysis; typically this is the same as Subprogram, except for
      --  derived task types, which can't have a Global contracts (so flow
      --  analysis do not provide it). For them, proof expects the Global
      --  contract of the root type (which should also be a task type and also
      --  be in SPARK).

      Globals : Global_Flow_Ids;
      Scope   : Flow_Scope;

      --  Start of processing for Get_Proof_Globals

   begin
      --  We currently have no way to annotate subprogram types with globals,
      --  assume that they have none.

      if Ekind (Subprogram) = E_Subprogram_Type then
         return;
      end if;

      if Is_Derived_Type (Subprogram) then
         E := Root_Type (Subprogram);

         if Is_Private_Type (E) then
            E := Full_View (E);
            pragma Assert (Present (E));
         end if;

         pragma
           Assert
             (Ekind (E) = E_Task_Type
              and then not Is_Derived_Type (E)
              and then Entity_In_SPARK (E));
      else
         E := Subprogram;
      end if;

      --  For predicate functions we generate globals on the fly as any objects
      --  referenced in the predicate expression (except for the predicate type
      --  itself, which is represented by the formal parameter of a predicate
      --  function).

      if Ekind (E) = E_Function and then Is_Predicate_Function (E) then
         declare
            Param : constant Entity_Id := First_Formal (E);

         begin
            for V of
              Get_Variables_For_Proof
                (Expr_N => Get_Expr_From_Return_Only_Func (E), Scope_N => E)
            loop
               if V.Kind = Direct_Mapping and then V.Node = Param then
                  null;
               else
                  Reads.Include (V);
               end if;
            end loop;
         end;

         Writes := Flow_Id_Sets.Empty_Set;

      elsif Is_Tagged_Predefined_Eq (E) then
         null;

      --  Otherwise, we rely on the flow analysis

      else

         --  If explicit visibility scope is provided, then use it; for
         --  access-to-subprograms use the visibility of their declaration;
         --  otherwise use "the most precise globals" that make sense,
         --  i.e. Refined_Global if subprogram body is in SPARK and
         --  Global otherwise.

         Scope :=
           (if Present (Scop)
            then Scop
            else
              (Ent  => E,
               Part =>
                 (if Entity_Body_In_SPARK (E)
                  then Body_Part
                  else Visible_Part)));

         Get_Globals
           (Subprogram          => E,
            Scope               => Scope,
            Classwide           => True,
            Globals             => Globals,
            Use_Deduced_Globals => True);

         --  Expand all variables; it is more efficent to process Proof_Ins and
         --  Reads separaterly, because they are disjoint and there is no point
         --  in computing their union.
         Reads :=
           Flow_Id_Sets.Union
             (Expand_Abstract_States (Globals.Proof_Ins),
              Expand_Abstract_States (Globals.Inputs));

         Writes := Expand_Abstract_States (Globals.Outputs);
      end if;

      if Erase_Constants then
         Reads := Only_Mutable (Reads);
         Writes := Only_Mutable (Writes);
      end if;
   end Get_Proof_Globals;

   --------------
   -- Get_Type --
   --------------

   function Get_Type (F : Flow_Id; Scope : Flow_Scope) return Entity_Id is
      E : constant Entity_Id :=
        (case F.Kind is
           when Direct_Mapping => Get_Direct_Mapping_Id (F),
           when Record_Field   => F.Component.Last_Element,
           when others         => raise Program_Error);
   begin
      return Get_Type (E, Scope);
   end Get_Type;

   function Get_Type (N : Node_Id; Scope : Flow_Scope) return Entity_Id is
      T : Entity_Id;
      --  Will be assigned the type of N
   begin
      T :=
        (if Nkind (N) = N_Defining_Identifier and then Is_Type (N)
         then
           --  If N is of Type_Kind then T is N
           N
         elsif Nkind (N) in N_Has_Etype
         then
           --  If Etype is Present then use that
           Etype (N)
         else
           --  We don't expect to get any other kind of node
           raise Program_Error);

      --  Deal with Abstract_State, which doesn't have a proper type

      if T = Standard_Void_Type then
         pragma
           Assert
             (Nkind (N) = N_Defining_Identifier
              and then Ekind (N) = E_Abstract_State);

         return T;
      end if;

      loop
         declare
            Full_V : constant Entity_Id := Full_View (T);

         begin
            --  We prefer to return the full view, if it is in SPARK and
            --  visible.

            if Present (Full_V)
              and then Entity_In_SPARK (Full_V)
              and then Is_Visible (Full_V, Scope)
            then
               T := Full_V;

            --  We do not want to return an Itype so we recurse on T's Etype if
            --  it different to T. If we cannot do any better then we will in
            --  fact return an Itype.

            elsif Is_Itype (T) then

               if Is_Nouveau_Type (T) then

                  --  The Itype is returned when we got into various base types
                  --  which flow analysis handles as blobs anyway.

                  pragma Assert (Is_Base_Type (T));
                  pragma
                    Assert
                      (Is_Array_Type (T)
                       or else Is_Anonymous_Access_Type (T)
                       or else Is_Fixed_Point_Type (T));

                  return T;
               else
                  T := Etype (T);
               end if;
            else
               return T;
            end if;
         end;
      end loop;
   end Get_Type;

   --------------------------
   -- Get_Explicit_Formals --
   --------------------------

   function Get_Explicit_Formals (E : Entity_Id) return Node_Sets.Set is
      Formal  : Entity_Id := First_Formal (E);
      Formals : Node_Sets.Set;

   begin
      --  Collect explicit formal parameters
      while Present (Formal) loop
         Formals.Insert (Formal);
         Next_Formal (Formal);
      end loop;

      return Formals;
   end Get_Explicit_Formals;

   -------------------------
   -- Get_Implicit_Formal --
   -------------------------

   function Get_Implicit_Formal (E : Entity_Id) return Entity_Id is
   begin
      case Ekind (E) is
         when E_Entry | E_Function | E_Procedure =>
            --  If E is directly enclosed in a protected object then add the
            --  protected object as an implicit formal parameter of the
            --  entry/subprogram.
            return
              (if Ekind (Scope (E)) = E_Protected_Type
               then Scope (E)
               else Empty);

         when E_Task_Type                        =>
            --  A task sees itself as a formal parameter
            return E;

         when others                             =>
            raise Program_Error;

      end case;
   end Get_Implicit_Formal;

   -----------------
   -- Get_Formals --
   -----------------

   function Get_Formals (E : Entity_Id) return Node_Sets.Set is
      Formals  : Node_Sets.Set;
      Implicit : constant Entity_Id := Get_Implicit_Formal (E);

   begin
      if Is_Subprogram_Or_Entry (E) then
         Formals := Get_Explicit_Formals (E);
      end if;

      if Present (Implicit) then
         Formals.Insert (Implicit);
      end if;

      return Formals;
   end Get_Formals;

   ------------------------
   --  Get_All_Variables --
   ------------------------

   function Get_All_Variables
     (N                       : Node_Id;
      Scope                   : Flow_Scope;
      Target_Name             : Flow_Id;
      Use_Computed_Globals    : Boolean;
      Assume_In_Expression    : Boolean := True;
      Expand_Internal_Objects : Boolean := False;
      Skip_Old                : Boolean := False) return Flow_Id_Sets.Set
   is
      Vars : Flow_Id_Sets.Set;

   begin
      for Ref_Kind in Reference_Kind loop
         Vars.Union
           (Get_Variables
              (N                       => N,
               Scope                   => Scope,
               Target_Name             => Target_Name,
               Fold_Functions          => Ref_Kind,
               Use_Computed_Globals    => Use_Computed_Globals,
               Assume_In_Expression    => Assume_In_Expression,
               Expand_Internal_Objects => Expand_Internal_Objects,
               Consider_Extensions     => False,
               Skip_Old                => Skip_Old));
      end loop;

      return Vars;
   end Get_All_Variables;

   -------------------
   -- Get_Variables --
   -------------------

   type Get_Variables_Context is record
      Scope                   : Flow_Scope;
      Target_Name             : Flow_Id;
      Fold_Functions          : Reference_Kind;
      Use_Computed_Globals    : Boolean;
      Assume_In_Expression    : Boolean;
      Expand_Internal_Objects : Boolean;
      Consider_Extensions     : Boolean;
   end record;

   function Get_Variables_Internal
     (N : Node_Id; Ctx : Get_Variables_Context; Skip_Old : Boolean := False)
      return Flow_Id_Sets.Set
   with Pre => (if Ctx.Assume_In_Expression then Nkind (N) in N_Subexpr);
   --  Internal version with a context that we'll use to recurse

   -------------------
   -- Get_Variables --
   -------------------

   function Get_Variables
     (N                       : Node_Id;
      Scope                   : Flow_Scope;
      Target_Name             : Flow_Id;
      Fold_Functions          : Reference_Kind;
      Use_Computed_Globals    : Boolean;
      Assume_In_Expression    : Boolean := True;
      Expand_Internal_Objects : Boolean := False;
      Consider_Extensions     : Boolean := False;
      Skip_Old                : Boolean := False) return Flow_Id_Sets.Set
   is
      Ctx : constant Get_Variables_Context :=
        (Scope                   => Scope,
         Target_Name             => Target_Name,
         Fold_Functions          => Fold_Functions,
         Use_Computed_Globals    => Use_Computed_Globals,
         Assume_In_Expression    => Assume_In_Expression,
         Expand_Internal_Objects => Expand_Internal_Objects,
         Consider_Extensions     => Consider_Extensions);

   begin
      return Get_Variables_Internal (N, Ctx, Skip_Old);
   end Get_Variables;

   ----------------------------
   -- Get_Variables_Internal --
   ----------------------------

   function Get_Variables_Internal
     (N : Node_Id; Ctx : Get_Variables_Context; Skip_Old : Boolean := False)
      return Flow_Id_Sets.Set
   is
      ----------------------------------------------------
      -- Subprograms that do *not* write into Variables --
      ----------------------------------------------------

      function Do_Subprogram_Call (Callsite : Node_Id) return Flow_Id_Sets.Set
      with
        Pre =>
          Nkind (Callsite) in N_Entry_Call_Statement | N_Subprogram_Call
          or else Is_Specialized_Actual (Callsite);
      --  Work out which variables (including globals) are used in the
      --  entry/subprogram call and add them to the given set. Do not follow
      --  children after calling this.

      function Do_Entity (E : Entity_Id) return Flow_Id_Sets.Set;
      --  Process the given entity and return the variables associated with it

      function Do_Attribute_Reference (N : Node_Id) return Flow_Id_Sets.Set
      with Pre => Nkind (N) = N_Attribute_Reference;
      --  Process the given attribute reference. Do not follow children after
      --  calling this.

      function Merge_Entity (E : Entity_Id) return Flow_Id_Sets.Set
      with
        Pre =>
          Ekind (E)
          in E_Constant
           | E_Discriminant
           | E_Loop_Parameter
           | E_Variable
           | Formal_Kind
          or else Is_Concurrent_Component_Or_Discr (E);
      --  Return a set that can be merged into Variables, as above

      function Recurse
        (N                   : Node_Id;
         Consider_Extensions : Boolean := False;
         Fold_Functions      : Reference_Kind := Ctx.Fold_Functions)
         return Flow_Id_Sets.Set
      with Pre => Present (N);
      --  Helper function to recurse on N

      function Untangle_Record_Fields
        (N                       : Node_Id;
         Scope                   : Flow_Scope;
         Target_Name             : Flow_Id;
         Fold_Functions          : Reference_Kind;
         Use_Computed_Globals    : Boolean;
         Expand_Internal_Objects : Boolean) return Flow_Id_Sets.Set
      with
        Pre =>
          Nkind (N) in N_Selected_Component | N_Delta_Aggregate
          or else Is_Attribute_Update (N);
      --  Process a node describing one or more record fields and return a
      --  variable set with all variables referenced.
      --
      --  Fold_Functions also has an effect on how we deal with useless
      --  'Update expressions:
      --
      --     Node                 Fold_Functions  Result
      --     -------------------  --------------  --------
      --     R'Update (X => N).Y  False           {R.Y, N}
      --     R'Update (X => N).Y  True            {R.Y}
      --     R'Update (X => N)    False           {R.Y, N}
      --     R'Update (X => N)    True            {R.Y, N}
      --
      --  Scope, Use_Computed_Globals, Expand_Internal_Objects will be passed
      --  on to Get_Variables if necessary.

      function Untangle_With_Context (N : Node_Id) return Flow_Id_Sets.Set
      is (Untangle_Record_Fields
            (N,
             Scope                   => Ctx.Scope,
             Target_Name             => Ctx.Target_Name,
             Fold_Functions          => Ctx.Fold_Functions,
             Use_Computed_Globals    => Ctx.Use_Computed_Globals,
             Expand_Internal_Objects => Ctx.Expand_Internal_Objects))
      with
        Pre =>
          Ekind
            (Unchecked_Full_Type
               (Etype
                  (if Nkind (N) = N_Delta_Aggregate
                   then Expression (N)
                   else Prefix (N))))
          in Record_Kind | Concurrent_Kind;
      --  Helper function to call Untangle_Record_Fields with the appropriate
      --  context. It can be called on types that have either components or
      --  discriminants.

      -------------
      -- Recurse --
      -------------

      function Recurse
        (N                   : Node_Id;
         Consider_Extensions : Boolean := False;
         Fold_Functions      : Reference_Kind := Ctx.Fold_Functions)
         return Flow_Id_Sets.Set
      is
         New_Ctx : Get_Variables_Context := Ctx;
      begin
         New_Ctx.Consider_Extensions := Consider_Extensions;
         New_Ctx.Fold_Functions := Fold_Functions;
         return Get_Variables_Internal (N, New_Ctx);
      end Recurse;

      ------------------
      -- Merge_Entity --
      ------------------

      function Merge_Entity (E : Entity_Id) return Flow_Id_Sets.Set is
      begin
         --  Concurrent components and discriminants are associated with
         --  a type, which is available from the entity's Scope. We return
         --  a construct of the form <Type>.<Entity> for these cases. Note
         --  <Record Type>.<Discriminant> constructs should be either filtered
         --  (using Ignore_Record_Type_Discriminants) or post-processed into
         --  a corresponding record variable.
         if Is_Concurrent_Component_Or_Discr (E)
           or else Ekind (E) = E_Discriminant
         then
            return
              Flatten_Variable
                (F     =>
                   Add_Component
                     (F    => Direct_Mapping_Id (Scope (E)),
                      Comp =>
                        (if Ekind (E) = E_Discriminant
                         then Unique_Component (E)
                         else E)),
                 Scope => Ctx.Scope);

         elsif Is_Part_Of_Concurrent_Object (E) then
            return
              Flatten_Variable
                (Add_Component
                   (Direct_Mapping_Id (Etype (Encapsulating_State (E))), E),
                 Ctx.Scope);

         else
            return Flatten_Variable (E, Ctx.Scope);
         end if;
      end Merge_Entity;

      ------------------------
      -- Do_Subprogram_Call --
      ------------------------

      function Do_Subprogram_Call (Callsite : Node_Id) return Flow_Id_Sets.Set
      is
         Is_Higher_Order_Actual : constant Boolean :=
           Is_Specialized_Actual (Callsite);

         Subprogram : constant Entity_Id :=
           (if Is_Higher_Order_Actual
            then Entity (Prefix (Callsite))
            else Get_Called_Entity (Callsite));

         Globals : Global_Flow_Ids;

         Folding : constant Boolean :=
           Ctx.Fold_Functions in Inputs | Null_Deps
           and then Ekind (Subprogram) = E_Function
           and then Has_Depends (Subprogram);
         --  ??? the name "Folding" refers to the previous implementation

         Used_Reads : Flow_Id_Sets.Set;

         V : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

         procedure Handle_Parameter (Formal : Entity_Id; Actual : Node_Id);
         --  Process parameter of a call. In particular, take into account:
         --  * the Inputs/Proof_Ins/Null_Deps mode
         --  * whether the Depends contract is present
         --  * what the Depends says about the current parameter

         ----------------------
         -- Handle_Parameter --
         ----------------------

         procedure Handle_Parameter (Formal : Entity_Id; Actual : Node_Id) is
            function May_Use_Extensions return Boolean
            is (Has_Extensions_Visible (Subprogram)
                or else Is_Class_Wide_Type (Get_Type (Formal, Ctx.Scope))
                or else
                  (Flow_Classwide.Is_Dispatching_Call (Callsite)
                   and then Is_Controlling_Formal (Formal)));
            --  True if we have the aspect set (so we know the subprogram might
            --  convert to a classwide type), we're dealing with a classwide
            --  type directly (since that may or may not have extensions), or
            --  the call is dispatching.

         begin
            --  When detecting Inputs and Null_Deps we use the Depends
            --  contract, if present; when detecting Proof_Ins, we go straight
            --  to the actual expression.

            case Ctx.Fold_Functions is
               when Inputs    =>
                  if Ekind (Subprogram) = E_Function
                    and then Has_Depends (Subprogram)
                  then
                     if Used_Reads.Contains (Direct_Mapping_Id (Formal)) then
                        V.Union (Recurse (Actual, May_Use_Extensions));
                     end if;
                  else
                     V.Union (Recurse (Actual, May_Use_Extensions));
                  end if;

               when Proof_Ins =>
                  V.Union (Recurse (Actual, May_Use_Extensions));

               when Null_Deps =>
                  if Ekind (Subprogram) = E_Function
                    and then Has_Depends (Subprogram)
                  then
                     --  If the Depends contract designates the current
                     --  parameter as a null dependency, then all pick both
                     --  its Inputs and Null_Deps.

                     if Used_Reads.Contains (Direct_Mapping_Id (Formal)) then
                        V.Union (Recurse (Actual, May_Use_Extensions));
                        V.Union
                          (Get_Variables_Internal
                             (Actual,
                              (Ctx
                               with delta
                                 Fold_Functions      => Inputs,
                                 Consider_Extensions => May_Use_Extensions)));
                     else
                        V.Union (Recurse (Actual, May_Use_Extensions));
                     end if;
                  else
                     V.Union (Recurse (Actual, May_Use_Extensions));
                  end if;
            end case;
         end Handle_Parameter;

         procedure Handle_Parameters is new
           Iterate_Call_Parameters (Handle_Parameter);

         --  Start of processing for Do_Subprogram_Call

      begin
         --  Ignore calls to predicate functions, which come from the frontend
         --  applying predicate checks where needed.

         if Ekind (Subprogram) = E_Function
           and then Is_Predicate_Function (Subprogram)
         then
            return Flow_Id_Sets.Empty_Set;
         end if;

         --  If we fold functions we need to obtain the used inputs

         if Folding then
            declare
               Depends : Dependency_Maps.Map;

            begin
               Get_Depends
                 (Subprogram           => Subprogram,
                  Scope                => Ctx.Scope,
                  Classwide            =>
                    Flow_Classwide.Is_Dispatching_Call (Callsite),
                  Depends              => Depends,
                  Use_Computed_Globals => Ctx.Use_Computed_Globals);

               pragma Assert (Depends.Length in 1 .. 2);
               --  For functions Depends always mentions the 'Result
               --  (user-written or synthesized) and possibly also null.

               case Ctx.Fold_Functions is
                  when Inputs    =>
                     Flow_Id_Sets.Move
                       (Target => Used_Reads,
                        Source => Depends (Direct_Mapping_Id (Subprogram)));

                  when Proof_Ins =>
                     raise Program_Error;

                  when Null_Deps =>
                     if Depends.Contains (Null_Flow_Id) then
                        Flow_Id_Sets.Move
                          (Target => Used_Reads,
                           Source => Depends (Null_Flow_Id));
                     end if;
               end case;

               Remove_Constants (Used_Reads);
            end;
         end if;

         --  If this is an external call to protected subprogram then we also
         --  need to add the enclosing object to the variables we're using;
         --  if this is an internal call, then add the protected type itself.
         --  Also, take into account same things as in Handle_Parameter.

         if Ekind (Scope (Subprogram)) = E_Protected_Type then
            declare
               Implicit_Actual : constant Flow_Id :=
                 Direct_Mapping_Id (Scope (Subprogram));

            begin
               case Ctx.Fold_Functions is
                  when Inputs    =>
                     if Ekind (Subprogram) = E_Function
                       and then Has_Depends (Subprogram)
                     then
                        if Used_Reads.Contains (Implicit_Actual) then
                           V.Union
                             (if Is_External_Call (Callsite)
                              then Recurse (Prefix (Name (Callsite)))
                              else
                                Flatten_Variable (Implicit_Actual, Ctx.Scope));
                        end if;
                     else
                        V.Union
                          (if Is_External_Call (Callsite)
                           then Recurse (Prefix (Name (Callsite)))
                           else Flatten_Variable (Implicit_Actual, Ctx.Scope));
                     end if;

                  when Proof_Ins =>
                     if Is_External_Call (Callsite) then
                        V.Union (Recurse (Prefix (Name (Callsite))));
                     end if;

                  when Null_Deps =>
                     if Is_External_Call (Callsite) then
                        if Ekind (Subprogram) = E_Function
                          and then Has_Depends (Subprogram)
                        then
                           if Used_Reads.Contains (Implicit_Actual) then
                              V.Union (Recurse (Prefix (Name (Callsite))));

                              V.Union
                                (Get_Variables_Internal
                                   (Prefix (Name (Callsite)),
                                    (Ctx
                                     with delta Fold_Functions => Inputs)));
                           else
                              V.Union (Recurse (Prefix (Name (Callsite))));
                           end if;
                        else
                           V.Union (Recurse (Prefix (Name (Callsite))));
                        end if;
                     else
                        if Ekind (Subprogram) = E_Function
                          and then Has_Depends (Subprogram)
                        then
                           if Used_Reads.Contains (Implicit_Actual) then
                              V.Union
                                (Flatten_Variable
                                   (Implicit_Actual, Ctx.Scope));
                           end if;
                        else
                           null;
                        end if;
                     end if;
               end case;
            end;
         end if;

         --  Merge the actuals into the set of variables used

         if not Is_Higher_Order_Actual then
            Handle_Parameters (Callsite);
         end if;

         --  Determine the global effects of the called program

         if Ekind (Subprogram) /= E_Subprogram_Type then
            Get_Globals
              (Subprogram          => Subprogram,
               Scope               => Ctx.Scope,
               Classwide           =>
                 not Is_Higher_Order_Actual
                 and then Flow_Classwide.Is_Dispatching_Call (Callsite),
               Globals             => Globals,
               Use_Deduced_Globals => Ctx.Use_Computed_Globals);

            Remove_Constants (Globals.Proof_Ins);
            Remove_Constants (Globals.Inputs);
         end if;

         --  Handle globals; very much like in Handle_Parameter

         case Ctx.Fold_Functions is
            when Inputs    =>
               for G of Globals.Inputs loop
                  if Ekind (Subprogram) = E_Function
                    and then Has_Depends (Subprogram)
                  then
                     if Used_Reads.Contains (Change_Variant (G, Normal_Use))
                     then
                        V.Union
                          (Flatten_Variable
                             (Change_Variant (G, Normal_Use), Ctx.Scope));
                     end if;
                  else
                     V.Union
                       (Flatten_Variable
                          (Change_Variant (G, Normal_Use), Ctx.Scope));
                  end if;
               end loop;

            when Proof_Ins =>
               for G of Globals.Proof_Ins loop
                  V.Union
                    (Flatten_Variable
                       (Change_Variant (G, Normal_Use), Ctx.Scope));
               end loop;

            when Null_Deps =>
               for G of Globals.Inputs loop
                  if Ekind (Subprogram) = E_Function
                    and then Has_Depends (Subprogram)
                  then
                     if Used_Reads.Contains (Change_Variant (G, Normal_Use))
                     then
                        V.Union
                          (Flatten_Variable
                             (Change_Variant (G, Normal_Use), Ctx.Scope));
                     end if;
                  end if;
               end loop;
         end case;

         --  For calls via access-to-subprogram recurse into their prefix

         if Ekind (Subprogram) = E_Subprogram_Type then
            V.Union (Recurse (Prefix (Name (Callsite))));
         end if;

         --  Apply sanity check for functions
         --  ??? we should not emit errors from an utility routine like this,
         --  but otherwise we would need:
         --  * an exact Node_Id of the call in the flow graph (for
         --    subprograms in the current unit whose bodies are in SPARK)
         --  * an extra sanity-check for contracts of subprograms from other
         --    units or whose bodies are not in SPARK

         if Nkind (Callsite) = N_Function_Call
           and then not Globals.Outputs.Is_Empty
           and then not Gnat2Why_Args.Global_Gen_Mode
           and then not Is_Function_With_Side_Effects (Subprogram)
         then
            Error_Msg_N
              (Msg   => "side effects of function & are not modeled in SPARK",
               N     => Callsite,
               Names => [Subprogram]);
         end if;

         return V;
      end Do_Subprogram_Call;

      ---------------
      -- Do_Entity --
      ---------------

      function Do_Entity (E : Entity_Id) return Flow_Id_Sets.Set is
      begin
         --  ??? This might be too early for return, e.g. when handling
         --  discriminant constraints (but their handling is suspicious on its
         --  own). Anyway, the idea is that this routine processes references
         --  to entities and when collecting Proof_Ins/Null_Deps such a
         --  reference itself doesn't contribute any object.

         if Ctx.Fold_Functions /= Inputs then
            return Flow_Id_Sets.Empty_Set;
         end if;

         --  Handle overlays before filtering constants without variable inputs

         if Ekind (E) = E_Variable
           and then Present (Ultimate_Overlaid_Entity (E))
         then
            return Do_Entity (Ultimate_Overlaid_Entity (E));
         end if;

         case Ekind (E) is
            --------------------------------------------
            -- Entities requiring some kind of action --
            --------------------------------------------

            when E_Constant                               =>
               if Ctx.Expand_Internal_Objects
                 and then not Comes_From_Source (E)
               then

                  --  To expand synthesized constants, we need to find the
                  --  original expression and find the variable set of that.

                  declare
                     Obj_Decl : constant Node_Id := Parent (E);

                     pragma
                       Assert
                         (Nkind (Obj_Decl) = N_Object_Declaration,
                          "Bad parent of constant entity");

                     Expr : constant Node_Id := Expression (Obj_Decl);

                     pragma
                       Assert (Present (Expr), "Constant has no expression");

                  begin
                     return Recurse (Expr);
                  end;

               else

                  --  Note that for constants of a constrained record or
                  --  concurrent type we want to detect their discriminant
                  --  constraints so we add them as well.

                  if Is_Access_Variable (Etype (E))
                    or else Has_Variable_Input (E)
                  then
                     return Merge_Entity (E);
                  else
                     return Flow_Id_Sets.Empty_Set;
                  end if;
               end if;

            when E_Component
               --  E_Constant is dealt with in the above case
               | E_Discriminant
               | E_Loop_Parameter
               | E_Variable
               | Formal_Kind                              =>
               if Is_Discriminal (E) then
                  return Do_Entity (Discriminal_Link (E));
               end if;

               --  References to the current instance of the single concurrent
               --  type are represented as E_Variable of the corresponding
               --  single concurrent object (because that is more convenient
               --  for the frontend error reporing machinery). Here we detect
               --  such references (with an abuse of Ctx.Scope to know the
               --  current context) and ignore them, just like we ignore
               --  references to the current instance of a non-single
               --  concurrent type.
               --
               --  For standalone subprograms (e.g. main subprogram) the
               --  Ctx.Scope is currently represented by a Null_Flow_Scope,
               --  whose Ent is Empty, which would crash the Is_CCT_Instance.
               --  Such standalone subprograms can't, by definition, reference
               --  the current instance of the concurrent type.

               if Is_Single_Concurrent_Object (E)
                 and then Present (Ctx.Scope)
                 and then Is_CCT_Instance (Etype (E), Ctx.Scope.Ent)
               then
                  return Flow_Id_Sets.Empty_Set;
               end if;

               declare
                  Vars : Flow_Id_Sets.Set := Merge_Entity (E);

               begin
                  --  If we've extensions (and we care about them) then we need
                  --  to add them now.

                  if Ctx.Consider_Extensions
                    and then Extensions_Visible (E, Ctx.Scope)
                  then
                     Vars.Include
                       (Direct_Mapping_Id
                          (Unique_Entity (E), Facet => Extension_Part));
                  end if;

                  return Vars;
               end;

            --  Types can only appear when we traverse statements; when we
            --  traverse expressions we special-case type identifiers depending
            --  on the context.

            when Type_Kind                                =>
               pragma Assert (not Ctx.Assume_In_Expression);

               --  These kinds of types are not allowed in SPARK (yet)
               pragma
                 Assert
                   (Ekind (E) not in E_Exception_Type | E_Subprogram_Type);

               if Is_Scalar_Type (E) then
                  declare
                     SR : constant Node_Id := Scalar_Range (E);
                     LB : constant Node_Id := Low_Bound (SR);
                     HB : constant Node_Id := High_Bound (SR);

                  begin
                     return Recurse (LB) or Recurse (HB);
                  end;
               end if;

            ---------------------------------------
            -- Entities with no flow consequence --
            ---------------------------------------

            when Named_Kind | E_Enumeration_Literal       =>
               --  All of these are simply constants, with no flow concern
               null;

            when E_Entry | E_Function | E_Procedure       =>
               --  Dealt with when dealing with N_Subprogram_Call nodes, except
               --  when traversing the AST looking for first use of a variable.
               --  ??? the following assertion can fail on access to
               --  subprograms, it should be fixed.
               --
               --  pragma Assert (not Ctx.Assume_In_Expression);
               null;

            when E_Block
               | E_Exception
               | E_Label
               | E_Loop
               | E_Package
               | E_Assertion_Level                        =>
               --  Nothing to do for these directly; we get them while
               --  traversing a list of statements or an identifier.
               null;

            -------------------------------------------
            -- Entities not expected or not in SPARK --
            -------------------------------------------

            --  Entities related to generic units are not in SPARK itself (we
            --  analyze instantiations instead of generics).

            when Formal_Object_Kind | Generic_Unit_Kind   =>
               raise Program_Error;

            --  Frontend rewrites calls to operators into function calls

            when E_Operator                               =>
               raise Program_Error;

            --  Entry families are not in SPARK yet

            when E_Entry_Family | E_Entry_Index_Parameter =>
               raise Program_Error;

            --  Abstract state cannot directly appear in expressions

            when E_Abstract_State                         =>
               raise Program_Error;

            when E_Package_Body
               | E_Protected_Body
               | E_Return_Statement
               | E_Subprogram_Body
               | E_Task_Body
               | E_Void                                   =>
               raise Program_Error;

         end case;

         return Flow_Id_Sets.Empty_Set;
      end Do_Entity;

      ----------------------------
      -- Do_Attribute_Reference --
      ----------------------------

      function Do_Attribute_Reference (N : Node_Id) return Flow_Id_Sets.Set is
         The_Attribute : constant Attribute_Id :=
           Get_Attribute_Id (Attribute_Name (N));

         Variables : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      begin
         --  The code here first deals with the unusual cases, followed by the
         --  usual case.
         --
         --  Sometimes we do a bit of the unusual with all the usual, in which
         --  case we do not exit; otherwise we return directly.

         -----------------
         -- The unusual --
         -----------------

         case The_Attribute is
            when Attribute_Access      =>
               if Is_Specialized_Actual (N) then
                  return Do_Subprogram_Call (N);
               end if;

            when Attribute_Result      =>
               pragma Assert (Ekind (Entity (Prefix (N))) = E_Function);

               --  It is an over-approximation to return all components of the
               --  'Result, but it is actually harmless, because in the Post
               --  expression the entire 'Result object must be initialized
               --  anyway.

               return Flatten_Variable (Entity (Prefix (N)), Ctx.Scope);

            when Attribute_Update      =>
               declare
                  --  There is exactly one attribute expression, which is an
                  --  aggregate with component associations only.

                  Expr : constant Node_Id := First (Expressions (N));
                  pragma
                    Assert
                      (No (Next (Expr))
                       and then Nkind (Expr) = N_Aggregate
                       and then No (Expressions (Expr))
                       and then not Null_Record_Present (Expr));

                  Assoc  : Node_Id;
                  Choice : Node_Id;
                  Index  : Node_Id;

                  T : constant Entity_Id := Get_Type (N, Ctx.Scope);

               begin
                  Variables.Union (Recurse (Prefix (N)));

                  if Is_Record_Type (T) then
                     if Is_Tagged_Type (T) then
                        --  ??? Precise analysis is disabled for tagged types

                        --  The syntax is:
                        --
                        --  PREFIX'Update
                        --    ( Comp1a | Comp1b | ... => Expr1, ...)
                        --
                        --  so we sanity check component names CompXY and
                        --  recurse into expresions ExprX.
                        Assoc := First (Component_Associations (Expr));
                        loop
                           Choice := First (Choices (Assoc));
                           loop
                              pragma Assert (Nkind (Choice) = N_Identifier);
                              Next (Choice);
                              exit when No (Choice);
                           end loop;
                           Variables.Union (Recurse (Expression (Assoc)));
                           Next (Assoc);
                           exit when No (Assoc);
                        end loop;

                        return Variables;
                     else
                        return Untangle_With_Context (N);
                     end if;
                  else
                     pragma Assert (Is_Array_Type (T));

                     --  The syntax differs between single and multiple
                     --  dimensional array updates:
                     --
                     --  PREFIX'Update
                     --    ( ARRAY_COMPONENT_ASSOCIATION
                     --   {, ARRAY_COMPONENT_ASSOCIATION } )
                     --
                     --  PREFIX'Update
                     --    ( MULTIDIMENSIONAL_ARRAY_COMPONENT_ASSOCIATION
                     --   {, MULTIDIMENSIONAL_ARRAY_COMPONENT_ASSOCIATION } )
                     --
                     --  MULTIDIMENSIONAL_ARRAY_COMPONENT_ASSOCIATION ::=
                     --    INDEX_EXPRESSION_LIST_LIST => EXPRESSION
                     --
                     --  INDEX_EXPRESSION_LIST_LIST ::=
                     --    INDEX_EXPRESSION_LIST {| INDEX_EXPRESSION_LIST }
                     --
                     --  INDEX_EXPRESSION_LIST ::=
                     --    ( EXPRESSION {, EXPRESSION } )

                     Assoc := First (Component_Associations (Expr));
                     loop
                        Choice := First (Choices (Assoc));
                        loop
                           --  For multi-dimensional array update the n-dim
                           --  indices appear as nested aggregates whose
                           --  expressions stand for the indices within the
                           --  individual dimensions.

                           if Nkind (Choice) = N_Aggregate then
                              pragma Assert (Number_Dimensions (T) > 1);
                              pragma
                                Assert
                                  (No (Component_Associations (Choice))
                                   and then not Null_Record_Present (Choice));

                              Index := First (Expressions (Choice));
                              loop
                                 Variables.Union (Recurse (Index));
                                 Next (Index);
                                 exit when No (Index);
                              end loop;

                           --  For one-dimentionsal array update the indices
                           --  appear as aggregate choices.

                           else
                              pragma Assert (Number_Dimensions (T) = 1);

                              --  Array component choice appears in a
                              --  subset of forms allowed for aggregates,
                              --  which are handled when processing
                              --  N_Component_Association nodes.

                              --  "(Low .. High => ...)"

                              if Nkind (Choice) = N_Range then
                                 Variables.Union
                                   (Recurse (Low_Bound (Choice)));
                                 Variables.Union
                                   (Recurse (High_Bound (Choice)));

                              --  "(A_Subtype range Low .. High => ...)"

                              elsif Nkind (Choice) = N_Subtype_Indication then
                                 declare
                                    R : constant Node_Id :=
                                      Range_Expression (Constraint (Choice));
                                 begin
                                    Variables.Union (Recurse (Low_Bound (R)));
                                    Variables.Union (Recurse (High_Bound (R)));
                                 end;

                              --  "(A_Subtype => ...)"

                              elsif Is_Entity_Name (Choice)
                                and then Is_Type (Entity (Choice))
                              then
                                 Variables.Union
                                   (Recurse
                                      (Type_Low_Bound (Entity (Choice))));
                                 Variables.Union
                                   (Recurse
                                      (Type_High_Bound (Entity (Choice))));

                              --  "(1 => ...)" or "(X + Y => ...)", etc.

                              elsif Nkind (Choice) in N_Subexpr then
                                 Variables.Union (Recurse (Choice));

                              else
                                 raise Program_Error;
                              end if;
                           end if;

                           Next (Choice);
                           exit when No (Choice);
                        end loop;

                        Variables.Union (Recurse (Expression (Assoc)));

                        Next (Assoc);
                        exit when No (Assoc);
                     end loop;
                  end if;
               end;

               return Variables;

            when Attribute_Constrained =>

               --  Mimic how proof recognizes when GNAT expands 'Constrained
               --  into an extra formal that is passed at runtime. ??? This is
               --  pessimistic, e.g. a formal of a constrained type has its
               --  'Constrained known statically.

               if Ctx.Fold_Functions = Inputs
                 and then Is_Entity_Name (Prefix (N))
                 and then
                   Ekind (Entity (Prefix (N)))
                   in E_In_Out_Parameter | E_Out_Parameter
                 and then
                   Has_Discriminants
                     (Get_Type (Entity (Prefix (N)), Ctx.Scope))
               then
                  return
                    Flow_Id_Sets.To_Set
                      (Direct_Mapping_Id
                         (Entity (Prefix (N)), Facet => The_Bounds));

               --  Otherwise, the attribute is known statically, but the prefix
               --  is still evaluated and we capture this as null dependencies.

               elsif Ctx.Fold_Functions = Null_Deps
                 and then not Statically_Names_Object (Prefix (N))
               then
                  return Recurse (Prefix (N), Fold_Functions => Inputs);
               else
                  return Flow_Id_Sets.Empty_Set;
               end if;

            when Attribute_Alignment
               | Attribute_Size
               | Attribute_Object_Size
               | Attribute_Value_Size  =>
               --  Attribute Size and similar do not read data from their
               --  prefix (which can be either a type name or an object
               --  reference), but for arrays and discriminated records
               --  their value depends on the array bounds and discriminant
               --  constraints, respectively.

               --  Also, if the object reference is anything but a name (e.g. a
               --  function call), then the prefix is actually evaluated and
               --  the attribute value depends on the prefix.

               --  Attribute Alignment doesn't seem to depend on the array
               --  bounds and discriminant constraints, but otherwise behaves
               --  just like attribute Size, so for simplicity we handle both
               --  attributes in the same way.

               declare
                  procedure Get_Type_Size (T : Type_Kind_Id);
                  --  Get variables from the bounds and discriminants of type
                  --  T, because they affect its size.

                  -------------------
                  -- Get_Type_Size --
                  -------------------

                  procedure Get_Type_Size (T : Type_Kind_Id) is
                  begin
                     if Is_Array_Type (T) then
                        declare
                           Index : Node_Id;
                        begin
                           Index := First_Index (T);
                           while Present (Index) loop
                              Variables.Union
                                (Recurse (Type_Low_Bound (Etype (Index))));
                              Variables.Union
                                (Recurse (Type_High_Bound (Etype (Index))));
                              Next_Index (Index);
                           end loop;
                        end;
                     elsif Has_Discriminants (T) then
                        for C of Iter (Discriminant_Constraint (T)) loop
                           Variables.Union (Recurse (C));
                        end loop;
                     end if;
                  end Get_Type_Size;

                  Pref      : constant Node_Id := Prefix (N);
                  Pref_Type : constant Entity_Id := Etype (Pref);

               begin
                  if Is_Object_Reference (Pref) then

                     if Is_Name_Reference (Pref) then
                        --  Attribute whose prefix is a class-wide object
                        --  reference is expanded into a dispatching function
                        --  call whose value depends on the object itself, but
                        --  currently marking rejects this as unsupported.
                        --
                        --  For other objects the attribute values don't depend
                        --  on the prefix.

                        pragma Assert (not Is_Class_Wide_Type (Pref_Type));
                     else
                        Variables.Union (Recurse (Pref));
                     end if;

                  else
                     pragma
                       Assert
                         (Is_Entity_Name (Pref) and then Is_Type (Pref_Type));
                  end if;

                  Get_Type_Size (Pref_Type);
               end;

               return Variables;

            when Attribute_First
               | Attribute_Last
               | Attribute_Length
               | Attribute_Range       =>
               declare
                  T : Entity_Id;
                  --  Type of the attribute prefix

                  LB : Node_Id;
                  HB : Node_Id;
                  --  Low and high bounds, respectively

                  Dims  : Pos;
                  Index : Node_Id;
                  --  Number of dimensions and index for multi-dimensional
                  --  arrays.

               begin
                  --  ??? We don't use Get_Type, because currently for a record
                  --  component with per-object constraints it returns its
                  --  ultimate constrained type. Instead, when the Etype is
                  --  private, we just take its full view, because we know that
                  --  the attribute wouldn't be legal on a private type so its
                  --  full view must have been visible.

                  T := Etype (Prefix (N));

                  if Is_Private_Type (T) then
                     T := Full_View (T);
                  end if;

                  pragma Assert (Is_Array_Type (T) or else Is_Scalar_Type (T));
                  pragma Assert (Entity_In_SPARK (T));

                  --  Explicitly handle references to components with
                  --  per-object constraints.

                  if Is_Constrained (T)
                    and then Is_Itype (T)
                    and then
                      Nkind (Associated_Node_For_Itype (T))
                      = N_Component_Declaration
                  then
                     pragma
                       Assert
                         (Nkind (Prefix (N))
                          in N_Explicit_Dereference | N_Selected_Component);
                     declare
                        Comp : constant Entity_Id :=
                          Defining_Identifier (Associated_Node_For_Itype (T));
                     begin
                        if Has_Per_Object_Constraint (Comp) then
                           return Recurse (Prefix (N));
                        end if;
                     end;
                  end if;

                  if Is_Constrained (T) then
                     if Is_Array_Type (T) then
                        if Present (Expressions (N)) then
                           Dims :=
                             UI_To_Int (Intval (First (Expressions (N))));
                           Index := First_Index (T);

                           for J in 1 .. Dims - 1 loop
                              Next_Index (Index);
                           end loop;

                           LB := Type_Low_Bound (Etype (Index));
                           HB := Type_High_Bound (Etype (Index));

                        else
                           LB := Type_Low_Bound (Etype (First_Index (T)));
                           HB := Type_High_Bound (Etype (First_Index (T)));
                        end if;
                     else
                        pragma Assert (Is_Scalar_Type (T));
                        LB := Low_Bound (Scalar_Range (T));
                        HB := High_Bound (Scalar_Range (T));
                     end if;

                     if The_Attribute /= Attribute_First then
                        --  Last, Length, and Range
                        Variables.Union (Recurse (HB));
                     end if;

                     if The_Attribute /= Attribute_Last then
                        --  First, Length, and Range
                        Variables.Union (Recurse (LB));
                     end if;

                  else
                     for F of Recurse (Prefix (N)) loop
                        if F.Kind in Direct_Mapping | Record_Field
                          and then F.Facet = Normal_Part
                          and then Has_Bounds (F, Ctx.Scope)
                        then
                           --  This is not a bound variable, but it requires
                           --  bounds tracking. We make it a bound variable.

                           --  ??? we should only do this if the immediate
                           --  prefix denotes an object (e.g. "Obj'Length"
                           --  but not "Func (Obj)'Length").

                           Variables.Include
                             ((F with delta Facet => The_Bounds));

                        else
                           --  This is something else, we just copy it
                           Variables.Include (F);
                        end if;
                     end loop;
                  end if;
               end;
               return Variables;

            when Attribute_Loop_Entry  =>
               --  Again, we ignore loop entry references, these are dealt with
               --  by Do_Pragma and Do_Loop_Statement in the CFG construction.
               return Flow_Id_Sets.Empty_Set;

            when Attribute_Address     =>

               --  For supported overlays like "X'Address" the expression does
               --  not read the overlying object (but reads array and slice
               --  expressions in the prefix, if any). For other subexpressoins
               --  in the prefix we conservatively assume them to be reads.

               declare
                  Pref : Node_Id := Prefix (N);
               begin
                  loop
                     case Nkind (Pref) is
                        when N_Identifier | N_Expanded_Name                =>
                           exit;

                        when N_Explicit_Dereference | N_Selected_Component =>
                           Pref := Prefix (Pref);

                        when N_Indexed_Component                           =>
                           declare
                              Index : Node_Id;
                           begin
                              Index := First (Expressions (Pref));
                              while Present (Index) loop
                                 Variables.Union (Recurse (Index));
                                 Next (Index);
                              end loop;
                           end;

                           Pref := Prefix (Pref);

                        when N_Slice                                       =>
                           declare
                              R : constant Node_Id :=
                                Get_Range (Discrete_Range (Pref));
                           begin
                              Variables.Union (Recurse (Low_Bound (R)));
                              Variables.Union (Recurse (High_Bound (R)));
                           end;

                           Pref := Prefix (Pref);

                        when others                                        =>
                           return Variables.Union (Recurse (Pref));
                     end case;
                  end loop;
               end;

               return Variables;

            when Attribute_Old         =>
               --  If Skip_Old is True, ignore the attribute. Otherwise, we
               --  just need the usual.

               if Skip_Old then
                  return Flow_Id_Sets.Empty_Set;
               end if;

            when Attribute_Callable
               | Attribute_Caller
               | Attribute_Count
               | Attribute_Terminated  =>
               --  Add the implicit use of
               --  Ada.Task_Identification.Tasking_State
               Variables.Union
                 (Flatten_Variable (RTE (RE_Tasking_State), Ctx.Scope));

            --  We also need to do the usual

            when others                =>
               --  We just need to do the usual
               null;
         end case;

         ---------------
         -- The usual --
         ---------------

         --  Here we just recurse down the tree, so we look at our prefix and
         --  then any arguments (if any).
         --
         --  The reason we can't do this first is that some attributes skip
         --  looking at the prefix (e.g. address) or do something strange (e.g.
         --  update).

         --  If the prefix denotes a type (which happens for quite a few
         --  attributes), then we have either already dealt with its prefix
         --  above (e.g. 'First) or this prefix is ignored below (e.g. 'Min).

         if Is_Entity_Name (Prefix (N)) and then Is_Type (Entity (Prefix (N)))
         then
            pragma
              Assert
                (The_Attribute
                 in Attribute_Alignment
                  | Attribute_Ceiling
                  | Attribute_Component_Size
                  | Attribute_Copy_Sign
                  | Attribute_Enum_Rep
                  | Attribute_Enum_Val
                  | Attribute_Floor
                  | Attribute_Image
                  | Attribute_Max
                  | Attribute_Min
                  | Attribute_Mod
                  | Attribute_Pos
                  | Attribute_Pred
                  | Attribute_Remainder
                  | Attribute_Rounding
                  | Attribute_Succ
                  | Attribute_Truncation
                  | Attribute_Val
                  | Attribute_Value);
         else
            Variables.Union (Recurse (Prefix (N)));
         end if;

         if Present (Expressions (N)) then
            declare
               Expr : Node_Id := First (Expressions (N));

            begin
               loop
                  Variables.Union (Recurse (Expr));
                  Next (Expr);
                  exit when No (Expr);
               end loop;
            end;
         end if;

         return Variables;
      end Do_Attribute_Reference;

      ----------------------------
      -- Untangle_Record_Fields --
      ----------------------------

      function Untangle_Record_Fields
        (N                       : Node_Id;
         Scope                   : Flow_Scope;
         Target_Name             : Flow_Id;
         Fold_Functions          : Reference_Kind;
         Use_Computed_Globals    : Boolean;
         Expand_Internal_Objects : Boolean) return Flow_Id_Sets.Set
      is
         M : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;

         Root_Node : Node_Id := N;

         Component : Node_Lists.List := Node_Lists.Empty_List;
         Seq       : Node_Lists.List := Node_Lists.Empty_List;

         Comp_Id       : Positive;
         Current_Field : Flow_Id;

         All_Vars     : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
         Depends_Vars : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
         Proof_Vars   : constant Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

         function Is_Ignored_Attribute (N : Node_Id) return Boolean;
         --  Returns True if N denotes an attribute 'Old or 'Loop_Entry, which
         --  are ignored when detecting references to variables.

         function Is_Ignored_Attribute (N : Node_Id) return Boolean
         is (Nkind (N) = N_Attribute_Reference
             and then Attribute_Name (N) in Name_Old | Name_Loop_Entry);

         function Get_Vars_Wrapper (N : Node_Id) return Flow_Id_Sets.Set
         is (Get_Variables
               (N,
                Scope                   => Scope,
                Target_Name             => Target_Name,
                Fold_Functions          => Fold_Functions,
                Use_Computed_Globals    => Use_Computed_Globals,
                Expand_Internal_Objects => Expand_Internal_Objects));

         procedure Untangle_Delta_Fields (Assocs : List_Id)
         with Pre => Is_Non_Empty_List (Assocs);

         ---------------------------
         -- Untangle_Delta_Fields --
         ---------------------------

         procedure Untangle_Delta_Fields (Assocs : List_Id) is
            Component_Association : Node_Id := First (Assocs);
            --  Iterators for the 'Update (...) expression

         begin
            Indent;
            while Present (Component_Association) loop
               --  HACK: skip deep choices for now until they are supported in
               --  flow.
               if not Sem_Aggr.Is_Deep_Choice
                        (First (Choices (Component_Association)), Etype (N))
               then
                  declare
                     Choice : constant Node_Id :=
                       First (Choices (Component_Association));
                     Expr   : constant Node_Id :=
                       Expression (Component_Association);

                     Comp : constant Entity_Id :=
                       Unique_Component (Entity (Choice));

                     Expr_Vars : Flow_Id_Sets.Set;
                     FS        : Flow_Id_Sets.Set;

                  begin
                     pragma Annotate (Xcov, Exempt_On, "Debugging code");
                     if Debug_Trace_Untangle_Fields then
                        Write_Str ("Updating component ");
                        Sprint_Node_Inline (Comp);
                        Write_Eol;
                     end if;
                     pragma Annotate (Xcov, Exempt_Off);

                     --  Composite update

                     if Is_Record_Type (Get_Type (Comp, Scope)) then

                        --  We should call Untangle_Record_Aggregate here.
                        --  For now we us a safe default (all fields depend
                        --  on everything).

                        case Nkind (Expr) is
                           --  when N_Aggregate =>
                           --     null;

                           when others =>
                              if Fold_Functions = Inputs then
                                 Expr_Vars := Get_Vars_Wrapper (Expr);

                                 --  Not sure what to do, so set all
                                 --  sensible fields to the given variables.

                                 FS :=
                                   Flatten_Variable
                                     (Add_Component (Current_Field, Comp),
                                      Scope);

                                 for F of FS loop
                                    M.Replace (F, Expr_Vars);
                                 end loop;

                              else
                                 All_Vars.Union
                                   (Get_Variables
                                      (N                       => Expr,
                                       Scope                   => Scope,
                                       Target_Name             => Target_Name,
                                       Fold_Functions          => Inputs,
                                       Use_Computed_Globals    =>
                                         Use_Computed_Globals,
                                       Expand_Internal_Objects =>
                                         Expand_Internal_Objects));
                              end if;

                        end case;

                     --  Direct field update of M

                     else
                        if Fold_Functions = Inputs then
                           Expr_Vars := Get_Vars_Wrapper (Expr);

                           M.Replace
                             (Add_Component (Current_Field, Comp), Expr_Vars);
                        else
                           All_Vars.Union
                             (Get_Variables
                                (N                       => Expr,
                                 Scope                   => Scope,
                                 Target_Name             => Target_Name,
                                 Fold_Functions          =>
                                   (if Fold_Functions = Proof_Ins
                                    then Proof_Ins
                                    else Inputs),
                                 Use_Computed_Globals    =>
                                   Use_Computed_Globals,
                                 Expand_Internal_Objects =>
                                   Expand_Internal_Objects));
                        end if;
                     end if;

                     --  Expansion rewrites multiple choices like "X | Y => A"
                     --  into separate component associations like
                     --  "X => A, Y => A", because depending on the type of the
                     --  component we might (or might not) need checks for the
                     --  expression.

                     pragma Assert (No (Next (Choice)));
                  end;
               end if;

               Next (Component_Association);
            end loop;
            Outdent;
         end Untangle_Delta_Fields;

         --  Start of processing for Untangle_Record_Fields

      begin
         pragma Annotate (Xcov, Exempt_On, "Debugging code");
         if Debug_Trace_Untangle_Fields then
            Write_Str ("Untangle_Record_Field on ");
            Sprint_Node_Inline (N);
            Write_Eol;
            Indent;
         end if;
         pragma Annotate (Xcov, Exempt_Off);

         --  First, we figure out what the root node is. For example in
         --  Foo.Bar'Update(...).Z the root node will be Foo.
         --
         --  We also note all components (bar, z), 'update nodes and the order
         --  in which they access or update fields (bar, the_update, z).

         while Nkind (Root_Node) = N_Selected_Component
           or else
             ((Is_Attribute_Update (Root_Node)
               or else
                 Nkind (Root_Node)
                 in N_Delta_Aggregate
                  | N_Type_Conversion
                  | N_Qualified_Expression)
              and then
                Is_Record_Type (Unchecked_Full_Type (Etype (Root_Node))))
           or else Is_Ignored_Attribute (Root_Node)
         loop
            if Nkind (Root_Node) = N_Selected_Component then
               Component.Prepend
                 (Unique_Component (Entity (Selector_Name (Root_Node))));
            end if;

            if not Is_Ignored_Attribute (Root_Node) then
               Seq.Prepend (Root_Node);
            end if;

            Root_Node :=
              (if Nkind (Root_Node)
                  in N_Delta_Aggregate
                   | N_Type_Conversion
                   | N_Qualified_Expression
               then Expression (Root_Node)
               else Prefix (Root_Node));

         end loop;

         pragma Annotate (Xcov, Exempt_On, "Debugging code");
         if Debug_Trace_Untangle_Fields then
            Write_Str ("Root: ");
            Sprint_Node_Inline (Root_Node);
            Write_Eol;

            Write_Str ("Components:");
            for C of Component loop
               Write_Str (" ");
               Sprint_Node_Inline (C);
            end loop;
            Write_Eol;

            Write_Str ("Seq:");
            Write_Eol;
            Indent;
            for N of Seq loop
               Print_Node_Briefly (N);
            end loop;
            Outdent;
         end if;
         pragma Annotate (Xcov, Exempt_Off);

         --  If the root node is not an entire record variable, we recurse here
         --  and then simply merge all variables we find here and then abort.
         --  Also, we apply this simplified processing to objects coming from
         --  declare expressions (because we can't do better with the current
         --  handling of declare expressions in flow).

         if not (Nkind (Root_Node)
                 in N_Identifier | N_Expanded_Name | N_Target_Name
                 and then
                   (if Nkind (Root_Node) = N_Identifier
                    then not Comes_From_Declare_Expr (Entity (Root_Node)))
                 and then
                   Is_Record_Type (Unchecked_Full_Type (Etype (Root_Node))))
         then
            return Vars : Flow_Id_Sets.Set do

               --  Recurse on root

               Vars := Get_Vars_Wrapper (Root_Node);

               --  Add anything we might find in 'Update or delta_aggregate
               --  expressions.

               for N of Seq loop
                  case Nkind (N) is
                     when N_Attribute_Reference  =>
                        pragma Assert (Is_Attribute_Update (N));
                        pragma Assert (List_Length (Expressions (N)) = 1);

                        declare
                           Component_Association : Node_Id :=
                             First
                               (Component_Associations
                                  (First (Expressions (N))));

                        begin
                           loop
                              Vars.Union
                                (Get_Vars_Wrapper
                                   (Expression (Component_Association)));
                              Next (Component_Association);
                              exit when No (Component_Association);
                           end loop;
                        end;

                     when N_Delta_Aggregate      =>
                        declare
                           Component_Association : Node_Id :=
                             First (Component_Associations (N));
                        begin
                           loop
                              Vars.Union
                                (Get_Vars_Wrapper
                                   (Expression (Component_Association)));
                              Next (Component_Association);
                              exit when No (Component_Association);
                           end loop;
                        end;

                     when N_Selected_Component
                        | N_Type_Conversion
                        | N_Qualified_Expression =>
                        null;

                     when others                 =>
                        raise Why.Unexpected_Node;
                  end case;
               end loop;

               pragma Annotate (Xcov, Exempt_On, "Debugging code");
               if Debug_Trace_Untangle_Fields then
                  Write_Str ("Early delegation return: ");
                  Print_Node_Set (Vars);
                  Outdent;
               end if;
               pragma Annotate (Xcov, Exempt_Off);
            end return;
         end if;

         --  Ok, so the root is an entire object, so we can untangle it further

         pragma
           Assert
             (Nkind (Root_Node)
              in N_Identifier | N_Expanded_Name | N_Target_Name);

         --  Set the Current_Field to the object (or its component) that is is
         --  being untangled. Likewise, set Comp_Id to the index of the current
         --  component that is being untangled. ??? Actually, Comp_Id could be
         --  a function of the Current_Field; see the Loop_Invariant below.

         if Nkind (Root_Node) = N_Target_Name then
            Comp_Id :=
              (if Target_Name.Kind = Direct_Mapping
               then 1
               else Positive (Target_Name.Component.Length) + 1);
            Current_Field := Target_Name;
         else
            declare
               Root_Entity : constant Entity_Id := Entity (Root_Node);

               pragma
                 Assert
                   (Ekind (Root_Entity)
                    in E_Constant
                     | E_Variable
                     | E_Loop_Parameter -- for cursors
                     | Formal_Kind
                    or else
                      (Ekind (Root_Entity) in E_Discriminant | E_Component
                       and then
                         Is_Concurrent_Type
                           (Sinfo.Nodes.Scope (Root_Entity))));

            begin
               if Is_Protected_Component (Root_Entity) then
                  Comp_Id := 2;
                  Current_Field :=
                    Add_Component
                      (Direct_Mapping_Id (Sinfo.Nodes.Scope (Root_Entity)),
                       Root_Entity);

               elsif Is_Part_Of_Concurrent_Object (Root_Entity) then
                  Comp_Id := 2;
                  Current_Field :=
                    Add_Component
                      (Direct_Mapping_Id
                         (Etype (Encapsulating_State (Root_Entity))),
                       Root_Entity);

               else
                  Comp_Id := 1;
                  Current_Field :=
                    Direct_Mapping_Id (Unique_Entity (Root_Entity));
               end if;
            end;
         end if;

         --  We set up an identity map of all fields of the original record.
         --  For example a record with two fields would produce this kind of
         --  map:
         --
         --     r.x -> r.x
         --     r.y -> r.y

         for F of Flatten_Variable (Current_Field, Scope) loop
            declare
               Root_Entity : constant Entity_Id :=
                 Get_Direct_Mapping_Id (Current_Field);
               Alias       : constant Entity_Id :=
                 (if Ekind (Root_Entity) = E_Variable
                  then Ultimate_Overlaid_Entity (Root_Entity)
                  else Empty);

               Inserted : Boolean;
               Position : Flow_Id_Maps.Cursor;
               --  We first insert key into the map and later fill its value

            begin
               M.Insert (F, Position, Inserted);
               pragma Assert (Inserted);

               --  Handle overlays

               if Present (Alias) then

                  --  Reading an overlaid constant without variable input is
                  --  represented as reading no data.

                  if Ekind (Alias) = E_Constant
                    and then not Has_Variable_Input (Alias)
                  then
                     pragma Assert (M (Position).Is_Empty);

                  --  Other overlays are represented as reading the entire
                  --  overlaid object.

                  else
                     M (Position) := Flatten_Variable (Alias, Scope);
                  end if;

               --  Likewise for ordinary constants without variable inputs

               elsif Ekind (Root_Entity) = E_Constant
                 and then not Has_Variable_Input (Root_Entity)
               then
                  pragma Assert (M (Position).Is_Empty);

               --  Finally, ordinary reads are represented as an identity map

               else
                  M (Position).Insert (F);
               end if;
            end;
         end loop;

         pragma Annotate (Xcov, Exempt_On, "Debugging code");
         if Debug_Trace_Untangle_Fields then
            Print_Flow_Map (M);
         end if;
         pragma Annotate (Xcov, Exempt_Off);

         --  We then process Seq (the sequence of actions we have been asked to
         --  take) and update the map or eliminate entries from it.
         --
         --  = Update =
         --  For example, if we get an update 'Update (y => z) then we change
         --  the map accordingly:
         --
         --     r.x -> r.x
         --     r.y -> z
         --
         --  = Selection =
         --  Otherwise, we trim down the map. For example .y will throw away
         --  any entries in the map that are not related:
         --
         --     r.y -> z
         --
         --  Once we have processed all actions, then the set of relevant
         --  variables remains in all elements of the map. In this example,
         --  just `z'.

         --  Comp_Id is maintained by this loop and refers to the next
         --  component index. The Current_Field is also maintained and refers
         --  to the field we're at right now. For example after
         --     R'Update (...).X'Update (...).Z
         --  has been processed, then Comp_Id = 3 and Current_Field = R.X.Z.
         --
         --  We use this to check which entries to update or trim in the map.
         --  For trimming we use Comp_Id, for updating we use Current_Field.

         --  Finally a note about function folding: on each update we merge all
         --  variables used in All_Vars so that subsequent trimmings don't
         --  eliminate them. Depends_Vars however is assembled at the end of
         --  the fully trimmed map. (Note N709-009 will also need to deal with
         --  proof variables here.)

         for N of Seq loop
            pragma
              Loop_Invariant
                (Comp_Id
                 = (if Current_Field.Kind = Direct_Mapping
                    then 1
                    else Positive (Current_Field.Component.Length) + 1));

            pragma Annotate (Xcov, Exempt_On, "Debugging code");
            if Debug_Trace_Untangle_Fields then
               Write_Str ("Processing: ");
               Print_Node_Briefly (N);
            end if;
            pragma Annotate (Xcov, Exempt_Off);

            case Nkind (N) is
               when N_Delta_Aggregate      =>
                  pragma Annotate (Xcov, Exempt_On, "Debugging code");
                  if Debug_Trace_Untangle_Fields then
                     Write_Str ("Updating the map at ");
                     Sprint_Flow_Id (Current_Field);
                     Write_Eol;
                  end if;
                  pragma Annotate (Xcov, Exempt_Off);

                  Untangle_Delta_Fields (Component_Associations (N));

               when N_Attribute_Reference  =>
                  pragma Assert (Is_Attribute_Update (N));
                  pragma Assert (List_Length (Expressions (N)) = 1);

                  pragma Annotate (Xcov, Exempt_On, "Debugging code");
                  if Debug_Trace_Untangle_Fields then
                     Write_Str ("Updating the map at ");
                     Sprint_Flow_Id (Current_Field);
                     Write_Eol;
                  end if;
                  pragma Annotate (Xcov, Exempt_Off);

                  Untangle_Delta_Fields
                    (Component_Associations (First (Expressions (N))));

               when N_Selected_Component   =>
                  declare
                     Comp : constant Entity_Id :=
                       Unique_Component (Entity (Selector_Name (N)));

                     New_Map : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;

                  begin
                     --  We trim the result map

                     pragma Annotate (Xcov, Exempt_On, "Debugging code");
                     if Debug_Trace_Untangle_Fields then
                        Write_Str ("Trimming for: ");
                        Sprint_Node_Inline (Comp);
                        Write_Eol;
                     end if;
                     pragma Annotate (Xcov, Exempt_Off);

                     for C in M.Iterate loop
                        declare
                           K : Flow_Id renames Flow_Id_Maps.Key (C);
                           V : Flow_Id_Sets.Set renames M (C);

                        begin
                           if K.Kind = Record_Field
                             and then Natural (K.Component.Length) >= Comp_Id
                             and then K.Component (Comp_Id) = Comp
                           then
                              New_Map.Insert (K, V);
                           end if;
                        end;
                     end loop;

                     Flow_Id_Maps.Move (Target => M, Source => New_Map);

                     Current_Field := Add_Component (Current_Field, Comp);
                     Comp_Id := Comp_Id + 1;
                  end;

               when N_Type_Conversion      =>
                  declare
                     New_T     : constant Entity_Id :=
                       Get_Type (Etype (N), Scope);
                     Old_T     : constant Entity_Id :=
                       Get_Type (Etype (Expression (N)), Scope);
                     Same_Priv : constant Boolean :=
                       (if not Is_Tagged_Type (Old_T)
                        then True
                        elsif Is_Ancestor (Old_T, New_T, Scope)
                        then
                          not Introduces_Private_Fields (New_T, Old_T, Scope)
                        elsif Is_Ancestor (New_T, Old_T, Scope)
                        then
                          not Introduces_Private_Fields (Old_T, New_T, Scope)
                        else False);
                     --  Normally, one of Old_T and New_T is an ancestor of the
                     --  other. However, when we peek into declarations of
                     --  nested packages without adjusting the visibility,
                     --  we can encounter conversions for which this
                     --  derivation is not visible.

                     New_Comps : Flow_Id_Sets.Set;
                     The_Ext   : constant Flow_Id :=
                       (Current_Field with delta Facet => Extension_Part);
                     The_Priv  : constant Flow_Id :=
                       (Current_Field with delta Facet => Private_Part);
                     Default   : Flow_Id_Sets.Set;
                     New_Map   : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;
                  begin
                     for K of
                       Flatten_Variable (Direct_Mapping_Id (New_T), Scope)
                     loop
                        New_Comps.Insert (Join (Current_Field, K));
                     end loop;

                     if Is_Tagged_Type (New_T) then
                        New_Comps.Include (The_Ext);
                     end if;

                     --  Go over M to remove additional components not present
                     --  in New_T. Merge their inputs into default.

                     for C in M.Iterate loop
                        declare
                           K : Flow_Id renames Flow_Id_Maps.Key (C);
                           V : Flow_Id_Sets.Set renames M (C);

                        begin
                           --  The conversion might be from or to an ancestor
                           --  type. In the first case, the extension might
                           --  flow into missing components and the private
                           --  part. In the second case, the private part and
                           --  additional components might flow into the
                           --  extension.  Handle both cases at once by merging
                           --  the extension and the private part into Default
                           --  and back again.  The case where both type have
                           --  the same private part is handled specifically
                           --  for more precision.

                           if not New_Comps.Contains (K)
                             or else K = The_Ext
                             or else (not Same_Priv and K = The_Priv)
                           then
                              Default.Union (V);
                           else
                              New_Map.Insert (K, V);
                              New_Comps.Delete (K);
                           end if;
                        end;
                     end loop;

                     --  Add missing components from New_T. They depend on
                     --  Default.

                     for K of New_Comps loop
                        New_Map.Insert (K, Default);
                     end loop;

                     M.Move (Source => New_Map);
                  end;

               when N_Qualified_Expression =>
                  null;

               when others                 =>
                  raise Why.Unexpected_Node;
            end case;

            pragma Annotate (Xcov, Exempt_On, "Debugging code");
            if Debug_Trace_Untangle_Fields then
               Print_Flow_Map (M);
            end if;
            pragma Annotate (Xcov, Exempt_Off);
         end loop;

         --  We merge what is left after trimming

         for S of M loop
            Depends_Vars.Union (S);
         end loop;

         pragma Annotate (Xcov, Exempt_On, "Debugging code");
         if Debug_Trace_Untangle_Fields then
            Write_Str ("Final (all) set: ");
            Print_Node_Set (All_Vars);
            Write_Str ("Final (depends) set: ");
            Print_Node_Set (Depends_Vars);
            Write_Str ("Final (proof) set: ");
            Print_Node_Set (Proof_Vars);

            Outdent;
            Write_Eol;
         end if;
         pragma Annotate (Xcov, Exempt_Off);

         --  proof variables (requires N709-009)

         if Fold_Functions = Inputs then
            return Depends_Vars;
         else
            return All_Vars;
         end if;
      end Untangle_Record_Fields;

      ------------------------------------------------
      -- Subprograms that *do* write into Variables --
      ------------------------------------------------

      Variables : Flow_Id_Sets.Set;

      function Proc (N : Node_Id) return Traverse_Result;
      --  Adds each identifier or defining_identifier found to Variables, as
      --  long as we are dealing with:
      --     * a variable
      --     * a subprogram parameter
      --     * a loop parameter
      --     * a constant

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Ignored_In_SPARK                                   =>
               return Skip;

            when N_Entry_Call_Statement
               | N_Function_Call
               | N_Procedure_Call_Statement                           =>
               pragma
                 Assert
                   (not Ctx.Assume_In_Expression
                    or else Nkind (N) = N_Function_Call);

               Variables.Union (Do_Subprogram_Call (N));
               return Skip;

            --  Operator nodes represent calls to intrinsic subprograms, which
            --  we assume to have Global => null. Variables referenced as
            --  operator parameters will be picked when processing their own
            --  nodes.

            when N_Op                                                 =>
               pragma Assert (Is_Intrinsic_Subprogram (Entity (N)));

            when N_Abstract_Subprogram_Declaration
               | N_Entry_Body
               | N_Entry_Declaration
               | N_Package_Declaration
               | N_Proper_Body
               | N_Single_Task_Declaration
               | N_Subprogram_Declaration
               | N_Task_Type_Declaration                              =>
               pragma Assert (not Ctx.Assume_In_Expression);

               --  These should allow us to go through package specs and bodies
               return Skip;

            when N_Identifier | N_Expanded_Name                       =>
               if Present (Entity (N)) then

                  --  When detecting variable inputs and seeing an internal
                  --  variable (which comes from inlining for proof), recurse
                  --  into the original expression.

                  if Ekind (Entity (N)) = E_Variable
                    and then Is_Internal (Entity (N))
                    and then Ctx.Expand_Internal_Objects
                  then
                     pragma Assert (Is_Rewrite_Substitution (N));
                     Variables.Union (Recurse (Original_Node (N)));

                  --  For flow it is better to consider variables captured by
                  --  internal constants introduced when processing actions.

                  elsif Ekind (Entity (N)) = E_Constant
                    and then Is_Action (Parent (Entity (N)))
                  then
                     pragma
                       Assert
                         (Comes_From_Declare_Expr (Entity (N))
                          or else not Comes_From_Source (Entity (N)));
                     Variables.Union
                       (Recurse (Expression (Parent (Entity (N)))));

                  elsif Is_Type (Entity (N))
                    and then Nkind (Parent (N)) = N_Slice
                  then
                     declare
                        R : constant Node_Id :=
                          Get_Range (Discrete_Range (Parent (N)));
                     begin
                        Variables.Union (Recurse (Low_Bound (R)));
                        Variables.Union (Recurse (High_Bound (R)));
                     end;

                  else
                     --  Within expressions, type identifiers are processed
                     --  depending on the context. We can only traverse them
                     --  when this routine is executed in a special mode for
                     --  statements.

                     pragma
                       Assert
                         (if Is_Type (Entity (N))
                          then not Ctx.Assume_In_Expression);

                     Variables.Union (Do_Entity (Entity (N)));
                  end if;
               end if;
               return Skip;

            --  Within expressions, a defining identifier only appears as a
            --  declaration for a compiler-generated temporary or as a
            --  parameter of a quantified expression (effectively, it declares
            --  a local object). Such identifiers are not considered as "uses"
            --  of any variable, so we ignore them.
            --
            --  ??? we also get here type indentifiers, when Get_Variables
            --  is called on an entire type declaration and not just on its
            --  constraint expressions; such calls of Get_Variables feel wrong.

            when N_Defining_Identifier                                =>
               if Is_Type (N) then
                  Variables.Union (Do_Entity (N));
               else
                  pragma
                    Assert
                      (Is_Internal (N) or else Is_Quantified_Loop_Param (N));
               end if;

            --  ??? Previously Traverse_Proc, as opposed to Traverse_More_Proc,
            --  didn't visit actions for short-circuit and if/case-expressions.
            --  Ignore these actions until this is discussed with the frontend.

            when N_Subtype_Declaration | N_Object_Declaration         =>
               pragma
                 Assert
                   (not Ctx.Assume_In_Expression
                    or else Is_Actions_Entity (Defining_Identifier (N)));

               if Is_Actions_Entity (Defining_Identifier (N)) then
                  return Skip;
               end if;

            when N_Aggregate                                          =>
               if Is_Array_Type (Etype (N)) then
                  declare
                     Array_Bounds : constant Node_Id := Aggregate_Bounds (N);
                  begin
                     if Present (Array_Bounds) then
                        Variables.Union (Recurse (Low_Bound (Array_Bounds)));
                        Variables.Union (Recurse (High_Bound (Array_Bounds)));
                     end if;
                  end;
               end if;

               --  Include variables from the default values that correspond to
               --  boxes in aggregate expressions.

               declare
                  Assoc     : Node_Id;
                  Aggr_Type : constant Entity_Id := Get_Type (N, Ctx.Scope);
                  Any_Boxes : Boolean := False;
                  Comp_Type : Entity_Id;
                  Def_Expr  : Node_Id;
               begin
                  Assoc := First (Component_Associations (N));
                  while Present (Assoc) loop
                     --  Each component must be associated with either a box
                     --  or an expression. Expressions are detected and handled
                     --  elsewhere.
                     pragma
                       Assert
                         (Box_Present (Assoc)
                          xor Present (Expression (Assoc)));

                     if Box_Present (Assoc) then
                        Any_Boxes := True;
                        exit;
                     end if;
                     Next (Assoc);
                  end loop;
                  --  ??? Record components are handled properly by the
                  --  Untangle_... machinery. Consider similar machinery
                  --  for array types.
                  if Any_Boxes and then Is_Array_Type (Aggr_Type) then
                     Comp_Type := Component_Type (Aggr_Type);
                     if Has_Discriminants (Comp_Type) then
                        for C of Iter (Discriminant_Constraint (Comp_Type))
                        loop
                           Variables.Union (Recurse (C));
                        end loop;
                     end if;

                     for F of Flatten_Variable (Comp_Type, Ctx.Scope) loop
                        Def_Expr := Get_Default_Initialization (F);
                        if Present (Def_Expr) then
                           --  Discriminant dependencies from default
                           --  expressions are managed above.
                           Variables.Union
                             (Ignore_Record_Type_Discriminants
                                (Recurse (Def_Expr)));
                        end if;
                     end loop;
                  end if;
               end;

            when N_Delta_Aggregate                                    =>
               declare
                  T : constant Entity_Id := Get_Type (N, Ctx.Scope);
               begin
                  if Is_Record_Type (T) then
                     Variables.Union (Untangle_With_Context (N));
                     return Skip;
                  else
                     pragma Assert (Is_Array_Type (T));

                     if Is_Deep_Delta_Aggregate (N) then

                        --  Pick variables from the base expression

                        Variables.Union (Recurse (Expression (N)));

                        --  Pick variables from the array component association
                        --  list.

                        declare
                           Assoc  : Node_Id;
                           Choice : Node_Id;
                           Expr   : Node_Id;
                           Pref   : Node_Id;
                        begin
                           Assoc := First (Component_Associations (N));
                           while Present (Assoc) loop

                              Choice := First (Choices (Assoc));
                              while Present (Choice) loop
                                 pragma Assert (Is_Deep_Choice (Choice, T));
                                 Pref := Choice;
                                 while not Is_Root_Prefix_Of_Deep_Choice (Pref)
                                 loop
                                    --  Pick variables from the index
                                    --  expressions.

                                    if Nkind (Pref) = N_Indexed_Component then
                                       Expr := First (Expressions (Pref));
                                       while Present (Expr) loop
                                          Variables.Union (Recurse (Expr));
                                          Next (Expr);
                                       end loop;

                                    else
                                       pragma
                                         Assert
                                           (Nkind (Pref)
                                            = N_Selected_Component);
                                    end if;
                                    Pref := Prefix (Pref);
                                 end loop;

                                 Variables.Union (Recurse (Pref));

                                 Next (Choice);
                              end loop;

                              Variables.Union (Recurse (Expression (Assoc)));

                              Next (Assoc);
                           end loop;
                        end;
                        return Skip;
                     end if;
                  end if;
               end;

            when N_Selected_Component                                 =>
               if Is_Subprogram_Or_Entry (Entity (Selector_Name (N))) then

                  --  ??? We are only getting here in the dubious mode that
                  --  originates from First_Variable_Use.

                  pragma Assert (not Ctx.Assume_In_Expression);

                  --  Here we are dealing with a call of a protected
                  --  entry/function. This appears on the tree as a selected
                  --  component of the protected object.

                  Variables.Union (Recurse (Prefix (N)));

               else
                  Variables.Union (Untangle_With_Context (N));
               end if;
               return Skip;

            when N_Type_Conversion                                    =>
               if Is_Record_Type (Get_Type (N, Ctx.Scope)) then
                  --  We use Untangle_Record_Assignment as this can deal with
                  --  view conversions.

                  declare
                     M : constant Flow_Id_Maps.Map :=
                       Untangle_Record_Assignment
                         (N,
                          Map_Root                =>
                            Direct_Mapping_Id (Etype (N)),
                          Map_Type                => Get_Type (N, Ctx.Scope),
                          Target_Name             => Ctx.Target_Name,
                          Scope                   => Ctx.Scope,
                          Fold_Functions          => Ctx.Fold_Functions,
                          Use_Computed_Globals    => Ctx.Use_Computed_Globals,
                          Expand_Internal_Objects =>
                            Ctx.Expand_Internal_Objects,
                          Extensions_Irrelevant   =>
                            not Ctx.Consider_Extensions);

                  begin
                     for FS of M loop
                        Variables.Union (FS);
                     end loop;
                  end;
               else
                  Variables.Union (Recurse (Expression (N)));
               end if;

               return Skip;

            when N_Attribute_Reference                                =>
               Variables.Union (Do_Attribute_Reference (N));
               return Skip;

            when N_Case_Expression_Alternative                        =>
               --  We special case case_expression_alternative because their
               --  discrete_choice_list may include subtype_indication, whose
               --  processing depends on the context. Here only subtypes with
               --  static bounds can appear and those can be safely ignored.

               Variables.Union (Recurse (Expression (N)));
               return Skip;

            when N_Component_Association                              =>
               declare
                  Choice : Node_Id := First (Choices (N));
               begin
                  loop
                     --  Record component choice; it always appears as a name
                     --  of a component or of a discriminant, "(C => ...)".

                     if Nkind (Choice) in N_Identifier | N_Expanded_Name
                       and then
                         Ekind (Entity (Choice))
                         in E_Component | E_Discriminant
                     then
                        null;

                     --  Array component choice; it appears in various forms

                     --  "(Low .. High => ...)"

                     elsif Nkind (Choice) = N_Range then
                        Variables.Union (Recurse (Low_Bound (Choice)));
                        Variables.Union (Recurse (High_Bound (Choice)));

                     --  "(A_Subtype range Low .. High => ...)"

                     elsif Nkind (Choice) = N_Subtype_Indication then
                        declare
                           R : constant Node_Id :=
                             Range_Expression (Constraint (Choice));
                        begin
                           Variables.Union (Recurse (Low_Bound (R)));
                           Variables.Union (Recurse (High_Bound (R)));
                        end;

                     --  "(A_Subtype => ...)"

                     elsif Is_Entity_Name (Choice)
                       and then Is_Type (Entity (Choice))
                     then
                        Variables.Union
                          (Recurse (Type_Low_Bound (Entity (Choice))));
                        Variables.Union
                          (Recurse (Type_High_Bound (Entity (Choice))));

                     --  "(others => ...)"

                     elsif Nkind (Choice) = N_Others_Choice then
                        null;

                     --  "(1 => ...)" or "(X + Y => ...)", etc.

                     elsif Nkind (Choice) in N_Subexpr then
                        Variables.Union (Recurse (Choice));

                     else
                        raise Program_Error;
                     end if;

                     Next (Choice);
                     exit when No (Choice);
                  end loop;
               end;

               if Box_Present (N) then
                  --  Default component expression managed at the level of
                  --  the aggregate expression.
                  null;
               else
                  --  Avoid <Record Type>.Discriminant constructs from default
                  --  expressions.
                  Variables.Union
                    (Ignore_Record_Type_Discriminants
                       (Recurse (Expression (N))));
               end if;

               return Skip;

            when N_Membership_Test                                    =>
               --  Membership tests involving type with predicates have the
               --  predicate flow into the variable set returned.

               declare
                  procedure Process_Predicate_Expression
                    (Type_Instance   : Formal_Kind_Id;
                     Pred_Expression : Node_Id);
                  --  Merge predicate function for the given type

                  procedure Process_Type (E : Entity_Id);
                  --  Handle what Ada RM 4.5.2 describes as "membership_choice
                  --  is a subtype_mark" and what GNAT implements in routine
                  --  Exp_Ch4.Expand_N_In.

                  procedure Process_Predicates is new
                    Iterate_Applicable_Predicates
                      (Process_Predicate_Expression);

                  ----------------------------------
                  -- Process_Predicate_Expression --
                  ----------------------------------

                  procedure Process_Predicate_Expression
                    (Type_Instance : Formal_Kind_Id; Pred_Expression : Node_Id)
                  is
                  begin
                     --  Filter predicate function parameter from variables
                     --  referenced in the predicate, because the parameter is
                     --  only visible within that expression (similar to what
                     --  we do for quantified expression).

                     for V of Recurse (Pred_Expression) loop
                        if V.Kind in Direct_Mapping | Record_Field
                          and then V.Node = Type_Instance
                        then
                           null;
                        else
                           Variables.Include (V);
                        end if;
                     end loop;
                  end Process_Predicate_Expression;

                  ------------------
                  -- Process_Type --
                  ------------------

                  procedure Process_Type (E : Entity_Id) is
                     Typ : constant Entity_Id :=
                       (if Is_Access_Type (E) then Designated_Type (E) else E);

                  begin
                     --  For scalar types recurse on their bounds

                     if Is_Scalar_Type (E) then
                        declare
                           Rng : constant Node_Id := Scalar_Range (E);
                        begin
                           Variables.Union (Recurse (Low_Bound (Rng)));
                           Variables.Union (Recurse (High_Bound (Rng)));
                        end;

                     --  For constrained composite types (and for access to
                     --  such types) recurse on their constraints, because the
                     --  membership test checks the equality of array bounds
                     --  (for arrays) and of discriminants (for other composite
                     --  types).

                     elsif Is_Constrained (Typ) then
                        if Is_Array_Type (Typ) then
                           declare
                              Index : Node_Id := First_Index (Typ);
                           begin
                              loop
                                 Variables.Union
                                   (Recurse (Type_Low_Bound (Etype (Index))));
                                 Variables.Union
                                   (Recurse (Type_High_Bound (Etype (Index))));

                                 Next_Index (Index);
                                 exit when No (Index);
                              end loop;
                           end;
                        elsif Has_Discriminants (Typ) then
                           for C of Iter (Discriminant_Constraint (Typ)) loop
                              Variables.Union (Recurse (C));
                           end loop;
                        end if;
                     end if;

                     --  Recurse on the predicate expressions, if any

                     Process_Predicates (Typ);

                  end Process_Type;

                  P : Node_Id;

               begin
                  Variables.Union (Recurse (Left_Opnd (N)));

                  if Present (Right_Opnd (N)) then

                     --  x in t

                     P := Right_Opnd (N);
                     if Is_Entity_Name (P) and then Is_Type (Entity (P)) then
                        Process_Type (Get_Type (P, Ctx.Scope));
                     else
                        Variables.Union (Recurse (P));
                     end if;

                  else

                     --  x in t | 1 .. y | u

                     P := First (Alternatives (N));
                     loop
                        if Is_Entity_Name (P) and then Is_Type (Entity (P))
                        then
                           Process_Type (Get_Type (P, Ctx.Scope));
                        else
                           Variables.Union (Recurse (P));
                        end if;
                        Next (P);

                        exit when No (P);
                     end loop;
                  end if;
               end;
               return Skip;

            when N_Qualified_Expression | N_Unchecked_Type_Conversion =>
               Variables.Union (Recurse (Expression (N)));
               return Skip;

            when N_Quantified_Expression                              =>
               declare
                  pragma
                    Assert
                      (Present (Iterator_Specification (N))
                       xor Present (Loop_Parameter_Specification (N)));

                  E : constant Entity_Id :=
                    Defining_Identifier
                      (if Present (Iterator_Specification (N))
                       then Iterator_Specification (N)
                       else Loop_Parameter_Specification (N));

                  Filter : constant Node_Id :=
                    Iterator_Filter
                      (if Present (Iterator_Specification (N))
                       then Iterator_Specification (N)
                       else Loop_Parameter_Specification (N));
               begin
                  if Present (Iterator_Specification (N)) then
                     Variables.Union
                       (Recurse (Name (Iterator_Specification (N))));
                  else
                     declare
                        R : constant Node_Id :=
                          Get_Range
                            (Discrete_Subtype_Definition
                               (Loop_Parameter_Specification (N)));

                     begin
                        Variables.Union (Recurse (Low_Bound (R)));
                        Variables.Union (Recurse (High_Bound (R)));
                     end;
                  end if;

                  --  Filter the quantified expression parameter from variables
                  --  referenced in the iterator filter, if present, because
                  --  the parameter is only visible within that predicate
                  --  (similar to what we do for type predicate expressions).

                  if Present (Filter) then
                     for V of Recurse (Filter) loop
                        if V.Kind in Direct_Mapping | Record_Field
                          and then V.Node = E
                        then
                           null;
                        else
                           Variables.Include (V);
                        end if;
                     end loop;
                  end if;

                  --  Filter the quantified expression parameter from variables
                  --  referenced in the predicate, because the parameter is
                  --  only visible within that predicate.

                  for V of Recurse (Condition (N)) loop
                     if V.Kind in Direct_Mapping | Record_Field
                       and then V.Node = E
                     then
                        null;
                     else
                        Variables.Include (V);
                     end if;
                  end loop;
               end;
               return Skip;

            when N_Iterated_Component_Association                     =>

               pragma
                 Assert
                   (Present (Defining_Identifier (N))
                    and then No (Iterator_Specification (N)));

               declare
                  Choice : Node_Id := First (Discrete_Choices (N));
               begin
                  loop
                     --  Choices in array component appear in various forms:
                     --  "(Low .. High => ...)"
                     --  "(A_Subtype range Low .. High => ...)"
                     --  "(A_Subtype => ...)"
                     if Nkind (Choice) = N_Range
                       or else Nkind (Choice) = N_Subtype_Indication
                       or else
                         (Is_Entity_Name (Choice)
                          and then Is_Type (Entity (Choice)))
                     then
                        declare
                           R : constant Node_Id := Get_Range (Choice);
                        begin
                           Variables.Union (Recurse (Low_Bound (R)));
                           Variables.Union (Recurse (High_Bound (R)));
                        end;

                     --  "(others => ...)"

                     elsif Nkind (Choice) = N_Others_Choice then
                        null;

                     --  "(1 => ...)" or "(X + Y => ...)", etc.

                     elsif Nkind (Choice) in N_Subexpr then
                        Variables.Union (Recurse (Choice));

                     else
                        raise Program_Error;
                     end if;

                     Next (Choice);
                     exit when No (Choice);
                  end loop;
               end;

               declare
                  E : constant Entity_Id := Defining_Identifier (N);
               begin

                  --  Filter the iterated component association parameter
                  --  from variables referenced in the expression, because the
                  --  parameter is only visible within that expression
                  --  (similar to what we do for type predicate expressions
                  --  or quantified expressions).

                  for V of Recurse (Expression (N)) loop
                     if V.Kind in Direct_Mapping | Record_Field
                       and then V.Node = E
                     then
                        null;
                     else
                        Variables.Include (V);
                     end if;
                  end loop;
               end;
               return Skip;

            when N_Slice                                              =>
               declare
                  R : constant Node_Id := Get_Range (Discrete_Range (N));
               begin
                  Variables.Union (Recurse (Low_Bound (R)));
                  Variables.Union (Recurse (High_Bound (R)));
               end;
               Variables.Union (Recurse (Prefix (N)));
               return Skip;

            when N_Allocator                                          =>
               declare
                  Expr : constant Node_Id := Expression (N);
               begin
                  --  If the allocated expression is just a type name, then
                  --  pull dependencies coming from default expressions.

                  if Is_Entity_Name (Expr) and then Is_Type (Entity (Expr))
                  then
                     declare
                        E        : constant Node_Id := Entity (Expr);
                        Typ      : constant Entity_Id :=
                          (if Is_Access_Type (E)
                           then Designated_Type (E)
                           else E);
                        Def_Expr : Node_Id;

                     begin
                        if Has_Discriminants (Typ) then
                           for C of Iter (Discriminant_Constraint (Typ)) loop
                              Variables.Union (Recurse (C));
                           end loop;
                        end if;
                        for F of Flatten_Variable (E, Ctx.Scope) loop
                           Def_Expr := Get_Default_Initialization (F);
                           if Present (Def_Expr) then
                              --  Dependencies coming from record discriminant
                              --  constraints and default initializations have
                              --  already been pulled above. Other discriminant
                              --  dependencies can only come from the
                              --  dependency of inner discriminants on outer
                              --  ones (which don't add new dependencies) so
                              --  filter them out here.
                              Variables.Union
                                (Ignore_Record_Type_Discriminants
                                   (Recurse (Def_Expr)));
                           end if;
                        end loop;
                     end;
                     --  Subpools are not currently allowed in SPARK, but make
                     --  sure that we don't forget to traverse them if they
                     --  become allowed.

                     pragma Assert (No (Subpool_Handle_Name (N)));

                     return Skip;
                  else
                     return OK;
                  end if;
               end;

            --  A declare expression (see Ada RM 4.5.9) consists of a set of
            --  declare items and a body_expression. We recurse into each
            --  part in turn.

            when N_Expression_With_Actions                            =>

               --  The declare items include object declarations and object
               --  renaming declarations; process these depending on the
               --  context's Fold_Function component.
               declare
                  procedure Process_Actions (Fold_Functions : Reference_Kind);
                  --  Helper procedure to process the expression's actions

                  ---------------------
                  -- Process_Actions --
                  ---------------------

                  procedure Process_Actions (Fold_Functions : Reference_Kind)
                  is
                     Action : Node_Id := First (Actions (N));
                  begin
                     while Present (Action) loop
                        case Nkind (Action) is
                           when N_Object_Declaration          =>
                              Variables.Union
                                (Recurse
                                   (N              => Expression (Action),
                                    Fold_Functions => Fold_Functions));

                           when N_Object_Renaming_Declaration =>
                              Variables.Union
                                (Recurse
                                   (N              => Name (Action),
                                    Fold_Functions => Fold_Functions));

                           --  The frontend should have rejected all other code
                           --  constructs. Therefore anything else we find in
                           --  this action list has been synthesised so we
                           --  ignore it.

                           when others                        =>
                              pragma Assert (not Comes_From_Source (Action));
                        end case;
                        Next (Action);
                     end loop;
                  end Process_Actions;
               begin
                  case Ctx.Fold_Functions is

                     --  Variables referenced in object declarations do not
                     --  flow into inputs.

                     when Inputs    =>
                        null;

                     --  Proof inputs need to be pulled

                     when Proof_Ins =>
                        Process_Actions (Fold_Functions => Proof_Ins);

                     --  Anything evaluated is referenced as a null dependency;
                     --  it will be pulled when referenced.

                     when Null_Deps =>
                        Process_Actions (Fold_Functions => Inputs);
                        Process_Actions (Fold_Functions => Null_Deps);
                  end case;

               end;

               --  And now the expression itself
               Variables.Union (Recurse (Expression (N)));
               return Skip;

            when N_Target_Name                                        =>
               if Ctx.Fold_Functions = Inputs then
                  Variables.Union
                    (Flatten_Variable (Ctx.Target_Name, Ctx.Scope));
               end if;
               return Skip;

            when others                                               =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);
      --  While finding objects referenced within an expression we ignore
      --  actions (by instantiating Traverse_Proc and not Traverse_More_Proc),
      --  because actions contain constructs that can't appear in expressions,
      --  e.g. itype declarations. We ignore those constructs so that we can
      --  have more assertions, e.g. about subtype names that can only appear
      --  in specific contexts.

      --  Start of processing for Get_Variables_Internal

   begin
      Traverse (N);

      --  Sanity check: no constants without variable inputs should come from
      --  the traversal.
      pragma
        Assert
          (for all V of Variables =>
             (if V.Kind in Direct_Mapping | Record_Field
                and then Ekind (V.Node) = E_Constant
                and then not Is_Access_Variable (Etype (V.Node))
              then Has_Variable_Input (V.Node)));

      Map_Generic_In_Formals (Ctx.Scope, Variables, Entire => False);

      return Variables;
   end Get_Variables_Internal;

   -----------------------------
   -- Get_Variables_For_Proof --
   -----------------------------

   function Get_Variables_For_Proof
     (Expr_N : Node_Id; Scope_N : Node_Id; Skip_Old : Boolean := False)
      return Flow_Id_Sets.Set
   is
      function Enclosing_Declaration_Or_Statement (N : Node_Id) return Node_Id;
      --  Return the nearest enclosing declaration or statement that houses
      --  arbitrary node N.
      --  ??? This is copy-pasted from sem_res.adb; refactor

      function Resolve_Target_Name
        (N : Node_Id; Scope : Flow_Scope) return Flow_Id
      with Pre => Nkind (N) in N_Subexpr;
      --  If the node N is a subexpression of an assignment statement with
      --  target_names, it returns the Flow_Id of the object represented by
      --  those target_names. This routine is needed to adapt proof (which asks
      --  for variables referenced by arbitrary subexpressions) to flow (which
      --  keeps track what target_name represents as part of its context info).

      ----------------------------------------
      -- Enclosing_Declaration_Or_Statement --
      ----------------------------------------

      function Enclosing_Declaration_Or_Statement (N : Node_Id) return Node_Id
      is
         Par : Node_Id;

      begin
         Par := N;
         while Present (Par) loop
            if Is_Declaration (Par) or else Is_Statement (Par) then
               return Par;

            --  Prevent the search from going too far

            elsif Is_Body_Or_Package_Declaration (Par) then
               exit;
            end if;

            Par := Parent (Par);
         end loop;

         return N;
      end Enclosing_Declaration_Or_Statement;

      -------------------------
      -- Resolve_Target_Name --
      -------------------------

      function Resolve_Target_Name
        (N : Node_Id; Scope : Flow_Scope) return Flow_Id
      is
         Stmt : constant Node_Id := Enclosing_Declaration_Or_Statement (N);
      begin
         if Nkind (Stmt) = N_Assignment_Statement
           and then Has_Target_Names (Stmt)
         then
            return Path_To_Flow_Id (Name (Stmt), Scope);
         else
            return Null_Flow_Id;
         end if;
      end Resolve_Target_Name;

      --  Local variables
      Entire_Variables : Flow_Id_Sets.Set;
      Scope            : constant Flow_Scope := Get_Flow_Scope (Scope_N);
      Target_Name      : constant Flow_Id :=
        Resolve_Target_Name (Expr_N, Scope);

      --  Start of processing for Get_Variables_For_Proof

   begin
      --  Ignore references to array bounds of objects (because they are never
      --  mutable).

      for V of
        Get_All_Variables
          (Expr_N,
           Scope                   => Scope,
           Target_Name             => Target_Name,
           Use_Computed_Globals    => True,
           Assume_In_Expression    => True,
           Expand_Internal_Objects => False,
           Skip_Old                => Skip_Old)
      loop
         if not Is_Bound (V) then
            Entire_Variables.Include (Entire_Variable (V));
         end if;
      end loop;

      return Expand_Abstract_States (Entire_Variables);
   end Get_Variables_For_Proof;

   -----------------
   -- Has_Depends --
   -----------------

   function Has_Depends (Subprogram : Entity_Id) return Boolean is
   begin
      return Present (Find_Contract (Subprogram, Pragma_Depends));
   end Has_Depends;

   ------------------------
   -- Has_Variable_Input --
   ------------------------

   function Has_Variable_Input (C : Entity_Id) return Boolean is
   begin
      --  If the answer has already been memoized, then return it

      declare
         Position : constant Entity_To_Boolean_Maps.Cursor :=
           Variable_Input_Map.Find (C);
         --  This cursor must be declared in a local block, so that it
         --  disappears before we might recursively call this routine via
         --  Has_Variable_Input_Internal. It would be illegal to do Insert in
         --  that recursive call while the above cursor is alive.

      begin
         if Entity_To_Boolean_Maps.Has_Element (Position) then
            return Variable_Input_Map (Position);
         end if;
      end;

      --  Otherwise, compute answer and memoize it

      declare
         Answer : constant Boolean := Has_Variable_Input_Internal (C);

      begin
         Variable_Input_Map.Insert (Key => C, New_Item => Answer);

         return Answer;
      end;
   end Has_Variable_Input;

   ---------------------------------
   -- Has_Variable_Input_Internal --
   ---------------------------------

   function Has_Variable_Input_Internal (C : Entity_Id) return Boolean is
      E    : Entity_Id;
      Expr : Node_Id;
      Vars : Flow_Id_Sets.Set;

   begin
      --  This routine is mirrored in Direct_Inputs_Of_Constant; any change
      --  here should be reflected there.
      --  ??? ideally, this should be refactored

      if Is_Imported (C) then
         --  If we are dealing with an imported constant, we consider this to
         --  have potentially variable input.
         return True;
      end if;

      Expr := Expression (Declaration_Node (C));
      if Present (Expr) then
         E := C;
      else
         --  We are dealing with a deferred constant so we need to get to the
         --  full view.
         E := Full_View (C);
         Expr := Expression (Declaration_Node (E));
      end if;

      if not Entity_In_SPARK (E) then
         --  We are dealing with an entity that is not in SPARK so we assume
         --  that it does not have variable input.
         return False;
      end if;

      Vars :=
        Get_Variables
          (Expr,
           Scope                => Get_Flow_Scope (E),
           Target_Name          => Null_Flow_Id,
           Fold_Functions       => Inputs,
           Use_Computed_Globals => GG_Has_Been_Generated);
      --  Note that Get_Variables calls Has_Variable_Input when it finds a
      --  constant. This means that there might be some mutual recursion here
      --  (but this should be fine).

      if Vars.Is_Empty then

         --  With Global contracts in place, Get_Variables result is trusted

         if GG_Has_Been_Generated then
            return False;

         --  Without Global contracts we conservatively assume that any
         --  unannotated function might read a variable.

         else
            --  ??? this code is duplicated in Direct_Inputs_Of_Constant

            return
              (for some F of
                 Get_Functions (Expr, Include_Predicates => False) =>
                 not Has_User_Supplied_Globals (F)
                 and then not Is_Ignored_Internal (F));
         end if;

      --  If any variable was found then return True

      else
         return True;
      end if;

   end Has_Variable_Input_Internal;

   ----------------
   -- Has_Bounds --
   ----------------

   function Has_Bounds (F : Flow_Id; Scope : Flow_Scope) return Boolean is
      T : Entity_Id;
   begin
      if F.Kind = Direct_Mapping then
         T := Get_Type (F.Node, Scope);

         return Is_Array_Type (T) and then not Is_Constrained (T);
      else
         return False;
      end if;
   end Has_Bounds;

   --------------------------------------
   -- Ignore_Record_Type_Discriminants --
   --------------------------------------

   function Ignore_Record_Type_Discriminants
     (Vars_Used : Flow_Id_Sets.Set) return Flow_Id_Sets.Set
   is
      Results : Flow_Id_Sets.Set;
   begin
      for Var_Used of Vars_Used loop
         if Is_Discriminant (Var_Used)
           and then Ekind (Get_Direct_Mapping_Id (Var_Used)) = E_Record_Type
         then
            null; --  Filter it out

         else
            Results.Insert (Var_Used);
         end if;
      end loop;

      return Results;
   end Ignore_Record_Type_Discriminants;

   -------------------------------
   -- Introduces_Private_Fields --
   -------------------------------

   function Introduces_Private_Fields
     (Ty : Entity_Id; Anc : Entity_Id; Scope : Flow_Scope) return Boolean
   is
      B_Anc : constant Entity_Id := Get_Type (Base_Type (Anc), Scope);
      S_Anc : constant Entity_Id :=
        (if Is_Class_Wide_Type (B_Anc)
         then Get_Specific_Type_From_Classwide (B_Anc, Scope)
         else B_Anc);
      T     : Entity_Id :=
        (if Is_Class_Wide_Type (Ty)
         then Get_Specific_Type_From_Classwide (Base_Type (Ty), Scope)
         else Ty);
   begin
      loop
         T := Get_Type (Base_Type (T), Scope);

         if T = S_Anc then
            return False;
         elsif Is_Private_Type (T) then
            return True;
         end if;
         T := Ancestor (T);
         pragma Assert (Present (T));
      end loop;
   end Introduces_Private_Fields;

   -----------------
   -- Is_Ancestor --
   -----------------

   function Is_Ancestor
     (Anc : Entity_Id; Ty : Entity_Id; Scope : Flow_Scope) return Boolean
   is
      B_Anc : constant Entity_Id := Get_Type (Base_Type (Anc), Scope);
      S_Anc : constant Entity_Id :=
        (if Is_Class_Wide_Type (B_Anc)
         then Get_Specific_Type_From_Classwide (B_Anc, Scope)
         else B_Anc);
      T     : Entity_Id :=
        (if Is_Class_Wide_Type (Ty)
         then Get_Specific_Type_From_Classwide (Base_Type (Ty), Scope)
         else Ty);
   begin
      loop
         T := Get_Type (Base_Type (T), Scope);

         if T = S_Anc then
            return True;
         end if;
         T := Ancestor (T);
         exit when No (T);
      end loop;
      return False;
   end Is_Ancestor;

   ----------------------------------
   -- Is_Assertion_Level_Dependent --
   ----------------------------------

   function Is_Assertion_Level_Dependent
     (Self : Flow_Id; Other : Flow_Id) return Boolean is
   begin
      pragma Assert (Self.Kind in Direct_Mapping | Magic_String);
      pragma Assert (Other.Kind in Direct_Mapping | Magic_String);

      --  Call the apropriate routine depening on the kind of inputs

      if Self.Kind = Direct_Mapping and then Other.Kind = Direct_Mapping then
         return
           Is_Assertion_Level_Dependent
             (Ghost_Assertion_Level (Get_Direct_Mapping_Id (Self)),
              Ghost_Assertion_Level (Get_Direct_Mapping_Id (Other)));
      elsif Self.Kind = Direct_Mapping and then Other.Kind = Magic_String then
         return
           GG_Is_Assertion_Level_Dependent
             (Ghost_Assertion_Level (Get_Direct_Mapping_Id (Self)),
              GG_Ghost_Assertion_Level (Other.Name));
      elsif Self.Kind = Magic_String and then Other.Kind = Direct_Mapping then
         return
           GG_Is_Assertion_Level_Dependent
             (GG_Ghost_Assertion_Level (Self.Name),
              Ghost_Assertion_Level (Get_Direct_Mapping_Id (Other)));
      else
         return
           GG_Is_Assertion_Level_Dependent
             (GG_Ghost_Assertion_Level (Self.Name),
              GG_Ghost_Assertion_Level (Other.Name));
      end if;
   end Is_Assertion_Level_Dependent;

   ---------------------
   -- Is_Ghost_Entity --
   ---------------------

   function Is_Ghost_Entity (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            return Is_Ghost_Entity (Get_Direct_Mapping_Id (F));

         when Magic_String                  =>
            return GG_Is_Ghost_Entity (F.Name);

         when others                        =>
            return False;
      end case;
   end Is_Ghost_Entity;

   -----------------------------
   -- Is_Checked_Ghost_Entity --
   -----------------------------

   function Is_Checked_Ghost_Entity (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            return Is_Checked_Ghost_Entity (Get_Direct_Mapping_Id (F));

         when Magic_String                  =>
            return GG_Is_Checked_Ghost_Entity (F.Name);

         when others                        =>
            return False;
      end case;
   end Is_Checked_Ghost_Entity;

   -----------------------------
   -- Is_Ignored_Ghost_Entity --
   -----------------------------

   function Is_Ignored_Ghost_Entity (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            return Is_Ignored_Ghost_Entity (Get_Direct_Mapping_Id (F));

         when Magic_String                  =>
            return GG_Is_Ignored_Ghost_Entity (F.Name);

         when others                        =>
            return False;
      end case;
   end Is_Ignored_Ghost_Entity;

   -----------------------------------
   -- Is_Constant_After_Elaboration --
   -----------------------------------

   function Is_Constant_After_Elaboration (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);

            begin
               return
                 Ekind (E) = E_Variable
                 and then Is_Constant_After_Elaboration (E);
            end;

         when Magic_String   =>
            return GG_Is_CAE_Entity (F.Name);

         when others         =>
            raise Program_Error;
      end case;
   end Is_Constant_After_Elaboration;

   --------------------------------
   -- Calls_Dispatching_Equality --
   --------------------------------

   function Calls_Dispatching_Equality (N : Node_Id) return Boolean is
   begin
      case Nkind (N) is

         --  On a function call, the usual routine works correctly

         when N_Function_Call   =>
            pragma Assert (Is_Tagged_Predefined_Eq (Get_Called_Entity (N)));

            return Flow_Classwide.Is_Dispatching_Call (N);

         --  On a membership test, if the left operand is a class-wide type
         --  and the right operand includes at least a constant or variable,
         --  then the equality function is called and it dispatches.

         when N_Membership_Test =>

            if Is_Class_Wide_Type (Etype (Left_Opnd (N))) then
               declare
                  P : Node_Id;

               begin
                  if Present (Right_Opnd (N)) then
                     P := Right_Opnd (N);
                     return Alternative_Uses_Eq (P);

                  else
                     --  x in t | 1 .. y | u
                     P := First (Alternatives (N));
                     loop
                        if Alternative_Uses_Eq (P) then
                           return True;
                        end if;
                        Next (P);

                        exit when No (P);
                     end loop;
                  end if;
               end;
            end if;

            return False;

         --  On an operator, the equality dispatchs if one of the operands is
         --  of a class-wide type.

         when N_Op_Eq | N_Op_Ne =>

            return
              Is_Class_Wide_Type (Etype (Left_Opnd (N)))
              or else Is_Class_Wide_Type (Etype (Right_Opnd (N)));

         when others            =>
            raise Program_Error;
      end case;
   end Calls_Dispatching_Equality;

   -----------------------------------
   -- Is_Initialized_At_Elaboration --
   -----------------------------------

   function Is_Initialized_At_Elaboration
     (F : Flow_Id; S : Flow_Scope) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            return
              Is_Initialized_At_Elaboration (Get_Direct_Mapping_Id (F), S);

         when Magic_String                  =>
            return GG_Is_Initialized_At_Elaboration (F.Name);

         when Synthetic_Null_Export         =>
            return False;

         when Null_Value                    =>
            raise Program_Error;
      end case;
   end Is_Initialized_At_Elaboration;

   -------------------------------------
   -- Is_Initialized_In_Specification --
   -------------------------------------

   function Is_Initialized_In_Specification
     (F : Flow_Id; S : Flow_Scope) return Boolean
   is
      pragma Unreferenced (S);
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               case Ekind (E) is
                  when E_Abstract_State =>
                     return False;

                  when others           =>
                     pragma Assert (Nkind (Parent (E)) = N_Object_Declaration);
                     return Present (Expression (Parent (E)));

               end case;
            end;

         when Magic_String                  =>
            --  The fact it is a Magic_String instead of an entity means that
            --  it comes from another compilation unit (via an indirect call)
            --  and therefore has to have already been elaborated.
            return True;

         when others                        =>
            raise Program_Error;
      end case;
   end Is_Initialized_In_Specification;

   --------------------------------
   -- Is_Valid_Assignment_Target --
   --------------------------------

   function Is_Valid_Assignment_Target (N : Node_Id) return Boolean is
      Ptr : Node_Id := N;
   begin
      while Nkind (Ptr) in Valid_Assignment_Kinds loop
         case Valid_Assignment_Kinds (Nkind (Ptr)) is
            --  ??? Check the return for dereference

            when N_Identifier | N_Expanded_Name                  =>
               return True;

            when N_Type_Conversion | N_Unchecked_Type_Conversion =>
               Ptr := Expression (Ptr);

            when N_Indexed_Component
               | N_Slice
               | N_Selected_Component
               | N_Explicit_Dereference                          =>
               Ptr := Prefix (Ptr);
         end case;
      end loop;
      return False;
   end Is_Valid_Assignment_Target;

   -----------------
   -- Is_Variable --
   -----------------

   function Is_Variable (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               if Ekind (E) = E_Constant then
                  return
                    Is_Access_Variable (Etype (E))
                    or else Has_Variable_Input (E);
               else
                  return True;
               end if;
            end;

         when Magic_String                  =>
            return True;

         --  Consider anything that is not a Direct_Mapping or a Record_Field
         --  to be a variable.

         when Synthetic_Null_Export         =>
            return True;

         when Null_Value                    =>
            raise Program_Error;
      end case;
   end Is_Variable;

   --------------------
   -- Is_Constituent --
   --------------------

   function Is_Constituent (N : Node_Id) return Boolean
   is (Nkind (N) in N_Entity
       and then Ekind (N) in E_Abstract_State | E_Constant | E_Variable
       and then Present (Encapsulating_State (N))
       and then Ekind (Encapsulating_State (N)) = E_Abstract_State);

   -----------------------------
   -- Is_Implicit_Constituent --
   -----------------------------

   function Is_Implicit_Constituent (N : Node_Id) return Boolean is

      function In_Body_Or_Private_Part (Item : Node_Id) return Boolean
      with Pre => Nkind (Item) in N_Object_Declaration | N_Package_Declaration;
      --  Returns True if Item is declared in body or private part of a
      --  package, or in a private desendant of a library-level pacakge.

      -----------------------------
      -- In_Body_Or_Private_Part --
      -----------------------------

      function In_Body_Or_Private_Part (Item : Node_Id) return Boolean is
         Context : constant Node_Id := Parent (Item);
      begin
         case Nkind (Context) is
            when N_Package_Body          =>
               pragma Assert (List_Containing (Item) = Declarations (Context));
               return True;

            when N_Package_Specification =>
               if List_Containing (Item) = Private_Declarations (Context) then
                  return True;

               elsif List_Containing (Item) = Visible_Declarations (Context)
               then
                  return In_Body_Or_Private_Part (Parent (Context));

               else
                  raise Program_Error;
               end if;

            --  Compilation unit may contain a package where objects are
            --  declared, but it won't contain the objects themselves.

            when N_Compilation_Unit      =>
               pragma Assert (Nkind (Item) = N_Package_Declaration);
               return Is_Private_Descendant (Defining_Entity (Item));

            when others                  =>
               return False;
         end case;
      end In_Body_Or_Private_Part;

   begin
      return
        Nkind (N) in N_Entity
        and then Ekind (N) in E_Constant | E_Variable
        and then Ekind (Scope (N)) = E_Package
        and then No (Encapsulating_State (N))
        and then In_Body_Or_Private_Part (Parent (N));
   end Is_Implicit_Constituent;

   -----------------------
   -- Is_Abstract_State --
   -----------------------

   function Is_Abstract_State (N : Node_Id) return Boolean
   is (Nkind (N) in N_Entity and then Ekind (N) = E_Abstract_State);

   ----------
   -- Join --
   ----------

   function Join (A, B : Flow_Id; Offset : Natural := 0) return Flow_Id is
      F : Flow_Id := A;
      N : Natural := 0;
   begin
      if B.Kind = Record_Field then
         for C of B.Component loop
            if N >= Offset then
               F := Add_Component (F, C);
            end if;
            N := N + 1;
         end loop;
      end if;
      F.Facet := B.Facet;
      return F;
   end Join;

   ------------------------------
   -- Rely_On_Generated_Global --
   ------------------------------

   function Rely_On_Generated_Global
     (E : Entity_Id; Scope : Flow_Scope) return Boolean is
   begin
      return
        Entity_Body_In_SPARK (E)
        and then Is_Visible (Get_Body (E), Scope)
        and then Refinement_Needed (E);
   end Rely_On_Generated_Global;

   ----------------------
   -- Remove_Constants --
   ----------------------

   procedure Remove_Constants (Objects : in out Flow_Id_Sets.Set) is
      Constants : Flow_Id_Sets.Set;
      --  ??? list would be more efficient here, since we only Insert and
      --  Iterate, but sets are more intuitive; for now let's leave it.
   begin
      for F of Objects loop
         case F.Kind is
            when Direct_Mapping | Record_Field =>
               declare
                  E : constant Entity_Id := Get_Direct_Mapping_Id (F);

               begin
                  if Ekind (E) = E_Constant
                    and then not Is_Access_Variable (Etype (E))
                    and then not Has_Variable_Input (E)
                  then
                     Constants.Insert (F);
                  end if;
               end;

            when Magic_String                  =>
               null;

            when Synthetic_Null_Export         =>
               null;

            when Null_Value                    =>
               raise Program_Error;
         end case;
      end loop;

      Objects.Difference (Constants);
   end Remove_Constants;

   ----------------------------------------------
   -- Is_Generic_Actual_Without_Variable_Input --
   ----------------------------------------------

   function Is_Generic_Actual_Without_Variable_Input
     (E : Entity_Id) return Boolean
   is (Ekind (E) = E_Constant
       and then In_Generic_Actual (E)
       and then not Is_Access_Variable (Etype (E))
       and then not Has_Variable_Input (E));

   ---------------------
   -- First_Name_Node --
   ---------------------

   function First_Name_Node (N : Node_Id) return Node_Id is
      Name : Node_Id := N;
   begin
      while Nkind (Name) = N_Expanded_Name loop
         Name := Prefix (Name);
      end loop;

      return Name;
   end First_Name_Node;

   -----------------------------
   -- Search_Depends_Contract --
   -----------------------------

   function Search_Depends_Contract
     (Unit : Entity_Id; Output : Entity_Id; Input : Entity_Id := Empty)
      return Node_Id
   is

      Contract_N : Node_Id;

      Needle : Node_Id := Empty;
      --  A node where the message about an "Output => Input" dependency should
      --  be located.

      procedure Scan_Contract (N : Node_Id);
      --  Scan contract looking for "Output => Input" dependency

      procedure Find_Output (N : Node_Id)
      with Pre => Nkind (N) = N_Component_Association;
      --  Find node that corresponds to the Output entity

      procedure Find_Input (N : Node_Id);
      --  Find node that corresponds to the Input entity

      -----------------
      -- Find_Output --
      -----------------

      procedure Find_Output (N : Node_Id) is
         Item : constant Node_Id := First (Choices (N));
         pragma Assert (List_Length (Choices (N)) = 1);

      begin
         --  Note: N_Numeric_Or_String_Literal can only appear on the RHS of a
         --  dependency clause; frontend rejects it if it appears on the LHS.

         case Nkind (Item) is
            --  Handle a clause like "null => ...", which must be the last one

            when N_Null                         =>
               if No (Output) then
                  Needle := Item;
                  if Present (Input) then
                     Find_Input (Expression (N));
                  end if;
                  return;
               end if;

            --  Handle clauses like "X => ..." and "X.Y => ..."

            when N_Identifier | N_Expanded_Name =>
               if Canonical_Entity (Entity (Item), Unit) = Output then
                  Needle := First_Name_Node (Item);
                  if Present (Input) then
                     Find_Input (Expression (N));
                  end if;
                  return;
               end if;

            --  Handle clauses like "X'Result => ..." and "X.Y'Result => ..."

            when N_Attribute_Reference          =>
               pragma Assert (Attribute_Name (Item) = Name_Result);

               if Entity (Prefix (Item)) = Output then
                  Needle := First_Name_Node (Prefix (Item));
                  if Present (Input) then
                     Find_Input (Expression (N));
                  end if;
                  return;
               end if;

            --  Handle clauses like "(X, X.Y, Z'Result, Z.Y'Result) => ..."

            when N_Aggregate                    =>
               declare
                  Single_Item : Node_Id := First (Expressions (Item));

               begin
                  loop
                     case Nkind (Single_Item) is
                        when N_Identifier | N_Expanded_Name =>
                           if Canonical_Entity (Entity (Single_Item), Unit)
                             = Output
                           then
                              Needle := First_Name_Node (Single_Item);
                              if Present (Input) then
                                 Find_Input (Expression (N));
                              end if;
                              return;
                           end if;

                        when N_Attribute_Reference          =>
                           pragma
                             Assert
                               (Attribute_Name (Single_Item) = Name_Result);

                           if Entity (Prefix (Single_Item)) = Output then
                              Needle := First_Name_Node (Prefix (Single_Item));
                              if Present (Input) then
                                 Find_Input (Expression (N));
                              end if;
                              return;
                           end if;

                        when others                         =>
                           raise Program_Error;
                     end case;

                     Next (Single_Item);

                     exit when No (Single_Item);
                  end loop;
               end;

            when others                         =>
               raise Program_Error;

         end case;
      end Find_Output;

      ----------------
      -- Find_Input --
      ----------------

      procedure Find_Input (N : Node_Id) is
      begin
         case Nkind (N) is
            when N_Null                         =>
               --  ??? a null RHS is syntactically possible, but this routine
               --  is not called in that case.
               raise Program_Error;

            --  Handle contracts like "... => X" and "... => X.Y"

            when N_Identifier | N_Expanded_Name =>
               if Canonical_Entity (Entity (N), Unit) = Input then
                  Needle := First_Name_Node (N);
               end if;

            --  Handle contracts like "... => (X, X.Y)"

            when N_Aggregate                    =>
               declare
                  Item : Node_Id := First (Expressions (N));

               begin
                  loop
                     pragma
                       Assert (Nkind (Item) in N_Identifier | N_Expanded_Name);

                     if Canonical_Entity (Entity (Item), Unit) = Input then
                        Needle := First_Name_Node (Item);
                        return;
                     end if;

                     Next (Item);

                     exit when No (Item);
                  end loop;
               end;

            when others                         =>
               raise Program_Error;
         end case;
      end Find_Input;

      -------------------
      -- Scan_Contract --
      -------------------

      procedure Scan_Contract (N : Node_Id) is
      begin
         case Nkind (N) is
            --  Handle empty contract, i.e. "null"

            when N_Null      =>
               return;

            --  Handle non-empty contracts, e.g. "... => ..., ... => ..."

            when N_Aggregate =>

               declare
                  Clause : Node_Id := First (Component_Associations (N));

               begin
                  loop
                     Find_Output (Clause);

                     exit when Present (Needle);

                     Next (Clause);

                     exit when No (Clause);
                  end loop;
               end;

            when others      =>
               raise Program_Error;
         end case;
      end Scan_Contract;

      --  Start of processing for Search_Depends_Contract

   begin
      Contract_N := Find_Contract (Unit, Pragma_Refined_Depends);

      if No (Contract_N) then
         Contract_N := Find_Contract (Unit, Pragma_Depends);
      end if;

      if Present (Contract_N) then

         Scan_Contract (Expression (Get_Argument (Contract_N, Unit)));

         return (if Present (Needle) then Needle else Contract_N);
      else
         return Unit;
      end if;

   end Search_Depends_Contract;

   ---------------------------------
   -- Search_Initializes_Contract --
   ---------------------------------

   function Search_Initializes_Contract
     (Unit : Entity_Id; Output : Entity_Id; Input : Entity_Id := Empty)
      return Node_Id
   is
      Contract : constant Node_Id := Get_Pragma (Unit, Pragma_Initializes);

      Needle : Node_Id := Empty;
      --  A node where the message about an "Output => Input" dependency should
      --  be located.

      procedure Scan_Initialization_Spec (Inits : Node_Id);
      --  Scan the initialization_spec of a Initializes contract

      procedure Scan_Initialization_Item (Item : Node_Id)
      with Pre => Nkind (Item) in N_Identifier | N_Expanded_Name;
      --  Scan an initialization clause of the form "X"

      procedure Scan_Initialization_Item_With_Inputs (N : Node_Id)
      with Pre => Nkind (N) = N_Component_Association;
      --  Scan an initialization clause of the form "X => ..."

      procedure Scan_Inputs (N : Node_Id);
      --  Scan the RHS of an initialization clause of the form "... => ..."

      ------------------------------
      -- Scan_Initialization_Item --
      ------------------------------

      procedure Scan_Initialization_Item (Item : Node_Id) is
      begin
         if Canonical_Entity (Entity (Item), Unit) = Output then
            Needle := First_Name_Node (Item);
         end if;
      end Scan_Initialization_Item;

      ------------------------------------------
      -- Scan_Initialization_Item_With_Inputs --
      ------------------------------------------

      procedure Scan_Initialization_Item_With_Inputs (N : Node_Id) is
         LHS : constant Node_Id := First (Choices (N));
         pragma Assert (List_Length (Choices (N)) = 1);

      begin
         pragma Assert (Nkind (LHS) in N_Identifier | N_Expanded_Name);

         if Canonical_Entity (Entity (LHS), Unit) = Output then
            Needle := First_Name_Node (LHS);

            if Present (Input) then
               Scan_Inputs (Expression (N));
            end if;
         end if;
      end Scan_Initialization_Item_With_Inputs;

      ------------------------------
      -- Scan_Initialization_Spec --
      ------------------------------

      procedure Scan_Initialization_Spec (Inits : Node_Id) is
         Init : Node_Id;

      begin
         case Nkind (Inits) is
            --  Null initialization list

            when N_Null      =>
               Needle := Inits;
               return;

            --  Clauses appear as component associations of an aggregate

            when N_Aggregate =>

               --  Handle clauses like "X"

               if Present (Expressions (Inits)) then
                  Init := First (Expressions (Inits));
                  loop
                     Scan_Initialization_Item (Init);

                     if Present (Needle) then
                        return;
                     end if;

                     Next (Init);
                     exit when No (Init);
                  end loop;
               end if;

               --  Handle clauses like "X => ..."

               if Present (Component_Associations (Inits)) then
                  Init := First (Component_Associations (Inits));
                  loop
                     Scan_Initialization_Item_With_Inputs (Init);

                     if Present (Needle) then
                        return;
                     end if;

                     Next (Init);
                     exit when No (Init);
                  end loop;
               end if;

            when others      =>
               raise Program_Error;
         end case;
      end Scan_Initialization_Spec;

      -----------------
      -- Scan_Inputs --
      -----------------

      procedure Scan_Inputs (N : Node_Id) is
      begin
         case Nkind (N) is

            --  Handle input like "... => X" and "... => X.Y"

            when N_Identifier | N_Expanded_Name =>
               if Canonical_Entity (Entity (N), Unit) = Input then
                  Needle := First_Name_Node (N);
               end if;

            --  Handle aggregate inputs like "... => (X, Y)"

            when N_Aggregate                    =>
               declare
                  RHS : Node_Id := First (Expressions (N));

               begin
                  loop
                     pragma
                       Assert (Nkind (RHS) in N_Identifier | N_Expanded_Name);

                     if Canonical_Entity (Entity (RHS), Unit) = Input then
                        Needle := First_Name_Node (RHS);
                        return;
                     end if;

                     Next (RHS);

                     exit when No (RHS);
                  end loop;
               end;

            when others                         =>
               raise Program_Error;

         end case;
      end Scan_Inputs;

      --  Start of processing for Search_Initializes_Contract

   begin
      if Present (Contract) then
         Scan_Initialization_Spec (Expression (Get_Argument (Contract, Unit)));

         return (if Present (Needle) then Needle else Contract);
      else
         return Unit;
      end if;

   end Search_Initializes_Contract;

   ------------------------
   -- Termination_Proved --
   ------------------------

   function Termination_Proved
     (I_Scheme           : Opt_N_Iteration_Scheme_Id;
      Loop_Writes        : Flow_Id_Sets.Set;
      Generating_Globals : Boolean := False) return Boolean is
   begin
      --  Termination of plain or while loops is not automatically proved

      if No (I_Scheme) or else Present (Condition (I_Scheme)) then
         return False;

      --  Termination of loops over a type or range is proved

      elsif Present (Loop_Parameter_Specification (I_Scheme)) then
         return True;

      elsif Present (Iterator_Specification (I_Scheme)) then
         declare
            I_Name : constant Node_Id :=
              Name (Iterator_Specification (I_Scheme));
         begin
            --  Loops over array always terminate
            if Is_Iterator_Over_Array (Iterator_Specification (I_Scheme))

              --  If the name is not a path, then we iterate over something
              --  constant.
              or else not Is_Path_Expression (I_Name)

              --  If we have no root object, then we iterate over an
              --  object created by an allocator, which we cannot modify
              --  during the loop.
              or else No (Get_Root_Object (I_Name))

              --  If the root object is a constant, it cannot be modified
              --  during the loop.
              or else Is_Constant_In_SPARK (Get_Root_Object (I_Name))

              --  Otherwise, if we are in phase 2 (i.e. we know exactly all
              --  loop writes), we check that the root object is not
              --  modified during the loop. Get_Root_Object will always
              --  return entire variables.
              or else
                (not Generating_Globals
                 and then
                   not Loop_Writes.Contains
                         (Direct_Mapping_Id (Get_Root_Object (I_Name))))
            then
               return True;
            end if;
         end;
      else
         raise Program_Error;
      end if;

      return False;
   end Termination_Proved;

   --------------------
   -- To_Flow_Id_Set --
   --------------------

   function To_Flow_Id_Set
     (NS : Name_Sets.Set; View : Flow_Id_Variant := Normal_Use)
      return Flow_Id_Sets.Set
   is
      FS : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for N of NS loop
         FS.Insert (Get_Flow_Id (N, View));
      end loop;

      return FS;
   end To_Flow_Id_Set;

   --------------------------------
   -- Untangle_Record_Assignment --
   --------------------------------

   function Untangle_Record_Assignment
     (N                       : Node_Id;
      Map_Root                : Flow_Id;
      Map_Type                : Entity_Id;
      Target_Name             : Flow_Id;
      Scope                   : Flow_Scope;
      Fold_Functions          : Reference_Kind;
      Use_Computed_Globals    : Boolean;
      Expand_Internal_Objects : Boolean;
      Extensions_Irrelevant   : Boolean;
      Top_Level               : Boolean := True) return Flow_Id_Maps.Map
   is
      --  !!! Join/Merge need to be able to deal with private parts and
      --      extensions (i.e. non-normal facets).

      function Get_Vars_Wrapper (N : Node_Id) return Flow_Id_Sets.Set
      is (Get_Variables
            (N,
             Scope                   => Scope,
             Target_Name             => Target_Name,
             Fold_Functions          => Fold_Functions,
             Use_Computed_Globals    => Use_Computed_Globals,
             Expand_Internal_Objects => Expand_Internal_Objects))
      with Pre => Nkind (N) in N_Subexpr;
      --  Helpful wrapper for calling Get_Variables

      function Recurse_On
        (N              : Node_Id;
         Map_Root       : Flow_Id;
         Map_Type       : Entity_Id := Empty;
         Ext_Irrelevant : Boolean := Extensions_Irrelevant)
         return Flow_Id_Maps.Map
      is (Untangle_Record_Assignment
            (N,
             Map_Root                => Map_Root,
             Map_Type                =>
               (if Present (Map_Type) then Map_Type else Get_Type (N, Scope)),
             Target_Name             => Target_Name,
             Scope                   => Scope,
             Fold_Functions          => Fold_Functions,
             Use_Computed_Globals    => Use_Computed_Globals,
             Expand_Internal_Objects => Expand_Internal_Objects,
             Extensions_Irrelevant   => Ext_Irrelevant,
             Top_Level               => False))
      with
        Pre =>
          Nkind (N) in N_Subexpr
          and then (if not Extensions_Irrelevant then not Ext_Irrelevant);
      --  Helpful wrapper for recursing. Note that once extensions are not
      --  irrelevant its not right to start ignoring them again.

      procedure Merge
        (M : in out Flow_Id_Maps.Map; Component : Entity_Id; Input : Node_Id)
      with
        Pre =>
          Is_Unique_Component (Component)
          and then (No (Input) or else Nkind (Input) in N_Subexpr);
      --  Merge the assignment map for Input into our current assignment
      --  map M. For example, if the input is (X => A, Y => B) and
      --  Component is C, and Map_Root is Obj, then we include in M the
      --  following: Obj.C.X => A, Obj.C.Y => B.
      --
      --  If Input is not some kind of record, we simply include a single
      --  field. For example if the input is simply Foo, then (all other
      --  things being equal to the example above) we include Obj.C => Foo.
      --
      --  If the Input is Empty (because we're looking at a box in an
      --  aggregate), then we add an empty map entry for it.

      function Untangle_Delta_Aggregate
        (Pref : Node_Id; Assocs : List_Id) return Flow_Id_Maps.Map
      with Pre => Is_Non_Empty_List (Assocs);
      --  Untangle delta aggregate or attribute Update
      --  ??? Pre should include "Is_Object_Reference (Pref)", but currently
      --  it would fail on nested delta aggregates (TA01-056).

      procedure Apply_Conversion
        (T_From : Entity_Id;
         T_To   : Entity_Id;
         Source : Flow_Id_Maps.Map;
         Target : in out Flow_Id_Maps.Map);
      --  Convert the map Source of type T_From to a map for an object of type
      --  T_To.

      ----------------------
      -- Apply_Conversion --
      ----------------------

      procedure Apply_Conversion
        (T_From : Entity_Id;
         T_To   : Entity_Id;
         Source : Flow_Id_Maps.Map;
         Target : in out Flow_Id_Maps.Map)
      is
         Valid_To_Fields : Flow_Id_Sets.Set;

         The_Ext   : constant Flow_Id :=
           (Map_Root with delta Facet => Extension_Part);
         The_Tg    : constant Flow_Id :=
           (Map_Root with delta Facet => The_Tag);
         The_Priv  : constant Flow_Id :=
           (Map_Root with delta Facet => Private_Part);
         Same_Priv : constant Boolean :=
           (if not Is_Tagged_Type (T_To)
            then True
            elsif Is_Ancestor (T_From, T_To, Scope)
            then not Introduces_Private_Fields (T_To, T_From, Scope)
            elsif Is_Ancestor (T_To, T_From, Scope)
            then not Introduces_Private_Fields (T_From, T_To, Scope)
            else False);
         --  The private parts of From and To contains the same fields.
         --  Normally, we should always be in a case where either T_From is
         --  an ancestor of T_To or the opposite, but it might not be the case
         --  if we are peeking into private declarations of nested packages.

         Default  : Flow_Id_Sets.Set;
         Position : Flow_Id_Maps.Cursor;
         Unused   : Boolean;

      begin
         pragma Annotate (Xcov, Exempt_On, "Debugging code");
         if Debug_Trace_Untangle_Record then
            Write_Str ("from: ");
            Sprint_Node_Inline (T_From);
            Write_Str (" (" & Ekind (T_From)'Img & ")");
            Write_Str (" to: ");
            Sprint_Node_Inline (T_To);
            Write_Str (" (" & Ekind (T_To)'Img & ")");
            Write_Eol;

            Write_Str ("temporary map: ");
            Print_Flow_Map (Source);
         end if;
         pragma Annotate (Xcov, Exempt_Off);

         for F of Flatten_Variable (Direct_Mapping_Id (T_To), Scope) loop
            Valid_To_Fields.Insert (Join (Map_Root, F));
         end loop;

         if not Valid_To_Fields.Contains (The_Ext)
           and then Is_Tagged_Type (T_To)
           and then not Extensions_Irrelevant
         then
            Valid_To_Fields.Insert (The_Ext);
         end if;

         --  Handle all fields of Source but the extension. If the field is
         --  valid in T_To, then insert it in M. Otherwise, put its
         --  dependencies in Default.

         for C in Source.Iterate loop
            declare
               Output   : Flow_Id renames Flow_Id_Maps.Key (C);
               Inputs   : Flow_Id_Sets.Set renames Source (C);
               C_Target : Flow_Id_Sets.Cursor := Valid_To_Fields.Find (Output);

            begin
               if Flow_Id_Sets.Has_Element (C_Target)
                 and then Output /= The_Ext
                 and then (Output /= The_Priv or else Same_Priv)
               then
                  Target.Insert (Output, Inputs);
                  Valid_To_Fields.Delete (C_Target);
               else
                  Default.Union (Inputs);
               end if;
            end;
         end loop;

         --  If T_To is an ancestor of T_From, all the additional fields of
         --  Source flow into the extension if any. Otherwise, they might flow
         --  into the private part too if any.

         if Valid_To_Fields.Contains (The_Ext) then
            Target.Insert (The_Ext, Default);
            Valid_To_Fields.Delete (The_Ext);
         end if;

         if Valid_To_Fields.Contains (The_Priv)
           and then not Is_Ancestor (T_To, T_From, Scope)
         then
            Target.Insert (The_Priv, Default);
            Valid_To_Fields.Delete (The_Priv);
         end if;

         --  Handle the missing To fields. If T_From is an ancestor of T_To,
         --  all remaining valid fields of T_To depend on the extension of Tmp.
         --  Otherwise, they might also depend on the private part if any.

         Default.Clear;

         declare
            C : constant Flow_Id_Maps.Cursor := Source.Find (The_Ext);
         begin
            if Flow_Id_Maps.Has_Element (C) then
               Default := Source (C);
            end if;
         end;

         if Source.Contains (The_Priv)
           and then not Same_Priv
           and then not Is_Ancestor (T_From, T_To, Scope)
         then
            Default.Union (Source (The_Priv));
         end if;

         for Output of Valid_To_Fields loop
            Target.Insert (Output, Default);
         end loop;

         if Valid_To_Fields.Contains (The_Tg) then
            Target.Insert (The_Tg, Position, Unused);
         end if;
      end Apply_Conversion;

      -----------
      -- Merge --
      -----------

      procedure Merge
        (M : in out Flow_Id_Maps.Map; Component : Entity_Id; Input : Node_Id)
      is
         F   : Flow_Id := Add_Component (Map_Root, Component);
         Tmp : Flow_Id_Maps.Map;

      begin
         --  In private declarations of nested packages, it might happen that
         --  we parse an aggregate whose components are not visible in the
         --  current scope. Use the private part instead.

         if not Component_Visible_In_Type (Component, Map_Type, Scope) then
            F := (Map_Root with delta Facet => Private_Part);
            declare
               Inputs   : constant Flow_Id_Sets.Set :=
                 (if Present (Input)
                  then Get_Vars_Wrapper (Input)
                  else Flow_Id_Sets.Empty_Set);
               Position : Flow_Id_Maps.Cursor;
               Inserted : Boolean;

            begin
               M.Insert (F, Inputs, Position, Inserted);
               if not Inserted then
                  M (Position).Union (Inputs);
               end if;
            end;

         elsif Present (Input) then
            if Is_Record_Type (Get_Type (Component, Scope)) then
               Tmp := Recurse_On (Input, F);

               for C in Tmp.Iterate loop
                  declare
                     Output : Flow_Id renames Flow_Id_Maps.Key (C);
                     Inputs : Flow_Id_Sets.Set renames Tmp (C);
                  begin
                     M.Insert (Output, Inputs);
                  end;
               end loop;
            else
               declare
                  Outputs : constant Flow_Id_Sets.Set :=
                    Flatten_Variable (F, Scope);

                  Inputs : constant Flow_Id_Sets.Set :=
                    Get_Vars_Wrapper (Input);

               begin
                  for Output of Outputs loop
                     M.Insert (Output, Inputs);
                  end loop;
               end;
            end if;
         else
            for Output of Flatten_Variable (F, Scope) loop
               M.Insert (Output, Flow_Id_Sets.Empty_Set);
            end loop;
         end if;
      end Merge;

      ------------------------------
      -- Untangle_Delta_Aggregate --
      ------------------------------

      function Untangle_Delta_Aggregate
        (Pref : Node_Id; Assocs : List_Id) return Flow_Id_Maps.Map
      is
         Assoc   : Node_Id;
         Output  : Node_Id;
         Input   : Node_Id;
         F       : Flow_Id;
         Partial : Boolean;

         procedure Add_Component_To_F (C : Entity_Id; T : Type_Kind_Id);
         --  Add C to F. If F is not visible in T, add the private part instead
         --  and set Partial to True.
         --  This happens because we sometimes analyze code with the wrong
         --  visibility in the private part of nested packages.

         ------------------------
         -- Add_Component_To_F --
         ------------------------

         procedure Add_Component_To_F (C : Entity_Id; T : Type_Kind_Id) is
         begin
            if Component_Visible_In_Type (C, T, Scope) then
               F := Add_Component (F, C);
            else
               F := (F with delta facet => Private_Part);
               Partial := True;
            end if;
         end Add_Component_To_F;

         Partial_Choice_Root : Node_Id;
         Partial_Choice_Vars : Flow_Id_Sets.Set;
         --  For handling partial assignments

         Deep_Choice_Seq : Node_Lists.List;
         --  For handling deep delta aggregates

         Class_Wide_Conversion : constant Boolean :=
           not Is_Class_Wide_Type (Get_Type (N, Scope))
           and then Is_Class_Wide_Type (Map_Type);

         M : Flow_Id_Maps.Map;

      begin
         M :=
           Recurse_On
             (Pref,
              Map_Root,
              Ext_Irrelevant =>
                not (Class_Wide_Conversion or not Extensions_Irrelevant));

         Assoc := First (Assocs);
         while Present (Assoc) loop
            pragma Assert (Nkind (Assoc) = N_Component_Association);

            Input := Expression (Assoc);
            Output := First (Choices (Assoc));

            F := Map_Root;
            Partial := False;
            Partial_Choice_Root := Output;
            Deep_Choice_Seq := Node_Lists.Empty_List;

            if Sem_Aggr.Is_Deep_Choice (Output, Etype (Pref)) then

               --  Determine the root node and the sequence of its selected
               --  and indexed components.
               while not Is_Root_Prefix_Of_Deep_Choice (Partial_Choice_Root)
               loop
                  Deep_Choice_Seq.Prepend (Partial_Choice_Root);
                  Partial_Choice_Root := Prefix (Partial_Choice_Root);
               end loop;

               --  Build the assigned target Flow_Id and determine whether this
               --  is a partial update (like partially assigned arrays).

               Add_Component_To_F
                 (Unique_Component (Entity (Partial_Choice_Root)),
                  Get_Type (N, Scope));

               for N of Deep_Choice_Seq loop
                  exit when Partial;
                  case Nkind (N) is
                     when N_Selected_Component =>
                        Add_Component_To_F
                          (Unique_Component (Entity (Selector_Name (N))),
                           Get_Type (F, Scope));

                     when N_Indexed_Component  =>
                        Partial := True;
                        exit;

                     when others               =>
                        raise Program_Error;
                  end case;
               end loop;

            else
               Add_Component_To_F
                 (Unique_Component (Entity (Output)), Get_Type (N, Scope));
            end if;

            --  Partial update is handled like a self-assignment, i.e. it uses
            --  the current value, variables from the index expressions and
            --  from the input expression.

            if Partial then

               --  For a partial update collect variables from its index
               --  expressions.

               Partial_Choice_Vars := Flow_Id_Sets.Empty_Set;

               for N of Deep_Choice_Seq loop
                  case Nkind (N) is
                     when N_Selected_Component =>
                        null;

                     when N_Indexed_Component  =>
                        declare
                           Expr : Node_Id;
                        begin
                           Expr := First (Expressions (N));
                           while Present (Expr) loop
                              Partial_Choice_Vars.Union
                                (Get_Vars_Wrapper (Expr));
                              Next (Expr);
                           end loop;
                        end;

                     when others               =>
                        raise Program_Error;
                  end case;
               end loop;

               Partial_Choice_Vars.Union (M (F));
               Partial_Choice_Vars.Union (Get_Vars_Wrapper (Input));
               M.Replace (F, Partial_Choice_Vars);

            elsif Is_Record_Type (Get_Type (F, Scope)) then
               for C in Recurse_On (Input, F).Iterate loop
                  M.Replace (Flow_Id_Maps.Key (C), Flow_Id_Maps.Element (C));
               end loop;
            else
               M.Replace (F, Get_Vars_Wrapper (Input));
            end if;

            --  Multiple component choices have been rewritten into individual
            --  component associations.
            pragma Assert (No (Next (Output)));

            Next (Assoc);
         end loop;

         return M;
      end Untangle_Delta_Aggregate;

      --  Local variables

      M : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;

      --  Start of processing for Untangle_Record_Assignment

   begin
      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Debug_Trace_Untangle_Record then
         Write_Str ("URA task: ");
         Write_Str (Character'Val (8#33#) & "[1m");
         Sprint_Flow_Id (Map_Root);
         Write_Str (Character'Val (8#33#) & "[0m");
         Write_Str (" <-- ");
         Write_Str (Character'Val (8#33#) & "[1m");
         Sprint_Node_Inline (N);
         Write_Str (Character'Val (8#33#) & "[0m");
         Write_Eol;

         Indent;

         Write_Str ("Map_Type: " & Ekind (Map_Type)'Img);
         Write_Eol;
         Write_Str ("RHS_Type: " & Ekind (Etype (N))'Img);
         Write_Eol;
         Write_Str ("Ext_Irrl: " & Extensions_Irrelevant'Img);
         Write_Eol;
      end if;
      pragma Annotate (Xcov, Exempt_Off);

      --  If we are at top level, convert to the type of Map_Root

      if Top_Level then
         declare
            N_Ty    : constant Entity_Id := Get_Type (N, Scope);
            Base_Ty : constant Entity_Id := Get_Type (Map_Root, Scope);
            Tmp     : constant Flow_Id_Maps.Map := Recurse_On (N, Map_Root);
         begin
            Apply_Conversion (N_Ty, Base_Ty, Tmp, M);
         end;

         goto Result_Untangle;
      end if;

      case Nkind (N) is
         when N_Aggregate                                        =>
            pragma Assert (No (Expressions (N)));
            --  The front-end should rewrite this for us.

            pragma Annotate (Xcov, Exempt_On, "Debugging code");
            if Debug_Trace_Untangle_Record then
               Write_Str ("processing aggregate");
               Write_Eol;
            end if;
            pragma Annotate (Xcov, Exempt_Off);

            declare
               Component_Association : Node_Id;

               Input  : Node_Id;
               Target : Node_Id;

            begin
               Component_Association := First (Component_Associations (N));

               --  If it is a null record aggregate, then the entire object is
               --  assigned an empty data.

               if No (Component_Association) then
                  M.Insert (Map_Root, Flow_Id_Sets.Empty_Set);
               end if;

               while Present (Component_Association) loop
                  if Box_Present (Component_Association) then
                     Input := Empty;  -- ??? use default component expression

                  else
                     Input := Expression (Component_Association);
                  end if;

                  Target := First (Choices (Component_Association));
                  Merge
                    (M,
                     Component => Unique_Component (Entity (Target)),
                     Input     => Input);

                  --  Multiple component updates are expanded into individual
                  --  component associations.
                  pragma Assert (No (Next (Target)));

                  Next (Component_Association);
               end loop;
            end;

         when N_Delta_Aggregate                                  =>
            M :=
              Untangle_Delta_Aggregate
                (Expression (N), Component_Associations (N));

         when N_Selected_Component                               =>
            pragma Annotate (Xcov, Exempt_On, "Debugging code");
            if Debug_Trace_Untangle_Record then
               Write_Line ("processing selected component");
            end if;
            pragma Annotate (Xcov, Exempt_Off);

            declare
               Ty  : constant Entity_Id :=
                 Get_Type (Etype (Prefix (N)), Scope);
               Tmp : constant Flow_Id_Maps.Map :=
                 Recurse_On (Prefix (N), Direct_Mapping_Id (Ty));

               Selector : constant Entity_Id :=
                 Unique_Component (Entity (Selector_Name (N)));

            begin
               if Component_Visible_In_Type (Selector, Ty, Scope) then
                  for C in Tmp.Iterate loop
                     declare
                        Output : Flow_Id renames Flow_Id_Maps.Key (C);
                        Inputs : Flow_Id_Sets.Set renames Tmp (C);

                     begin
                        if Output.Component.First_Element = Selector then
                           M.Insert (Join (Map_Root, Output, 1), Inputs);
                        end if;
                     end;
                  end loop;
               else
                  declare
                     Inputs : constant Flow_Id_Sets.Set :=
                       Tmp.Element
                         ((Direct_Mapping_Id (Ty)
                           with delta facet => Private_Part));
                  begin
                     M.Insert (Map_Root, Inputs);
                  end;
               end if;
            end;

         when N_Identifier | N_Expanded_Name | N_Target_Name     =>
            pragma Annotate (Xcov, Exempt_On, "Debugging code");
            if Debug_Trace_Untangle_Record then
               Write_Str ("processing direct assignment");
               Write_Eol;
            end if;
            pragma Annotate (Xcov, Exempt_Off);

            if Nkind (N) /= N_Target_Name
              and then Comes_From_Declare_Expr (Entity (N))
            then
               --  Need to recurse into the declare expression
               M :=
                 Recurse_On
                   (N        => Expression (Declaration_Node (Entity (N))),
                    Map_Root => Map_Root);
            else
               declare
                  E : constant Entity_Id :=
                    (if Nkind (N) = N_Target_Name
                     then Get_Direct_Mapping_Id (Target_Name)
                     else Entity (N));

                  Is_Pure_Constant : constant Boolean :=
                    Fold_Functions /= Inputs
                    or else
                      (Ekind (E) = E_Constant
                       and then not Has_Variable_Input (E));
                  --  If we are assigning a pure constant, we don't really
                  --  want to see it (just like if we assign integer/string/...
                  --  literals then we don't want to see them in flow).
                  --  However, we can't just pretend that the RHS is an empty
                  --  map; it is a map (i.e. a certain structure) with empty
                  --  elements, e.g. the private extension part. Same when
                  --  we detect Proof_Ins/Null_Deps and see a plain object
                  --  reference.

                  LHS : constant Flow_Id_Sets.Set :=
                    Flatten_Variable (Map_Root, Scope);

                  LHS_Ext : constant Flow_Id :=
                    (Map_Root with delta Facet => Extension_Part);

                  LHS_Ext_Inputs   : Flow_Id_Sets.Set;
                  LHS_Ext_Position : Flow_Id_Maps.Cursor;
                  Unused           : Boolean;
                  --  LHS extension, its inputs and position in the map

                  RHS : Flow_Id_Sets.Set :=
                    (if Nkind (N) = N_Target_Name
                     then Flatten_Variable (Target_Name, Scope)

                     elsif Is_Concurrent_Component_Or_Discr (E)
                     then
                       Flatten_Variable
                         (Add_Component
                            (Direct_Mapping_Id (Sinfo.Nodes.Scope (E)), E),
                          Scope)

                     elsif Is_Part_Of_Concurrent_Object (E)
                     then
                       Flatten_Variable
                         (Add_Component
                            (Direct_Mapping_Id
                               (Etype (Encapsulating_State (E))),
                             E),
                          Scope)

                     elsif Ekind (E) = E_Variable
                       and then Present (Ultimate_Overlaid_Entity (E))
                     then
                       Flatten_Variable (Ultimate_Overlaid_Entity (E), Scope)

                     else Flatten_Variable (E, Scope));

               begin
                  if (Is_Class_Wide_Type (Map_Type)
                      and then not Is_Class_Wide_Type (Etype (N)))
                    or else not Extensions_Irrelevant
                  then
                     --  This is an implicit conversion to class wide, or we
                     --  for some other reason care specifically about the
                     --  extensions.

                     case Nkind (N) is
                        when N_Target_Name                  =>
                           if Extensions_Visible (Target_Name, Scope) then
                              RHS.Insert
                                ((Target_Name
                                  with delta Facet => Extension_Part));

                           --  RHS.Insert
                           --    ((Target_Name with delta
                           --         Facet => The_Tag));

                           end if;

                        when N_Identifier | N_Expanded_Name =>
                           if Extensions_Visible (E, Scope) then
                              RHS.Insert
                                (Direct_Mapping_Id
                                   (E, Facet => Extension_Part));

                           --  RHS.Insert
                           --    (Direct_Mapping_Id (E, Facet => The_Tag));

                           end if;

                        when others                         =>
                           raise Program_Error;
                     end case;
                  end if;

                  for Input of RHS loop
                     declare
                        F : constant Flow_Id :=
                          Join
                            (Map_Root,
                             Input,
                             Offset =>
                               (if Is_Concurrent_Component_Or_Discr (E)
                                  or else Is_Part_Of_Concurrent_Object (E)
                                then 1
                                else 0));
                     begin
                        if LHS.Contains (F) then
                           M.Insert
                             (F,
                              (if Is_Pure_Constant
                               then Flow_Id_Sets.Empty_Set
                               else Flow_Id_Sets.To_Set (Input)));
                        else
                           LHS_Ext_Inputs.Insert (Input);
                        end if;
                     end;
                  end loop;

                  if not LHS_Ext_Inputs.Is_Empty
                    and then Is_Tagged_Type (Map_Type)
                  then
                     --  Attempt to insert an empty set
                     M.Insert
                       (Key      => LHS_Ext,
                        Position => LHS_Ext_Position,
                        Inserted => Unused);

                     if not Is_Pure_Constant then
                        M (LHS_Ext_Position).Union (LHS_Ext_Inputs);
                     end if;
                  end if;
               end;
            end if;

         when N_Type_Conversion                                  =>
            pragma Annotate (Xcov, Exempt_On, "Debugging code");
            if Debug_Trace_Untangle_Record then
               Write_Str ("processing type/view conversion");
               Write_Eol;
            end if;
            pragma Annotate (Xcov, Exempt_Off);
            declare
               T_From : constant Entity_Id := Get_Type (Expression (N), Scope);
               T_To   : constant Entity_Id := Get_Type (N, Scope);

               Class_Wide_Conversion : constant Boolean :=
                 not Is_Class_Wide_Type (T_From)
                 and then Is_Class_Wide_Type (T_To);

               Tmp : constant Flow_Id_Maps.Map :=
                 Recurse_On
                   (Expression (N),
                    Map_Root,
                    Ext_Irrelevant =>
                      not (Class_Wide_Conversion
                           or not Extensions_Irrelevant));
               --  If we convert to a classwide type then any extensions
               --  are no longer irrelevant.

            begin
               Apply_Conversion (T_From, T_To, Tmp, M);
            end;

         when N_Expression_With_Actions | N_Qualified_Expression =>
            --  Recurse into the expression.
            M := Recurse_On (Expression (N), Map_Root, Map_Type);

         when N_Attribute_Reference                              =>
            pragma Annotate (Xcov, Exempt_On, "Debugging code");
            if Debug_Trace_Untangle_Record then
               Write_Str ("processing attribute ");
               Write_Name (Attribute_Name (N));
               Write_Eol;
            end if;
            pragma Annotate (Xcov, Exempt_Off);

            case Attribute_Name (N) is
               when Name_Update =>
                  pragma Assert (List_Length (Expressions (N)) = 1);
                  M :=
                    Untangle_Delta_Aggregate
                      (Prefix (N),
                       Component_Associations (First (Expressions (N))));

               when Name_Result =>
                  declare
                     Class_Wide_Conversion : constant Boolean :=
                       not Is_Class_Wide_Type (Get_Type (N, Scope))
                       and then Is_Class_Wide_Type (Map_Type);

                  begin
                     M :=
                       Recurse_On
                         (Prefix (N),
                          Map_Root,
                          Ext_Irrelevant =>
                            not (Class_Wide_Conversion
                                 or not Extensions_Irrelevant));
                  end;

               when Name_Old    =>
                  M := Recurse_On (Prefix (N), Map_Root);

               when others      =>
                  Error_Msg_N ("cannot untangle attribute", N);
                  raise Program_Error;
            end case;

         when N_Explicit_Dereference
            | N_Function_Call
            | N_Indexed_Component
            | N_Unchecked_Type_Conversion                        =>

            --  For these we just summarize the entire blob

            declare
               RHS : constant Flow_Id_Sets.Set := Get_Vars_Wrapper (N);
               LHS : constant Flow_Id_Sets.Set :=
                 Flatten_Variable (Map_Root, Scope);

            begin
               for Comp of LHS loop
                  M.Insert (Comp, RHS);
               end loop;
            end;

         when others                                             =>
            declare
               S : constant String := Nkind (N)'Img;

            begin
               Error_Msg_N ("cannot untangle node " & S, N);
               raise Why.Unexpected_Node;
            end;
      end case;

      <<Result_Untangle>>

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Debug_Trace_Untangle_Record then
         Outdent;

         Write_Str ("URA result: ");
         Print_Flow_Map (M);
      end if;
      pragma Annotate (Xcov, Exempt_Off);

      return M;
   end Untangle_Record_Assignment;

   --------------------------------
   -- Untangle_Assignment_Target --
   --------------------------------

   procedure Untangle_Assignment_Target
     (N                    : Node_Id;
      Scope                : Flow_Scope;
      Use_Computed_Globals : Boolean;
      Force_Extension      : Boolean := False;
      View_Conversion      : out Boolean;
      Map_Root             : out Flow_Id;
      Vars_Defined         : out Flow_Id_Sets.Set;
      Vars_Used            : out Flow_Id_Sets.Set;
      Partial_Definition   : out Boolean;
      Partial_Ext          : out Boolean;
      Partial_Priv         : out Boolean)
   is
      function Get_Vars_Wrapper (N : Node_Id) return Flow_Id_Sets.Set
      is (Get_Variables
            (N,
             Scope                => Scope,
             Target_Name          => Null_Flow_Id,
             Fold_Functions       => Inputs,
             Use_Computed_Globals => Use_Computed_Globals))
      with Pre => Nkind (N) in N_Subexpr;
      --  Returns inputs referenced in expression N

      Seq : Node_Lists.List;
      Idx : Positive;

      --  Start of processing for Untangle_Assignment_Target

   begin
      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Debug_Trace_Untangle then
         Write_Str ("Untangle_Assignment_Target on ");
         Sprint_Node_Inline (N);
         Write_Eol;
         Indent;
      end if;
      pragma Annotate (Xcov, Exempt_Off);

      Get_Assignment_Target_Properties
        (N,
         Partial_Definition => Partial_Definition,
         View_Conversion    => View_Conversion,
         Map_Root           => Map_Root,
         Seq                => Seq,
         Scope              => Scope);

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Debug_Trace_Untangle then
         Write_Line ("Seq is:");
         Indent;
         for N of Seq loop
            Print_Tree_Node (N);
         end loop;
         Outdent;

         Write_Str ("Map_Root: ");
         Print_Flow_Id (Map_Root);
         Write_Eol;
      end if;
      pragma Annotate (Xcov, Exempt_Off);

      --  We now set the variable(s) defined and will start to establish
      --  other variables that might be used.

      Vars_Defined := Flatten_Variable (Map_Root, Scope);
      Vars_Used := Flow_Id_Sets.Empty_Set;

      --  Assignment to an unconstrained record doesn't modify its bounds

      Vars_Defined.Exclude ((Map_Root with delta Facet => The_Bounds));

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Debug_Trace_Untangle then
         Write_Str ("Components: ");
         Print_Node_Set (Vars_Defined);
      end if;
      pragma Annotate (Xcov, Exempt_Off);

      --  We go through the sequence. At each point we might do one of the
      --  following, depending on the operation:
      --
      --    * Array index and slice: we process the expressions and add to
      --      the variables used in code and proof. We also make sure to
      --      not process any future type conversions as flow analysis can
      --      no longer distinguish elements.
      --
      --    * Component selection: we increment Idx.

      Idx := 1;

      for N of Seq loop
         case Valid_Assignment_Kinds (Nkind (N)) is
            when N_Indexed_Component                             =>
               declare
                  Expr : Node_Id := First (Expressions (N));

               begin
                  while Present (Expr) loop
                     Vars_Used.Union (Get_Vars_Wrapper (Expr));
                     Next (Expr);
                  end loop;
               end;

            when N_Slice                                         =>
               declare
                  R  : constant Node_Id := Get_Range (Discrete_Range (N));
                  LB : constant Node_Id := Low_Bound (R);
                  HB : constant Node_Id := High_Bound (R);
               begin
                  Vars_Used.Union (Get_Vars_Wrapper (LB));
                  Vars_Used.Union (Get_Vars_Wrapper (HB));
               end;

            when N_Selected_Component                            =>
               Idx := Idx + 1;

            when N_Unchecked_Type_Conversion | N_Type_Conversion =>
               null;

            when N_Explicit_Dereference                          =>
               null;

            when others                                          =>
               raise Why.Unexpected_Node;

         end case;
      end loop;

      Partial_Ext := False;
      Partial_Priv := False;

      --  On assignments to view conversions, the whole object might not be
      --  written even if Partial_Definition is False. Compute the assigned
      --  components.

      if View_Conversion and then not Partial_Definition then
         declare
            Assigned_Ty : constant Entity_Id := Get_Type (Etype (N), Scope);
            Base_Ty     : constant Entity_Id := Get_Type (Map_Root, Scope);
         begin
            --  If Assigned_Ty a specific ancestor of Base_Ty, trim the fields
            --  that do not occur in the assigned part.

            if not Is_Class_Wide_Type (Assigned_Ty)
              and then not Force_Extension
              and then Is_Ancestor (Assigned_Ty, Base_Ty, Scope)
            then
               declare
                  Old_Vars   : constant Flow_Id_Sets.Set := Vars_Defined;
                  New_Typ_Id : constant Flow_Id :=
                    Direct_Mapping_Id (Assigned_Ty);
                  New_Comps  : constant Flow_Id_Sets.Set :=
                    Get_Components (New_Typ_Id, Scope);
               begin
                  Vars_Defined := Flow_Id_Sets.Empty_Set;
                  for F of Old_Vars loop
                     if F.Kind = Record_Field
                       and then
                         New_Comps.Contains
                           (Add_Component (New_Typ_Id, F.Component (Idx)))
                     then
                        Vars_Defined.Insert (F);
                     elsif F.Kind = Direct_Mapping then
                        case F.Facet is
                           when Extension_Part =>

                              --  The extension cannot be written

                              null;

                           when Private_Part   =>

                              --  If Map_Root has a private part, then it might
                              --  be written by the assignment if Assigned_Ty
                              --  has private fields.

                              if New_Comps.Contains
                                   ((New_Typ_Id
                                     with delta Facet => Private_Part))
                              then
                                 Vars_Defined.Insert (F);

                                 --  If Base_Ty has additional private fields
                                 --  compared to Assigned_Ty, then the private
                                 --  fields is only partially written.

                                 Partial_Priv :=
                                   Introduces_Private_Fields
                                     (Base_Ty, Assigned_Ty, Scope);
                              end if;

                           when others         =>
                              raise Program_Error;
                        end case;
                     end if;
                  end loop;
               end;

            --  Otherwise, the extension might be assigned if it is visible

            else
               pragma
                 Assert
                   (Is_Class_Wide_Type (Assigned_Ty)
                    or else Force_Extension
                    or else Is_Ancestor (Base_Ty, Assigned_Ty, Scope));

               declare
                  The_Ext : constant Flow_Id :=
                    (Map_Root with delta Facet => Extension_Part);

               begin
                  if Extensions_Visible (Map_Root, Scope) then
                     Vars_Defined.Include (The_Ext);
                  end if;

                  --  When the Assigned_Ty is not a classwide type, the
                  --  extension might not be completly set.

                  if Vars_Defined.Contains (The_Ext)
                    and then not Is_Class_Wide_Type (Assigned_Ty)
                    and then not Force_Extension
                  then
                     Partial_Ext := True;
                  end if;
               end;
            end if;
         end;
      end if;

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Debug_Trace_Untangle then
         Write_Str ("Variables ");
         if Partial_Definition then
            Write_Str ("partially ");
         end if;
         Write_Str ("defined: ");
         Print_Node_Set (Vars_Defined);

         Write_Str ("Variables used: ");
         Print_Node_Set (Vars_Used);

         Outdent;
      end if;
      pragma Annotate (Xcov, Exempt_Off);
   end Untangle_Assignment_Target;

   --------------------------
   -- Is_Empty_Record_Type --
   --------------------------

   function Is_Empty_Record_Type (T : Entity_Id) return Boolean is
      Decl : constant Node_Id := Parent (T);
      Def  : Node_Id;
   begin
      case Nkind (Decl) is
         when N_Full_Type_Declaration =>
            Def := Type_Definition (Decl);
            case Nkind (Def) is
               when N_Record_Definition       =>
                  --  Ordinary record declaration, we just check if its either
                  --  null or there are no components.
                  return
                    No (Component_List (Def))
                    or else Null_Present (Component_List (Def));

               when N_Derived_Type_Definition =>
                  declare
                     Ext : constant Node_Id := Record_Extension_Part (Def);
                  begin
                     return
                       Is_Entity_Name (Subtype_Indication (Def))
                       and then
                         Is_Empty_Record_Type
                           (Entity (Subtype_Indication (Def)))
                       and then
                         (No (Ext)
                          or else Null_Present (Ext)
                          or else No (Component_List (Ext)));
                  end;

               when others                    =>
                  null;
            end case;

         when N_Subtype_Declaration   =>
            --  A subtype can be null too, we just check if the thing we're
            --  deriving it from is null.
            return
              Is_Entity_Name (Subtype_Indication (Decl))
              and then
                Is_Empty_Record_Type (Entity (Subtype_Indication (Decl)));

         when others                  =>
            null;
      end case;

      return False;
   end Is_Empty_Record_Type;

   -----------------------------
   -- Is_Dummy_Abstract_State --
   -----------------------------

   function Is_Dummy_Abstract_State
     (F : Flow_Id; S : Flow_Scope) return Boolean is
   begin
      if F.Kind = Direct_Mapping then
         declare
            E : constant Entity_Id := Get_Direct_Mapping_Id (F);
         begin
            return
              Ekind (E) = E_Abstract_State
              and then State_Refinement_Is_Visible (E, S)
              and then Has_Null_Refinement (E);
         end;
      else
         return False;
      end if;
   end Is_Dummy_Abstract_State;

   ----------------------
   -- Contract_Globals --
   ----------------------

   function Contract_Globals (E : Entity_Id) return Raw_Global_Nodes is
      Contract : Node_Id;

   begin
      --  Flow graphs contain globals that come, in the order of preference,
      --  from Refined_Global, Refined_Depends, Global or Depends (this order
      --  is hardcoded in Get_Globals).

      --  We should only process refined contracts if the body is in SPARK
      if Entity_Body_In_SPARK (E) then
         Contract := Find_Contract (E, Pragma_Refined_Global);

         if Present (Contract) then
            return Parse_Global_Contract (E, Contract);
         end if;

         Contract := Find_Contract (E, Pragma_Refined_Depends);

         if Present (Contract) then
            return Parse_Depends_Contract (E, Contract);
         end if;
      end if;

      Contract := Find_Contract (E, Pragma_Global);

      if Present (Contract) then
         return Parse_Global_Contract (E, Contract);
      end if;

      Contract := Find_Contract (E, Pragma_Depends);

      if Present (Contract) then
         return Parse_Depends_Contract (E, Contract);
      end if;

      pragma Assert (Is_Pure (E) or else Is_Null_Procedure (E));

      return
        (Proof_Ins => Node_Sets.Empty_Set,
         Inputs    => Node_Sets.Empty_Set,
         Outputs   => Node_Sets.Empty_Set);
   end Contract_Globals;

   ----------------------------
   -- Parse_Depends_Contract --
   ----------------------------

   function Parse_Depends_Contract
     (Subprogram : Entity_Id; Depends_Node : Node_Id) return Raw_Global_Nodes
   is
      Raw_Depends : constant Dependency_Maps.Map :=
        Parse_Depends (Depends_Node);
      --  ??? Parse_Depends should return a map of Entity_Ids and a separate
      --  routine should lift that to Flow_Ids.

      Params : constant Node_Sets.Set := Get_Formals (Subprogram);
      --  Our own parameters are allowed in Depends but not in Globals, so we
      --  need to filter them. Note that the formal parameters that we collect
      --  here will also include implicit formal parameters of subprograms that
      --  belong to concurrent types.

      Globals : Raw_Global_Nodes;

   begin
      for C in Raw_Depends.Iterate loop
         declare
            Output : Flow_Id renames Dependency_Maps.Key (C);
            Inputs : Flow_Id_Sets.Set renames Raw_Depends (C);

         begin
            pragma Assert (Output.Kind in Null_Value | Direct_Mapping);

            --  Filter function'Result and parameters
            if Present (Output) then
               declare
                  Item : constant Entity_Id := Get_Direct_Mapping_Id (Output);

               begin
                  if Item /= Subprogram and then not Params.Contains (Item)
                  then
                     Globals.Outputs.Include (Item);
                  end if;
               end;
            end if;

            for Input of Inputs loop
               pragma Assert (Input.Kind in Null_Value | Direct_Mapping);

               if Present (Input) then
                  declare
                     Item : constant Entity_Id :=
                       Get_Direct_Mapping_Id (Input);

                  begin
                     if not Params.Contains (Item) then
                        Globals.Inputs.Include (Item);

                        --  A volatile with effective reads is always an output
                        --  as well (this should be recorded in the depends,
                        --  but the front-end does not enforce this).
                        if Has_Effective_Reads (Input) then
                           Globals.Outputs.Include (Item);
                        end if;

                     end if;
                  end;
               end if;
            end loop;
         end;
      end loop;

      return Globals;

   end Parse_Depends_Contract;

   -------------------------
   -- Is_Opaque_For_Proof --
   -------------------------

   function Is_Opaque_For_Proof (F : Flow_Id) return Boolean is
      E : constant Entity_Id := Find_Entity (F.Name);

   begin
      if Present (E) then
         return Ekind (E) = E_Abstract_State or else not Entity_In_SPARK (E);
      else
         return True;
      end if;
   end Is_Opaque_For_Proof;

   -------------
   -- Find_In --
   -------------

   function Find_In (User : Node_Sets.Set; G : Entity_Id) return Entity_Id is
   begin
      if User.Contains (G) then
         return G;
      elsif Is_Constituent (G) then
         return Find_In (User, Encapsulating_State (G));
      else
         return Empty;
      end if;
   end Find_In;

   -------------
   -- Find_In --
   -------------

   function Find_In (User : Flow_Id_Sets.Set; G : Flow_Id) return Flow_Id is
   begin
      if User.Contains (G) then
         return G;
      elsif Is_Constituent (G) then
         return Find_In (User, Encapsulating_State (G));
      else
         return Null_Flow_Id;
      end if;
   end Find_In;

   --------------------------
   -- Strip_Child_Prefixes --
   --------------------------

   function Strip_Child_Prefixes (EN : String) return String
   is (if EN'Length > Child_Prefix'Length
         and then
           EN (EN'First .. EN'First + Child_Prefix'Length - 1) = Child_Prefix
       then
         Strip_Child_Prefixes (EN (EN'First + Child_Prefix'Length .. EN'Last))
       else EN);

   ---------------------
   -- Path_To_Flow_Id --
   ---------------------

   function Path_To_Flow_Id (Expr : Node_Id; Scop : Flow_Scope) return Flow_Id
   is
      Seq : Node_Lists.List;
      --  A sequence of nodes on the path expression; we use a list here,
      --  because it makes an expression like "A.B.C" easy to process
      --  left-to-right, while the AST of this expression only allows
      --  processing right-to-left.

      N : Node_Id := Expr;
      --  Current node

      Obj : Flow_Id;
      --  The flow representation of the object denoted by the Expr path

   begin
      while Nkind (N) not in N_Expanded_Name | N_Identifier | N_Null loop
         Seq.Prepend (N);

         N :=
           (case Nkind (N) is
              when N_Explicit_Dereference
                 | N_Indexed_Component
                 | N_Slice
                 | N_Selected_Component
                 | N_Attribute_Reference       => Prefix (N),

              when N_Qualified_Expression
                 | N_Type_Conversion
                 | N_Unchecked_Type_Conversion => Expression (N),

              when others                      => raise Program_Error);
      end loop;

      if Nkind (N) = N_Null then
         return Null_Flow_Id;
      end if;

      declare
         Root_Entity : constant Entity_Id := Entity (N);

      begin
         Obj :=
           (if Is_Protected_Component (Root_Entity)
            then
              Add_Component
                (Direct_Mapping_Id (Scope (Root_Entity)), Root_Entity)

            elsif Is_Part_Of_Concurrent_Object (Root_Entity)
            then
              Add_Component
                (Direct_Mapping_Id (Etype (Encapsulating_State (Root_Entity))),
                 Root_Entity)

            elsif Ekind (Root_Entity) = E_Variable
              and then Present (Ultimate_Overlaid_Entity (Root_Entity))
            then Direct_Mapping_Id (Ultimate_Overlaid_Entity (Root_Entity))

            else Direct_Mapping_Id (Unique_Entity (Root_Entity)));
      end;

      for N of Seq loop
         case Nkind (N) is
            when N_Explicit_Dereference | N_Indexed_Component | N_Slice =>
               return Obj;

            when N_Attribute_Reference                                  =>
               pragma Assert (Attribute_Name (N) = Name_Access);
               return Obj;

            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion                            =>
               null;

            when N_Selected_Component                                   =>
               declare
                  Field      : constant Entity_Id :=
                    Unique_Component (Entity (Selector_Name (N)));
                  Components : constant Flow_Id_Sets.Set :=
                    Get_Components (Obj, Scop);
                  New_Comp   : constant Flow_Id := Add_Component (Obj, Field);
               begin
                  if Components.Contains (New_Comp) then
                     Obj := New_Comp;
                  else

                     --  If Map_Root's type is an ancestor of the type
                     --  declaring Field, then Field is necessarily part of
                     --  the extension. Otherwise, we are in presence of
                     --  invisible private derivation. We cannot know which
                     --  parts of the object is updated.

                     if Is_Ancestor
                          (Get_Type (Obj, Scop),
                           Get_Type (Scope (Field), Scop),
                           Scop)
                     then
                        Obj := (Obj with delta Facet => Extension_Part);
                     end if;
                     return Obj;
                  end if;
               end;

            when others                                                 =>
               raise Program_Error;
         end case;
      end loop;

      return Obj;
   end Path_To_Flow_Id;

   --------------------
   -- To_Subprograms --
   --------------------

   function To_Subprograms (Calls : Call_Sets.Set) return Node_Sets.Set is
      Subps : Node_Sets.Set;
   begin
      for SC of Calls loop
         Subps.Include (SC.E);
      end loop;

      return Subps;
   end To_Subprograms;

   ----------------------------------
   -- Denote_Same_Protected_Object --
   ----------------------------------

   function Denote_Same_Protected_Object (A, B : Node_Id) return Boolean is
      A_Prefix : Node_Id := A;
      B_Prefix : Node_Id := B;
   begin
      --  The following code intentionally uses iteration and not recursion, so
      --  that we only check the postcondition once we get the final verdict.

      loop
         if Is_Entity_Name (A_Prefix) and then Is_Entity_Name (B_Prefix) then
            return Entity (A_Prefix) = Entity (B_Prefix);

         elsif Nkind (A_Prefix) = N_Slice then
            A_Prefix := Prefix (A_Prefix);

         elsif Nkind (B_Prefix) = N_Slice then
            B_Prefix := Prefix (B_Prefix);

         elsif Nkind (A_Prefix) = N_Indexed_Component
           and then Nkind (B_Prefix) = N_Indexed_Component
         then
            A_Prefix := Prefix (A_Prefix);
            B_Prefix := Prefix (B_Prefix);

         elsif Nkind (A_Prefix) = N_Selected_Component
           and then Nkind (B_Prefix) = N_Selected_Component
           and then
             Chars (Selector_Name (A_Prefix))
             = Chars (Selector_Name (B_Prefix))
         then
            A_Prefix := Prefix (A_Prefix);
            B_Prefix := Prefix (B_Prefix);

         else
            --  This routine is only executed as part of equivalence check
            --  after protected prefixes yield the same hash value, which is
            --  virtually impossible to test.

            pragma Annotate (Xcov, Exempt_On, "Only runs on hash collision");

            pragma
              Assert
                (Is_Entity_Name (A_Prefix)
                 or else
                   Nkind (A_Prefix)
                   in N_Indexed_Component | N_Selected_Component | N_Slice);

            pragma
              Assert
                (Is_Entity_Name (B_Prefix)
                 or else
                   Nkind (B_Prefix)
                   in N_Indexed_Component | N_Selected_Component | N_Slice);

            return False;

            pragma Annotate (Xcov, Exempt_Off);
         end if;
      end loop;
   end Denote_Same_Protected_Object;

   -----------------------------
   -- Register_Protected_Call --
   -----------------------------

   procedure Register_Protected_Call
     (Callsite : Node_Id; Locks : in out Protected_Call_Sets.Set)
   is
      Unused_Position : Protected_Call_Sets.Cursor;
      Unused_Inserted : Boolean;
   begin
      --  If a given prefix was already locked by another protected operation,
      --  then inserting as opposed to including will keep the previous
      --  operation. This way we pick the syntactically first protected call
      --  to a given prefix, which makes call traces easier to understand.

      Locks.Insert
        (Protected_Call'
           (Prefix    => Prefix (Name (Callsite)),
            Operation => Get_Called_Entity (Callsite)),
         Unused_Position,
         Unused_Inserted);
   end Register_Protected_Call;

end Flow_Utility;
