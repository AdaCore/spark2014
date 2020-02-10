------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2013-2020, Altran UK Limited                --
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

with Ada.Containers.Hashed_Maps;

with Errout;                          use Errout;
with Lib;                             use Lib;
with Namet;                           use Namet;
with Nlists;                          use Nlists;
with Output;                          use Output;
with Rtsfind;                         use Rtsfind;
with Sem_Prag;                        use Sem_Prag;
with Sem_Type;                        use Sem_Type;
with Sprint;                          use Sprint;
with Treepr;                          use Treepr;
with Uintp;                           use Uintp;

with Common_Iterators;                use Common_Iterators;
with Gnat2Why_Args;
with Gnat2Why.Util;
with SPARK_Definition;                use SPARK_Definition;
with SPARK_Frame_Conditions;          use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms;          use SPARK_Util.Subprograms;
with SPARK_Util.Types;                use SPARK_Util.Types;
with Why;

with Flow_Classwide;
with Flow_Debug;                      use Flow_Debug;
with Flow.Dynamic_Memory;
with Flow_Generated_Globals.Phase_2;  use Flow_Generated_Globals.Phase_2;
with Flow_Refinement;                 use Flow_Refinement;

package body Flow_Utility is

   use type Flow_Id_Sets.Set;

   ----------------------------------------------------------------------
   --  Debug
   ----------------------------------------------------------------------

   Debug_Trace_Get_Global      : constant Boolean := False;
   --  Enable this to debug Get_Global.

   Debug_Trace_Flatten         : constant Boolean := False;
   --  Enable this for tracing in Flatten_Variable.

   Debug_Trace_Untangle        : constant Boolean := False;
   --  Enable this to print the tree and def/use sets in each call of
   --  Untangle_Assignment_Target.

   Debug_Trace_Untangle_Fields : constant Boolean := False;
   --  Enable this to print detailed traces in Untangle_Record_Fields.

   Debug_Trace_Untangle_Record : constant Boolean := False;
   --  Enable this to print traces for Untangle_Record_Assignemnt.

   ----------------------------------------------------------------------
   --  Loop information
   ----------------------------------------------------------------------

   package Loop_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Flow_Id_Sets.Set,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   Loop_Info_Frozen : Boolean       := False with Ghost;
   Loop_Info        : Loop_Maps.Map := Loop_Maps.Empty_Map;

   ----------------------------------------------------------------------
   --  Local
   ----------------------------------------------------------------------

   function Unique_Components (E : Entity_Id) return Node_Lists.List
   with Pre  => Is_Type (E),
        Post => (for all C of Unique_Components'Result =>
                   Is_Unique_Component (C));
   --  Return components in SPARK of the given entity E, similar to
   --  {First,Next}_Component_Or_Discriminant, with the difference that any
   --  components of private ancestors are included.
   --  @param E a type entity
   --  @return all unique components and discriminants of type E that are in
   --    SPARK or the empty list if none exists.

   function First_Name_Node (N : Node_Id) return Node_Id
   with Pre  => Nkind (N) in N_Identifier | N_Expanded_Name,
        Post => Nkind (First_Name_Node'Result) = N_Identifier;
   --  Returns the first node that represents a (possibly qualified) entity
   --  name, i.e. for "X" it will be the node of X itself and for "P.X" it will
   --  be the node of P.
   --
   --  This is a helper routine for putting error messages within the Depends,
   --  Refined_Depends and Initializes contract. Note: it is similar to the
   --  Errout.First_Node, but doesn't rely on slocs thus avoids possible
   --  problems with generic instances (as described in Safe_First_Sloc).

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

   package Entity_To_Boolean_Maps is new Ada.Containers.Hashed_Maps
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

   function Classwide_Pre_Post (E : Entity_Id; Contract : Pragma_Id)
                                return Node_Lists.List
   is (Find_Contracts (E         => E,
                       Name      => Contract,
                       Classwide => not Present (Overridden_Operation (E)),
                       Inherited => Present (Overridden_Operation (E))))
   with Pre => Is_Dispatching_Operation (E)
     and then Contract in Pragma_Precondition
                        | Pragma_Postcondition;
   --  Return the list of the classwide pre- or post-conditions for entity E

   ---------------------
   -- Add_Loop_Writes --
   ---------------------

   procedure Add_Loop_Writes (Loop_E : Entity_Id;
                              Writes : Flow_Id_Sets.Set)
   is
   begin
      pragma Assert (not Loop_Info_Frozen);
      Loop_Info.Insert (Loop_E, Writes);
   end Add_Loop_Writes;

   -------------------------------------------
   -- Collect_Functions_And_Read_Locked_POs --
   -------------------------------------------

   procedure Collect_Functions_And_Read_Locked_POs
     (N                  : Node_Id;
      Scop               : Flow_Scope;
      Functions_Called   : in out Node_Sets.Set;
      Tasking            : in out Tasking_Info;
      Generating_Globals : Boolean)
   is
      function Proc (N : Node_Id) return Traverse_Result;
      --  If the node being processed is an N_Function_Call, store a
      --  corresponding Entity_Id; for protected functions store the
      --  read-locked protected object.

      procedure Process_Type (E : Entity_Id);
      --  Merge predicate function for the given type

      ------------------
      -- Process_Type --
      ------------------

      procedure Process_Type (E : Entity_Id) is
         P : constant Entity_Id := Predicate_Function (E);
      begin
         if Present (P) then
            Collect_Functions_And_Read_Locked_POs
              (N                  => Get_Expr_From_Return_Only_Func (P),
               Scop               => Scop,
               Functions_Called   => Functions_Called,
               Tasking            => Tasking,
               Generating_Globals => Generating_Globals);
         end if;
      end Process_Type;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result
      is
         P : Node_Id;
      begin
         case Nkind (N) is
            when N_Function_Call =>
               declare
                  Called_Func : constant Entity_Id := Get_Called_Entity (N);

               begin
                  --  For predicate functions descend into the predicate
                  --  expression and continue traversal.

                  if Is_Predicate_Function (Called_Func) then
                     Collect_Functions_And_Read_Locked_POs
                       (N                  =>
                          Get_Expr_From_Return_Only_Func (Called_Func),
                        Scop               => Scop,
                        Functions_Called   => Functions_Called,
                        Tasking            => Tasking,
                        Generating_Globals => Generating_Globals);

                     return OK;
                  end if;

                  --  We include the called function only if it is visible from
                  --  the scope. For example, the call might not be visible
                  --  when it happens in the type invariant of an externally
                  --  visible type and the function called is declared in the
                  --  private part.
                  if Is_Visible (Unit_Declaration_Node (Called_Func), Scop)
                  then
                     Functions_Called.Include (Called_Func);
                  end if;

                  --  Only external calls to protected functions trigger
                  --  priority ceiling protocol checks; internal calls do not.
                  if Generating_Globals
                    and then Ekind (Scope (Called_Func)) = E_Protected_Type
                    and then Is_External_Call (N)
                  then
                     Tasking (Locks).Include
                       (Get_Enclosing_Object (Prefix (Name (N))));
                  end if;
               end;

            when N_Membership_Test =>
               if Present (Right_Opnd (N)) then
                  --  x in t
                  P := Right_Opnd (N);
                  if Nkind (P) in N_Identifier | N_Expanded_Name
                    and then Is_Type (Entity (P))
                  then
                     Process_Type (Get_Type (P, Scop));
                  end if;
               else
                  --  x in t | 1 .. y | u
                  P := First (Alternatives (N));
                  loop
                     if Nkind (P) in N_Identifier | N_Expanded_Name
                       and then Is_Type (Entity (P))
                     then
                        Process_Type (Get_Type (P, Scop));
                     end if;
                     Next (P);

                     exit when No (P);
                  end loop;
               end if;

            --  Operator nodes represent calls to intrinsic subprograms, which
            --  we assume to be free from any side effects.

            when N_Op =>
               pragma Assert (Is_Intrinsic_Subprogram (Entity (N)));

            when others =>
               null;
         end case;

         return OK;
      end Proc;

      procedure Traverse is new Traverse_More_Proc (Process => Proc);
      --  AST traversal procedure

   --  Start of processing for Collect_Functions_And_Read_Locked_POs

   begin
      Traverse (N);
   end Collect_Functions_And_Read_Locked_POs;

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
            function Ancestor (Typ : Entity_Id) return Entity_Id
            with Pre  => Is_Type (Typ),
                 Post => (if Present (Ancestor'Result)
                          then Is_Type (Ancestor'Result));
            --  Helper function to iterate over a type ancestors. If Typ is a
            --  subtype, then skip the immediate ancestor. If no more ancestors
            --  are present, then return Empty.

            --------------
            -- Ancestor --
            --------------

            function Ancestor (Typ : Entity_Id) return Entity_Id is
               Parent_Typ : constant Entity_Id := Etype (Typ);
            begin
               if Ekind (Typ) = E_Record_Subtype then
                  return Ancestor (Parent_Typ);
               else
                  if Parent_Typ = Typ then
                     return Empty;
                  else
                     pragma Assert (Present (Parent_Typ));
                     return Parent_Typ;
                  end if;
               end if;
            end Ancestor;

            --  Local variables

            Ptr : Entity_Id;
            T   : Entity_Id       := E;
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
                        S.Insert (New_Item => Unique_Component (Ptr),
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
   -- Contains_Discriminants --
   ----------------------------

   function Contains_Discriminants
     (F : Flow_Id;
      S : Flow_Scope)
      return Boolean
   is
      FS : constant Flow_Id_Sets.Set := Flatten_Variable (F, S);
   begin
      return (for some X of FS => Is_Discriminant (X));
   end Contains_Discriminants;

   ----------------------------
   -- Expand_Abstract_States --
   ----------------------------

   function Expand_Abstract_States
     (Vars : Flow_Id_Sets.Set)
      return Flow_Id_Sets.Set
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
     (E     : Entity_Id;
      Scope : Flow_Scope)
      return Boolean
   is
      T : constant Entity_Id := Get_Type (E, Scope);
   begin
      return Is_Formal (E)
        and then Is_Tagged_Type (T)
        and then not Is_Class_Wide_Type (T)
        and then Has_Extensions_Visible (Sinfo.Scope (E));
   end Extensions_Visible;

   function Extensions_Visible (F     : Flow_Id;
                                Scope : Flow_Scope)
                                return Boolean
   is
   begin
      case F.Kind is
         when Direct_Mapping =>
            return Extensions_Visible (Get_Direct_Mapping_Id (F), Scope);

         when Record_Field =>
            --  Record fields themselves cannot be classwide
            return False;

         when Null_Value | Synthetic_Null_Export | Magic_String =>
            --  These are just blobs which we don't know much about, so no
            --  extensions here.
            return False;
      end case;
   end Extensions_Visible;

   ----------------------
   -- Flatten_Variable --
   ----------------------

   function Flatten_Variable
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Flow_Id_Sets.Set
   is
   begin
      if F.Kind in Direct_Mapping | Record_Field
        and then F.Facet = Normal_Part
      then
         if Debug_Trace_Flatten then
            Write_Str ("Flatten: ");
            Print_Flow_Id (F);
         end if;

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

               subtype Private_Nonrecord_Kind is Private_Kind with
                 Static_Predicate =>
                   Private_Nonrecord_Kind not in E_Record_Type_With_Private |
                                                 E_Record_Subtype_With_Private;
               --  Non-record private types

               procedure Debug (Msg : String);
               --  Output debug message

               -----------
               -- Debug --
               -----------

               procedure Debug (Msg : String) is
               begin
                  if Debug_Trace_Flatten then
                     Write_Line (Msg);
                  end if;
               end Debug;

            begin
               if Debug_Trace_Flatten then
                  Indent;
               end if;

               while Is_Class_Wide_Type (T) loop
                  T := Get_Type (Etype (T), Scope);
               end loop;

               pragma Assert (Is_Type (T));

               if Debug_Trace_Flatten then
                  Write_Str ("Branching on type: ");
                  Sprint_Node_Inline (T);
                  Write_Line (" (" & Ekind (T)'Img & ")");
               end if;

               --  If the type is not in SPARK we return the variable itself
               if not Entity_In_SPARK (T) then
                  return Flow_Id_Sets.To_Set (F);
               end if;

               case Type_Kind'(Ekind (T)) is
                  when Private_Nonrecord_Kind =>
                     Debug ("processing private type");

                     if Has_Discriminants (T) then
                        for C of Unique_Components (T) loop
                           if Is_Visible (C, Scope) then
                              Results.Insert (Add_Component (F, C));
                           else
                              Contains_Non_Visible := True;
                           end if;
                        end loop;
                        Results.Insert (F'Update (Facet => Private_Part));
                     else
                        Results := Flow_Id_Sets.To_Set (F);
                     end if;

                  when Concurrent_Kind =>
                     Debug ("processing " &
                            (case Ekind (T) is
                               when Protected_Kind => "protected",
                               when Task_Kind      => "task",
                               when others         => raise Program_Error) &
                              " type");

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
                              Results.Union
                                (Flatten_Variable (Add_Component (F, C),
                                                   Scope));

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
                                 Results.Union
                                   (Flatten_Variable (Add_Component (F, C),
                                    Scope));
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

                  when Record_Kind =>
                     Debug ("processing record type");

                     --  Include classwide types and privates with
                     --  discriminants.
                     if Unique_Components (T).Is_Empty then
                        --  If the record has an empty component list then we
                        --  add the variable itself...
                        --  Note that this happens also when the components are
                        --  hidden behind a SPARK_Mode => Off.
                        Results.Insert (F);

                     else
                        --  ...else we add each visible component
                        for C of Unique_Components (T) loop
                           if Is_Visible (C, Scope) then
                              --  Here we union disjoint sets, so possibly we
                              --  could optimize this.
                              Results.Union
                                (Flatten_Variable
                                   (Add_Component (F, C), Scope));

                           else
                              Contains_Non_Visible := True;
                           end if;
                        end loop;
                     end if;

                     if Is_Private_Type (T) then
                        Contains_Non_Visible := True;
                     end if;

                     if Contains_Non_Visible then
                        --  We must have some discriminant, so return
                        --  X'Private_Part and the discriminants. For
                        --  simple private types we don't do this split.
                        if Results.Is_Empty then
                           Results := Flow_Id_Sets.To_Set (F);
                        else
                           Results.Insert (F'Update (Facet => Private_Part));
                        end if;
                     end if;

                     if Classwide then
                        --  Ids.Insert (F'Update (Facet => The_Tag)); ???
                        Results.Insert (F'Update (Facet => Extension_Part));
                     end if;

                  when Access_Kind
                     | Array_Kind
                     | Scalar_Kind
                  =>
                     Debug ("processing access or array or scalar type");

                     Results := Flow_Id_Sets.To_Set (F);

                  when E_Exception_Type
                     | E_Subprogram_Type
                     | Incomplete_Kind
                  =>
                     raise Program_Error;

               end case;

               if Debug_Trace_Flatten then
                  Outdent;
               end if;

               return Results;
            end;
         end if;
      else
         if Debug_Trace_Flatten then
            Write_Str ("Flatten: ");
            Print_Flow_Id (F);
         end if;

         return Flow_Id_Sets.To_Set (F);
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
      Partial_Definition : out Boolean;
      View_Conversion    : out Boolean;
      Map_Root           : out Flow_Id;
      Seq                : out Node_Lists.List)
   is
      subtype Interesting_Nodes is Valid_Assignment_Kinds
        with Static_Predicate => Interesting_Nodes not in
          N_Identifier | N_Expanded_Name;

      Root_Node   : Node_Id := N;
      Root_Entity : Entity_Id;
      --  To avoid repeated calls to Entity on the Root_Node

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

               when others =>
                  Prefix (Root_Node));
      end loop;

      pragma Assert (Nkind (Root_Node) in N_Identifier | N_Expanded_Name);

      Root_Entity := Entity (Root_Node);

      if Is_Protected_Component (Root_Entity) then
         Map_Root :=
           Add_Component
             (Direct_Mapping_Id (Scope (Root_Entity)),
              Root_Entity);

      elsif Is_Part_Of_Concurrent_Object (Root_Entity) then
         Map_Root :=
           Add_Component
             (Direct_Mapping_Id
                (Etype (Encapsulating_State (Root_Entity))),
              Root_Entity);

      else
         Map_Root := Direct_Mapping_Id (Root_Entity);
      end if;

      --  We now work out which variable (or group of variables) is actually
      --  defined, by following the selected components. If we find an array
      --  slice or index we stop and note that we are dealing with a partial
      --  assignment (the defined variable is implicitly used).

      Partial_Definition := False;
      View_Conversion    := False;

      for N of Seq loop
         case Interesting_Nodes (Nkind (N)) is
            when N_Selected_Component =>
               Map_Root :=
                 Add_Component
                   (Map_Root,
                    Unique_Component (Entity (Selector_Name (N))));

            when N_Type_Conversion =>
               View_Conversion := True;

            when N_Unchecked_Type_Conversion =>
               null;

            when N_Indexed_Component | N_Slice | N_Explicit_Dereference =>
               Partial_Definition := True;
               exit;
         end case;
      end loop;
   end Get_Assignment_Target_Properties;

   -----------------
   -- Get_Depends --
   -----------------

   procedure Get_Depends
     (Subprogram           : Entity_Id;
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
         pragma Assert
           (Present (Find_Contract (Subprogram, Pragma_Depends))
              and then
            No (Find_Contract (Subprogram, Pragma_Refined_Depends)));

         --  Collect all global Proof_Ins, Outputs and Inputs

         Get_Globals (Subprogram          => Subprogram,
                      Scope               => Scope,
                      Classwide           => False,
                      Globals             => Globals,
                      Use_Deduced_Globals => Use_Computed_Globals,
                      Ignore_Depends      => True);

         --  Change all variants to Normal_Use

         Globals :=
           (Proof_Ins => Change_Variant (Globals.Proof_Ins, Normal_Use),
            Inputs    => Change_Variant (Globals.Inputs,    Normal_Use),
            Outputs   => Change_Variant (Globals.Outputs,   Normal_Use));

         --  Add formal parameters

         for Param of Get_Formals (Subprogram) loop
            declare
               Formal_Param : constant Flow_Id := Direct_Mapping_Id (Param);

            begin
               case Ekind (Param) is
                  when E_In_Parameter =>
                     Globals.Inputs.Insert (Formal_Param);
                     Globals.Proof_Ins.Insert (Formal_Param);

                  when E_In_Out_Parameter =>
                     Globals.Proof_Ins.Insert (Formal_Param);
                     Globals.Inputs.Insert (Formal_Param);
                     Globals.Outputs.Insert (Formal_Param);

                  when E_Out_Parameter =>
                     Globals.Outputs.Insert (Formal_Param);

                  when E_Protected_Type | E_Task_Type =>
                     Globals.Inputs.Insert (Formal_Param);
                     Globals.Proof_Ins.Insert (Formal_Param);
                     if Ekind (Subprogram) /= E_Function then
                        Globals.Outputs.Insert (Formal_Param);
                     end if;

                  when others =>
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
               Output : Flow_Id          renames Dependency_Maps.Key (C);
               Input  : Flow_Id_Sets.Set renames Contract_Relation (C);

               Refined_Input  : constant Flow_Id_Sets.Set :=
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
                       Refined_Input.Intersection (if O = Null_Flow_Id
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

               D_In  : constant Flow_Id_Sets.Set :=
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

      Get_Globals (Subprogram          => Subprogram,
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
            Depends.Insert (Key      => Null_Flow_Id,
                            Position => Position,
                            Inserted => Unused);

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
            Depends.Insert (Key      => Current_Task_Type,
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
     (Name : Entity_Name;
      View : Flow_Id_Variant := Normal_Use)
      return Flow_Id
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

   function Get_Functions (N                  : Node_Id;
                           Include_Predicates : Boolean)
                           return Node_Sets.Set
   is
      Funcs  : Node_Sets.Set := Node_Sets.Empty_Set;
      Unused : Tasking_Info;
   begin
      Collect_Functions_And_Read_Locked_POs
        (N,
         Scop               => Get_Flow_Scope (N), --  ??? could be parameter
         Functions_Called   => Funcs,
         Tasking            => Unused,
         Generating_Globals => Include_Predicates);
      return Funcs;
   end Get_Functions;

   ---------------------------
   -- Parse_Global_Contract --
   ---------------------------

   function Parse_Global_Contract
     (Subprogram  : Entity_Id;
      Global_Node : Node_Id)
      return Raw_Global_Nodes
   is
      Globals : Raw_Global_Nodes;

      subtype Global_Name_Id is Name_Id
        with Static_Predicate => Global_Name_Id in Name_Input
                                                 | Name_In_Out
                                                 | Name_Output
                                                 | Name_Proof_In;

      procedure Process (The_Mode   : Global_Name_Id;
                         The_Global : Entity_Id);
      --  Add the given global to Reads, Writes or Proof_Ins, depending
      --  on the mode.

      -------------
      -- Process --
      -------------

      procedure Process (The_Mode   : Global_Name_Id;
                         The_Global : Entity_Id)
      is
         E : constant Entity_Id :=
           Canonical_Entity (The_Global, Subprogram);

      begin
         case The_Mode is
            when Name_Input =>
               if not Is_Generic_Actual_Without_Variable_Input (E) then
                  Globals.Inputs.Insert (E);
               end if;

            when Name_In_Out =>
               Globals.Inputs.Insert (E);
               Globals.Outputs.Insert (E);

            when Name_Output =>
               Globals.Outputs.Insert (E);

            when Name_Proof_In =>
               if not Is_Generic_Actual_Without_Variable_Input (E) then
                  Globals.Proof_Ins.Insert (E);
               end if;
         end case;
      end Process;

      --  Local variables

      pragma Assert
        (List_Length (Pragma_Argument_Associations (Global_Node)) = 1);

      PAA  : constant Node_Id :=
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
               pragma Assert
                 (Nkind (RHS) in N_Identifier | N_Expanded_Name);

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
            Row : Node_Id :=
              First (Component_Associations (Expression (PAA)));

         begin
            loop
               pragma Assert (List_Length (Choices (Row)) = 1);

               declare
                  Mode : Name_Id renames Chars (First (Choices (Row)));
                  RHS  : Node_Id renames Expression (Row);

               begin
                  case Nkind (RHS) is
                     when N_Null =>
                        null;

                     when N_Identifier | N_Expanded_Name =>
                        Process (Mode, Entity (RHS));

                     when N_Aggregate =>
                        declare
                           Item : Node_Id := First (Expressions (RHS));

                        begin
                           loop
                              pragma Assert
                                (Nkind (Item) in N_Identifier
                                               | N_Expanded_Name);

                              Process (Mode, Entity (Item));

                              Next (Item);

                              exit when No (Item);
                           end loop;
                        end;

                     when others =>
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
     (Scop : Flow_Scope; Objects : in out Flow_Id_Sets.Set;
      Entire : Boolean := True)
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
                  if Ekind (E) = E_Constant
                    and then In_Generic_Actual (E)
                  then
                     if Scope_Within_Or_Same (Inner => Scop.Ent,
                                              Outer => Scope (E))
                     then
                        Mapped.Include (Object);
                     else
                        declare
                           Inputs : constant Flow_Id_Sets.Set :=
                             Get_Variables
                               (Expression (Declaration_Node (E)),
                                Scope                => Scop,
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

            when Magic_String =>
               Mapped.Include (Object);

            when others =>
               raise Program_Error;
         end case;
      end loop;

      Flow_Id_Sets.Move (Target => Objects,
                         Source => Mapped);
   end Map_Generic_In_Formals;

   -----------------
   -- Get_Globals --
   -----------------

   procedure Get_Globals (Subprogram          : Entity_Id;
                          Scope               : Flow_Scope;
                          Classwide           : Boolean;
                          Globals             : out Global_Flow_Ids;
                          Use_Deduced_Globals : Boolean := True;
                          Ignore_Depends      : Boolean := False)
   is
      Global_Node  : constant Node_Id := Get_Contract_Node (Subprogram,
                                                            Scope,
                                                            Global_Contract);
      Depends_Node : constant Node_Id := Get_Contract_Node (Subprogram,
                                                            Scope,
                                                            Depends_Contract);

      Use_Generated_Globals : constant Boolean :=
        Rely_On_Generated_Global (Subprogram, Scope);

      procedure Debug (Msg : String);
      --  Write message Msg to debug output

      procedure Debug (Label : String; S : Flow_Id_Sets.Set);
      --  Write Label followed by elements of S to debug output

      -----------
      -- Debug --
      -----------

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

   --  Start of processing for Get_Globals

   begin
      Globals.Proof_Ins := Flow_Id_Sets.Empty_Set;
      Globals.Inputs    := Flow_Id_Sets.Empty_Set;
      Globals.Outputs   := Flow_Id_Sets.Empty_Set;

      if Debug_Trace_Get_Global then
         Write_Str ("Get_Global (");
         Sprint_Node (Subprogram);
         Write_Str (", ");
         Print_Flow_Scope (Scope);
         Write_Line (")");
      end if;

      if Present (Global_Node)
        and then not Use_Generated_Globals
      then
         Debug ("using user annotation");

         declare
            ---------------------------------------------------------------
            --  Step 1: Process global annotation
            ---------------------------------------------------------------

            Raw_Globals : constant Raw_Global_Nodes :=
              Parse_Global_Contract (Subprogram  => Subprogram,
                                     Global_Node => Global_Node);

         begin
            ---------------------------------------------------------------
            --  Step 2: Expand any abstract state that might be too refined for
            --  our given scope; also, convert to Flow_Ids in preparation for
            --  the next step, where objects only known by Magic_String might
            --  appear.
            ---------------------------------------------------------------

            Globals :=
              (Proof_Ins =>
                 To_Flow_Id_Set (Down_Project (Raw_Globals.Proof_Ins, Scope),
                                 In_View),
               Inputs =>
                 To_Flow_Id_Set (Down_Project (Raw_Globals.Inputs, Scope),
                                 In_View),
               Outputs =>
                 To_Flow_Id_Set (Down_Project (Raw_Globals.Outputs, Scope),
                                 Out_View));

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
              and then Pragma_Name (Global_Node)  = Name_Global
              and then Pragma_Name (Depends_Node) = Name_Refined_Depends
              and then Mentions_State_With_Ambiguous_Refinement
                         (Global_Node, Scope)
            then
               declare
                  D_Map          : Dependency_Maps.Map;
                  Refined_Inputs : Flow_Id_Sets.Set;

               begin
                  --  Read the Refined_Depends aspect
                  Get_Depends (Subprogram           => Subprogram,
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
         Debug ("reads",     Globals.Inputs);
         Debug ("writes",    Globals.Outputs);

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

            Get_Depends (Subprogram           => Subprogram,
                         Scope                => Scope,
                         Classwide            => Classwide,
                         Depends              => D_Map,
                         Use_Computed_Globals => Use_Deduced_Globals);

            --  Always OK to call direct_mapping here since you can't refer
            --  to hidden state in user-written depends contracts.

            for C in D_Map.Iterate loop
               declare
                  Output : Flow_Id          renames Dependency_Maps.Key (C);
                  Inputs : Flow_Id_Sets.Set renames D_Map (C);
               begin
                  --  Filter function'Result and parameters
                  if Present (Output) then
                     declare
                        E : constant Entity_Id :=
                          Get_Direct_Mapping_Id (Output);
                     begin
                        if E /= Subprogram
                          and then not Params.Contains (E)
                        then
                           Globals.Outputs.Include
                             (Change_Variant (Output, Out_View));
                        end if;
                     end;
                  end if;

                  for Input of Inputs loop
                     pragma Assert (Input.Kind in Null_Value
                                                | Magic_String
                                                | Direct_Mapping);
                     --  Unlike Output, which is either a Null_Value or a
                     --  Direct_Mapping, Input might be also a Magic_String,
                     --  when an extra "null => proof_in" dependency is added
                     --  from a generated Refined_Global.

                     if Input.Kind = Magic_String
                       or else
                        (Input.Kind = Direct_Mapping
                           and then
                         not Params.Contains (Get_Direct_Mapping_Id (Input)))
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

            Debug ("reads",  Globals.Inputs);
            Debug ("writes", Globals.Outputs);
         end;

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

      elsif Gnat2Why_Args.Flow_Generate_Contracts
        and then Use_Deduced_Globals
      then

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

   -----------------------------------
   -- Get_Postcondition_Expressions --
   -----------------------------------

   function Get_Postcondition_Expressions (E       : Entity_Id;
                                           Refined : Boolean)
                                           return Node_Lists.List
   is
      P_Expr : Node_Lists.List;
      P_CC   : Node_Lists.List;
   begin
      case Ekind (E) is
         when Entry_Kind | E_Function | E_Procedure =>
            if Refined then
               P_Expr := Find_Contracts (E, Pragma_Refined_Post);
            else
               P_Expr := Find_Contracts (E, Pragma_Postcondition);
               P_CC   := Find_Contracts (E, Pragma_Contract_Cases);

               if Is_Dispatching_Operation (E) then
                  for Post of Classwide_Pre_Post (E, Pragma_Postcondition) loop
                     P_Expr.Append (Post);
                  end loop;
               end if;

               --  If a Contract_Cases aspect was found then we pull out
               --  every right-hand-side.
               if not P_CC.Is_Empty then

                  --  At the most one Contract_Cases expression is allowed
                  pragma Assert (P_CC.Length = 1);

                  declare
                     Consequence : Node_Id :=
                       First (Component_Associations (P_CC.First_Element));

                  begin
                     loop
                        P_Expr.Append (Expression (Consequence));
                        Next (Consequence);

                        exit when No (Consequence);
                     end loop;
                  end;
               end if;
            end if;

         when E_Package =>
            if Refined then
               P_Expr := Node_Lists.Empty_List;
            else
               P_Expr := Find_Contracts (E, Pragma_Initial_Condition);
            end if;

         when others =>
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
      Contract_Cases           : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Contract_Cases);
   begin
      if Is_Dispatching_Operation (E) then
         for Pre of Classwide_Pre_Post (E, Pragma_Precondition) loop
            Precondition_Expressions.Append (Pre);
         end loop;
      end if;

      --  If a Contract_Cases aspect was found then we pull out every
      --  condition apart from the others.
      if not Contract_Cases.Is_Empty then
         declare
            Contract_Case : Node_Id :=
              First (Component_Associations (Contract_Cases.First_Element));

            Case_Guard : Node_Id;

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
      end if;

      return Precondition_Expressions;

   end Get_Precondition_Expressions;

   -----------------------
   -- Get_Proof_Globals --
   -----------------------

   procedure Get_Proof_Globals (Subprogram      :     Entity_Id;
                                Reads           : out Flow_Id_Sets.Set;
                                Writes          : out Flow_Id_Sets.Set;
                                Erase_Constants :     Boolean;
                                Scop            :     Flow_Scope :=
                                  Null_Flow_Scope)
   is
      Globals : Global_Flow_Ids;

      S : constant Flow_Scope :=
        (if Present (Scop)
         then Scop
         else Get_Flow_Scope (if Entity_Body_In_SPARK (Subprogram)
                              then Get_Body_Entity (Subprogram)
                              else Subprogram));

      function Only_Mutable
        (Objects : Flow_Id_Sets.Set)
      return Flow_Id_Sets.Set
      with Pre  => Erase_Constants,
           Post => Flow_Id_Sets.Is_Subset (Subset => Only_Mutable'Result,
                                           Of_Set => Objects);
      --  Returns those of Objects that are mutable in Why3

      ------------------
      -- Only_Mutable --
      ------------------

      function Only_Mutable
        (Objects : Flow_Id_Sets.Set)
         return Flow_Id_Sets.Set
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

   --  Start of processing for Get_Proof_Globals

   begin
      if Is_Derived_Type (Subprogram) then
         E := Root_Type (Subprogram);

         pragma Assert (Ekind (E) = E_Task_Type
                          and then not Is_Derived_Type (E)
                          and then Entity_In_SPARK (E));
      else
         E := Subprogram;
      end if;

      --  For predicate functions we generate globals on the fly as any objects
      --  referenced in the predicate expression (except for the predicate type
      --  itself, which is represented by the formal parameter of a predicate
      --  function).

      if Ekind (E) = E_Function
        and then Is_Predicate_Function (E)
      then
         declare
            Param : constant Entity_Id := First_Formal (E);

         begin
            for V of Get_Variables_For_Proof
              (Expr_N  => Get_Expr_From_Return_Only_Func (E),
               Scope_N => Etype (First_Formal (E)))
            loop
               if V.Kind = Direct_Mapping
                 and then V.Node = Param
               then
                  null;
               else
                  Reads.Include (V);
               end if;
            end loop;
         end;

         Writes := Flow_Id_Sets.Empty_Set;

      --  Otherwise, we rely on the flow analysis

      else
         Get_Globals
           (Subprogram          => E,
            Scope               => S,
            Classwide           => True,
            Globals             => Globals,
            Use_Deduced_Globals => True);

         --  Expand all variables; it is more efficent to process Proof_Ins and
         --  Reads separaterly, because they are disjoint and there is no point
         --  in computing their union.
         Reads := Flow_Id_Sets.Union
           (Expand_Abstract_States (Globals.Proof_Ins),
            Expand_Abstract_States (Globals.Inputs));

         Writes := Expand_Abstract_States (Globals.Outputs);
      end if;

      if Erase_Constants then
         Reads  := Only_Mutable (Reads);
         Writes := Only_Mutable (Writes);
      end if;
   end Get_Proof_Globals;

   --------------
   -- Get_Type --
   --------------

   function Get_Type (F     : Flow_Id;
                      Scope : Flow_Scope)
                      return Entity_Id
   is
      E : constant Entity_Id :=
        (case F.Kind is
         when Direct_Mapping => Get_Direct_Mapping_Id (F),
         when Record_Field   => F.Component.Last_Element,
         when others         => raise Program_Error);
   begin
      return Get_Type (E, Scope);
   end Get_Type;

   function Get_Type (N     : Node_Id;
                      Scope : Flow_Scope)
                      return Entity_Id
   is
      T : Entity_Id;
      --  Will be assigned the type of N
   begin
      T :=
        (if Nkind (N) = N_Defining_Identifier
           and then Is_Type (N)
         then
            --  If N is of Type_Kind then T is N
            N
         elsif Nkind (N) in N_Has_Etype then
            --  If Etype is Present then use that
            Etype (N)
         else
            --  We don't expect to get any other kind of node
            raise Program_Error);

      if T = Standard_Void_Type then
         pragma Assert (Nkind (N) = N_Defining_Identifier and then
                        Ekind (N) = E_Abstract_State);

         return T;
      else
         loop
            pragma Loop_Invariant (Is_Type (T));

            declare
               Full_V : constant Entity_Id := Full_View (T);

            begin
               if Present (Full_V)
                 and then Entity_In_SPARK (Full_V)
                 and then Is_Visible (Full_V, Scope)
               then
                  T := Full_V;
               else
                  exit;
               end if;
            end;
         end loop;

         --  We do not want to return an Itype so we recurse on T's Etype if
         --  it different to T. If we cannot do any better then we will in
         --  fact return an Itype.

         if Is_Itype (T)
           and then not Is_Nouveau_Type (T)
         then
            T := Get_Type (Etype (T), Scope);
         end if;

         return T;
      end if;
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

         when E_Task_Type =>
            --  A task sees itself as a formal parameter
            return E;

         when others =>
            raise Program_Error;

      end case;
   end Get_Implicit_Formal;

   -----------------
   -- Get_Formals --
   -----------------

   function Get_Formals
     (E : Entity_Id)
      return Node_Sets.Set
   is
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
      Use_Computed_Globals    : Boolean;
      Assume_In_Expression    : Boolean := True;
      Expand_Internal_Objects : Boolean := False)
      return Flow_Id_Sets.Set
   is
      Vars : Flow_Id_Sets.Set;

   begin
      for Ref_Kind in Reference_Kind loop
         Vars.Union
           (Get_Variables (N                       => N,
                           Scope                   => Scope,
                           Fold_Functions          => Ref_Kind,
                           Use_Computed_Globals    => Use_Computed_Globals,
                           Assume_In_Expression    => Assume_In_Expression,
                           Expand_Internal_Objects => Expand_Internal_Objects,
                           Consider_Extensions     => False));
      end loop;

      return Vars;
   end Get_All_Variables;

   -------------------
   -- Get_Variables --
   -------------------

   type Get_Variables_Context is record
      Scope                   : Flow_Scope;
      Fold_Functions          : Reference_Kind;
      Use_Computed_Globals    : Boolean;
      Assume_In_Expression    : Boolean;
      Expand_Internal_Objects : Boolean;
      Consider_Extensions     : Boolean;
   end record;

   function Get_Variables_Internal
     (N   : Node_Id;
      Ctx : Get_Variables_Context)
      return Flow_Id_Sets.Set;
   --  Internal version with a context that we'll use to recurse

   function Get_Variables_Internal
     (L   : List_Id;
      Ctx : Get_Variables_Context)
      return Flow_Id_Sets.Set;
   --  Internal version with a context that we'll use to recurse

   -------------------
   -- Get_Variables --
   -------------------

   function Get_Variables
     (N                       : Node_Id;
      Scope                   : Flow_Scope;
      Fold_Functions          : Reference_Kind;
      Use_Computed_Globals    : Boolean;
      Assume_In_Expression    : Boolean := True;
      Expand_Internal_Objects : Boolean := False;
      Consider_Extensions     : Boolean := False)
      return Flow_Id_Sets.Set
   is
      Ctx : constant Get_Variables_Context :=
        (Scope                   => Scope,
         Fold_Functions          => Fold_Functions,
         Use_Computed_Globals    => Use_Computed_Globals,
         Assume_In_Expression    => Assume_In_Expression,
         Expand_Internal_Objects => Expand_Internal_Objects,
         Consider_Extensions     => Consider_Extensions);

   begin
      return Get_Variables_Internal (N, Ctx);
   end Get_Variables;

   function Get_Variables
     (L                       : List_Id;
      Scope                   : Flow_Scope;
      Fold_Functions          : Reference_Kind;
      Use_Computed_Globals    : Boolean;
      Assume_In_Expression    : Boolean := True;
      Expand_Internal_Objects : Boolean := False)
      return Flow_Id_Sets.Set
   is
      Ctx : constant Get_Variables_Context :=
        (Scope                   => Scope,
         Fold_Functions          => Fold_Functions,
         Use_Computed_Globals    => Use_Computed_Globals,
         Assume_In_Expression    => Assume_In_Expression,
         Expand_Internal_Objects => Expand_Internal_Objects,
         Consider_Extensions     => False);

   begin
      return Get_Variables_Internal (L, Ctx);
   end Get_Variables;

   ----------------------------
   -- Get_Variables_Internal --
   ----------------------------

   function Get_Variables_Internal (N   : Node_Id;
                                    Ctx : Get_Variables_Context)
                                    return Flow_Id_Sets.Set
   is

      ----------------------------------------------------
      -- Subprograms that do *not* write into Variables --
      ----------------------------------------------------

      function Do_Subprogram_Call (Callsite : Node_Id) return Flow_Id_Sets.Set
      with Pre => Nkind (Callsite) in N_Entry_Call_Statement
                                    | N_Subprogram_Call;
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
      with Pre => Ekind (E) in E_Constant
                             | E_Loop_Parameter
                             | E_Variable
                             | Formal_Kind
                    or else
                  Is_Concurrent_Component_Or_Discr (E);
      --  Return a set that can be merged into Variables, as above

      function Recurse (N                   : Node_Id;
                        Consider_Extensions : Boolean := False)
                        return Flow_Id_Sets.Set;
      --  Helper function to recurse on N

      function Untangle_Record_Fields
        (N                       : Node_Id;
         Scope                   : Flow_Scope;
         Fold_Functions          : Reference_Kind;
         Use_Computed_Globals    : Boolean;
         Expand_Internal_Objects : Boolean)
         return Flow_Id_Sets.Set
      with Pre => Nkind (N) = N_Selected_Component
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

      function Untangle_With_Context (N : Node_Id)
                                      return Flow_Id_Sets.Set
      is (Untangle_Record_Fields
           (N,
            Scope                   => Ctx.Scope,
            Fold_Functions          => Ctx.Fold_Functions,
            Use_Computed_Globals    => Ctx.Use_Computed_Globals,
            Expand_Internal_Objects => Ctx.Expand_Internal_Objects));
      --  Helper function to call Untangle_Record_Fields with the appropriate
      --  context.

      -------------
      -- Recurse --
      -------------

      function Recurse (N                   : Node_Id;
                        Consider_Extensions : Boolean := False)
                        return Flow_Id_Sets.Set
      is
         New_Ctx : Get_Variables_Context := Ctx;
      begin
         New_Ctx.Consider_Extensions := Consider_Extensions;
         return Get_Variables_Internal (N, New_Ctx);
      end Recurse;

      ------------------
      -- Merge_Entity --
      ------------------

      function Merge_Entity (E : Entity_Id) return Flow_Id_Sets.Set is
      begin
         if Is_Concurrent_Component_Or_Discr (E) then
            return Flatten_Variable (Add_Component
                                     (Direct_Mapping_Id (Scope (E)), E),
                                     Ctx.Scope);

         elsif Is_Part_Of_Concurrent_Object (E) then
            return Flatten_Variable
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
         Subprogram : constant Entity_Id := Get_Called_Entity (Callsite);

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
            function May_Use_Extensions return Boolean is
              (Has_Extensions_Visible (Subprogram)
                 or else
               Is_Class_Wide_Type (Get_Type (Formal, Ctx.Scope)));
            --  True if we have the aspect set (so we know the subprogram might
            --  convert to a classwide type), or we're dealing with a classwide
            --  type directly (since that may or may not have extensions).

         begin
            --  When detecting Inputs and Null_Deps we use the Depends
            --  contract, if present; when detecting Proof_Ins, we go straight
            --  to the actual expression.

            case Ctx.Fold_Functions is
               when Inputs =>
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
                              Ctx'Update
                                (Fold_Functions      => Inputs,
                                 Consider_Extensions => May_Use_Extensions)));
                     else
                        V.Union (Recurse (Actual, May_Use_Extensions));
                     end if;
                  else
                     V.Union (Recurse (Actual, May_Use_Extensions));
                  end if;
            end case;
         end Handle_Parameter;

         procedure Handle_Parameters is
            new Iterate_Call_Parameters (Handle_Parameter);

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
               Get_Depends (Subprogram           => Subprogram,
                            Scope                => Ctx.Scope,
                            Classwide            =>
                              Flow_Classwide.Is_Dispatching_Call (Callsite),
                            Depends              => Depends,
                            Use_Computed_Globals => Ctx.Use_Computed_Globals);

               pragma Assert (Depends.Length in 1 .. 2);
               --  For functions Depends always mentions the 'Result
               --  (user-written or synthesized) and possibly also null.

               case Ctx.Fold_Functions is
                  when Inputs =>
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
                  when Inputs =>
                     if Ekind (Subprogram) = E_Function
                       and then Has_Depends (Subprogram)
                     then
                        if Used_Reads.Contains (Implicit_Actual) then
                           V.Union
                             (if Is_External_Call (Callsite)
                              then Recurse (Prefix (Name (Callsite)))
                              else Flatten_Variable (Implicit_Actual,
                                                     Ctx.Scope));
                        end if;
                     else
                        V.Union
                          (if Is_External_Call (Callsite)
                           then Recurse (Prefix (Name (Callsite)))
                           else Flatten_Variable (Implicit_Actual,
                                                  Ctx.Scope));
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
                                    Ctx'Update (Fold_Functions => Inputs)));
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

         Handle_Parameters (Callsite);

         --  Determine the global effects of the called program

         Get_Globals (Subprogram          => Subprogram,
                      Scope               => Ctx.Scope,
                      Classwide           =>
                        Flow_Classwide.Is_Dispatching_Call (Callsite),
                      Globals             => Globals,
                      Use_Deduced_Globals => Ctx.Use_Computed_Globals);

         Remove_Constants (Globals.Proof_Ins);
         Remove_Constants (Globals.Inputs);

         --  Handle globals; very much like in Handle_Parameter

         case Ctx.Fold_Functions is
            when Inputs =>
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
         then
            Error_Msg_NE
              (Msg => "side effects of function & are not modeled in SPARK",
               N   => Callsite,
               E   => Subprogram);
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

         case Ekind (E) is
            --------------------------------------------
            -- Entities requiring some kind of action --
            --------------------------------------------

            when E_Constant =>
               if Ctx.Expand_Internal_Objects
                 and then not Comes_From_Source (E)
               then

                  --  To expand synthesized constants, we need to find the
                  --  original expression and find the variable set of that.

                  declare
                     Obj_Decl : constant Node_Id := Parent (E);

                     pragma Assert
                       (Nkind (Obj_Decl) = N_Object_Declaration,
                        "Bad parent of constant entity");

                     Expr : constant Node_Id := Expression (Obj_Decl);

                     pragma Assert
                       (Present (Expr),
                        "Constant has no expression");

                  begin
                     return Recurse (Expr);
                  end;

               else

                  --  Note that for constants of a constrained record or
                  --  concurrent type we want to detect their discriminant
                  --  constraints so we add them as well.

                  if Has_Variable_Input (E) then
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
               | Formal_Kind
            =>
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

               --  Ignore discriminants and components unless they come from
               --  task or protected types.

               if Ekind (E) in E_Discriminant | E_Component
                 and then Ekind (Scope (E)) not in E_Protected_Type
                                                 | E_Task_Type
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
                       (Direct_Mapping_Id (Unique_Entity (E),
                                           Facet => Extension_Part));
                  end if;

                  return Vars;
               end;

           --  Types mostly get dealt with by membership tests here, but
           --  sometimes they just appear (for example in a for loop over
           --  a type).

            when Type_Kind =>

               --  These kinds of types are not allowed in SPARK (yet)
               pragma Assert (Ekind (E) not in E_Exception_Type
                                             | E_Subprogram_Type);

               if Is_Scalar_Type (E)
                 and then Is_Constrained (E)
               then
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

            when Named_Kind
               | E_Enumeration_Literal
            =>
               --  All of these are simply constants, with no flow concern
               null;

            when E_Entry
               | E_Function
               | E_Procedure
            =>
               --  Dealt with when dealing with N_Subprogram_Call nodes, except
               --  when traversing the AST looking for first use of a variable.
               pragma Assert (not Ctx.Assume_In_Expression);

            when E_Block
               | E_Exception
               | E_Label
               | E_Loop
               | E_Package
            =>
               --  Nothing to do for these directly; we get them while
               --  traversing a list of statements or an identifier.
               null;

            -------------------------------------------
            -- Entities not expected or not in SPARK --
            -------------------------------------------

            --  Entities related to generic units are not in SPARK itself (we
            --  analyze instantiations instead of generics).

            when Formal_Object_Kind
               | Generic_Unit_Kind
            =>
               raise Program_Error;

            --  Frontend rewrites calls to operators into function calls

            when E_Operator =>
               raise Program_Error;

            --  Entry families are not in SPARK yet

            when E_Entry_Family
               | E_Entry_Index_Parameter
            =>
               raise Program_Error;

            --  Abstract state cannot directly appear in expressions

            when E_Abstract_State =>
               raise Program_Error;

            when E_Package_Body
               | E_Protected_Object
               | E_Protected_Body
               | E_Return_Statement
               | E_Subprogram_Body
               | E_Task_Body
               | E_Void
            =>
               raise Program_Error;

         end case;

         return Flow_Id_Sets.Empty_Set;
      end Do_Entity;

      ----------------------------
      -- Do_Attribute_Reference --
      ----------------------------

      function Do_Attribute_Reference (N : Node_Id) return Flow_Id_Sets.Set
      is
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
            when Attribute_Result =>
               pragma Assert (Ekind (Entity (Prefix (N))) = E_Function);

               --  It is an over-approximation to return all components of the
               --  'Result, but it is actually harmless, because in the Post
               --  expression the entire 'Result object must be initialized
               --  anyway.

               return
                 Flatten_Variable (Entity (Prefix (N)), Ctx.Scope);

            when Attribute_Update =>
               if Is_Tagged_Type (Get_Type (N, Ctx.Scope)) then
                  --  ??? Precise analysis is disabled for tagged types, so we
                  --      just do the usual instead.
                  null;

               else
                  return Untangle_With_Context (N);
               end if;

            when Attribute_Constrained =>
               for F of Recurse (Prefix (N)) loop
                  if F.Kind in Direct_Mapping | Record_Field
                    and then F.Facet = Normal_Part
                    and then Has_Bounds (F, Ctx.Scope)
                  then
                     --  This is not a bound variable, but it requires
                     --  bounds tracking. We make it a bound variable.
                     Variables.Include
                       (F'Update (Facet => The_Bounds));

                  elsif Is_Discriminant (F) then
                     Variables.Include (F);

                  end if;
               end loop;
               return Variables;

            when Attribute_First
               | Attribute_Last
               | Attribute_Length
               | Attribute_Range
            =>
               declare
                  T : constant Entity_Id := Get_Type (Prefix (N), Ctx.Scope);

                  LB : Node_Id;
                  HB : Node_Id;
                  --  Low and high bounds, respectively

                  Dims  : Pos;
                  Index : Node_Id;
                  --  Number of dimensions and index for multi-dimensional
                  --  arrays.

               begin
                  if Is_Constrained (T) then
                     if Is_Array_Type (T) then
                        if Present (Expressions (N)) then
                           Dims :=
                             UI_To_Int (Intval (First (Expressions (N))));
                           Index := First_Index (T);

                           for J in 1 .. Dims - 1 loop
                              Next_Index (Index);
                           end loop;

                           LB := Type_Low_Bound  (Etype (Index));
                           HB := Type_High_Bound (Etype (Index));

                        else
                           LB := Type_Low_Bound  (Etype (First_Index (T)));
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
                             (F'Update (Facet => The_Bounds));

                        else
                           --  This is something else, we just copy it
                           Variables.Include (F);
                        end if;
                     end loop;
                  end if;
               end;
               return Variables;

            when Attribute_Loop_Entry =>
               --  Again, we ignore loop entry references, these are dealt with
               --  by Do_Pragma and Do_Loop_Statement in the CFG construction.
               return Flow_Id_Sets.Empty_Set;

            when Attribute_Address =>
               --  The address of anything is totally separate from anything
               --  flow analysis cares about, so we ignore it.
               return Flow_Id_Sets.Empty_Set;

            when Attribute_Body_Version
               | Attribute_Version
            =>
               --  Attributes 'Version and 'Body_Version for flow analysis are
               --  like references to hidden static constants, so we ignore it.
               return Flow_Id_Sets.Empty_Set;

            when Attribute_Callable
               | Attribute_Caller
               | Attribute_Count
               | Attribute_Terminated
            =>
               --  Add the implicit use of
               --  Ada.Task_Identification.Tasking_State
               Variables.Union
                 (Flatten_Variable (RTE (RE_Tasking_State), Ctx.Scope));

               --  We also need to do the usual

            when others =>
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

         Variables.Union (Recurse (Prefix (N)));

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
         Fold_Functions          : Reference_Kind;
         Use_Computed_Globals    : Boolean;
         Expand_Internal_Objects : Boolean)
         return Flow_Id_Sets.Set
      is
         function Is_Ignored_Attribute (N : Node_Id) return Boolean;
         --  Returns True if N denotes an attribute 'Old or 'Loop_Entry, which
         --  are ignored when detecting references to variables.

         function Is_Ignored_Attribute (N : Node_Id) return Boolean
         is (Nkind (N) = N_Attribute_Reference
               and then
             Attribute_Name (N) in Name_Old | Name_Loop_Entry);

         function Get_Vars_Wrapper (N : Node_Id) return Flow_Id_Sets.Set
         is (Get_Variables
             (N,
              Scope                   => Scope,
              Fold_Functions          => Fold_Functions,
              Use_Computed_Globals    => Use_Computed_Globals,
              Expand_Internal_Objects => Expand_Internal_Objects));

         M             : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;

         Root_Node     : Node_Id := N;

         Component     : Node_Lists.List := Node_Lists.Empty_List;
         Seq           : Node_Lists.List := Node_Lists.Empty_List;

         Comp_Id       : Positive;
         Current_Field : Flow_Id;

         Must_Abort    : Boolean := False with Ghost;

         All_Vars      : Flow_Id_Sets.Set          := Flow_Id_Sets.Empty_Set;
         Depends_Vars  : Flow_Id_Sets.Set          := Flow_Id_Sets.Empty_Set;
         Proof_Vars    : constant Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

      --  Start of processing for Untangle_Record_Fields

      begin
         if Debug_Trace_Untangle_Fields then
            Write_Str ("Untangle_Record_Field on ");
            Sprint_Node_Inline (N);
            Write_Eol;
            Indent;
         end if;

         --  First, we figure out what the root node is. For example in
         --  Foo.Bar'Update(...).Z the root node will be Foo.
         --
         --  We also note all components (bar, z), 'update nodes and the order
         --  in which they access or update fields (bar, the_update, z).

         while Nkind (Root_Node) = N_Selected_Component
           or else
             (Is_Attribute_Update (Root_Node)
              and then
              Is_Record_Type (Unchecked_Full_Type (Etype (Root_Node))))
           or else
             Is_Ignored_Attribute (Root_Node)
         loop
            if Nkind (Root_Node) = N_Selected_Component then
               Component.Prepend
                 (Unique_Component
                    (Entity (Selector_Name (Root_Node))));
            end if;

            if not Is_Ignored_Attribute (Root_Node) then
               Seq.Prepend (Root_Node);
            end if;

            Root_Node := Prefix (Root_Node);

         end loop;

         if Root_Node = N then

            --  In some case Arr'Update (...) we need to make sure that Seq
            --  contains the 'Update so that the early abort can handle things.
            Root_Node  := Prefix (N);
            Seq.Prepend (N);
            Must_Abort := True;
         end if;

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

         --  If the root node is not an entire record variable, we recurse here
         --  and then simply merge all variables we find here and then abort.

         if not (Nkind (Root_Node) in N_Identifier | N_Expanded_Name
                   and then
                 Is_Record_Type
                   (Unchecked_Full_Type (Etype (Root_Node))))
         then
            return Vars : Flow_Id_Sets.Set do

               --  Recurse on root

               Vars := Get_Vars_Wrapper (Root_Node);

               --  Add anything we might find in 'Update expressions

               for N of Seq loop
                  case Nkind (N) is
                  when N_Attribute_Reference =>
                     pragma Assert (Is_Attribute_Update (N));
                     pragma Assert (List_Length (Expressions (N)) = 1);

                     declare
                        Component_Association : Node_Id :=
                          First (Component_Associations
                                   (First (Expressions (N))));

                     begin
                        loop
                           Vars.Union
                             (Get_Vars_Wrapper (Component_Association));
                           Next (Component_Association);
                           exit when No (Component_Association);
                        end loop;
                     end;

                  when N_Selected_Component =>
                     null;

                  when others =>
                     raise Why.Unexpected_Node;
                  end case;
               end loop;

               if Debug_Trace_Untangle_Fields then
                  Write_Str ("Early delegation return: ");
                  Print_Node_Set (Vars);
                  Outdent;
               end if;
            end return;
         end if;

         --  Ok, so the root is an entire object, so we can untangle it further

         pragma Assert (Nkind (Root_Node) in N_Identifier | N_Expanded_Name);
         pragma Assert (not Must_Abort);

         --  If the root is a constant without variable inputs and we are
         --  looking for genuine inputs, then we will find none.

         if Fold_Functions = Inputs
           and then Ekind (Entity (Root_Node)) = E_Constant
           and then not Has_Variable_Input (Entity (Root_Node))
         then
            return Flow_Id_Sets.Empty_Set;
         end if;

         --  We set up an identity map of all fields of the original record.
         --  For example a record with two fields would produce this kind of
         --  map:
         --
         --     r.x -> r.x
         --     r.y -> r.y

         declare
            Root_Entity : constant Entity_Id := Entity (Root_Node);

            pragma Assert
              (Ekind (Root_Entity) in E_Constant
                                    | E_Variable
                                    | E_Loop_Parameter -- for cursors
                                    | Formal_Kind
                 or else
               (Ekind (Root_Entity) in E_Discriminant | E_Component
                  and then
                Is_Concurrent_Type (Sinfo.Scope (Root_Entity))));

         begin
            if Is_Protected_Component (Root_Entity) then
               Comp_Id       := 2;
               Current_Field :=
                 Add_Component
                   (Direct_Mapping_Id (Sinfo.Scope (Root_Entity)),
                    Root_Entity);

            elsif Is_Part_Of_Concurrent_Object (Root_Entity) then
               Comp_Id       := 2;
               Current_Field :=
                 Add_Component
                   (Direct_Mapping_Id
                      (Etype (Encapsulating_State (Root_Entity))),
                    Root_Entity);

            else
               Comp_Id       := 1;
               Current_Field := Direct_Mapping_Id (Root_Entity);
            end if;

            for F of Flatten_Variable (Current_Field, Scope) loop
               M.Insert (F, Flow_Id_Sets.To_Set (F));
            end loop;

            if Debug_Trace_Untangle_Fields then
               Print_Flow_Map (M);
            end if;
         end;

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
            if Debug_Trace_Untangle_Fields then
               Write_Str ("Processing: ");
               Print_Node_Briefly (N);
            end if;

            case Nkind (N) is
            when N_Attribute_Reference =>
               pragma Assert (Is_Attribute_Update (N));
               pragma Assert (List_Length (Expressions (N)) = 1);

               if Debug_Trace_Untangle_Fields then
                  Write_Str ("Updating the map at ");
                  Sprint_Flow_Id (Current_Field);
                  Write_Eol;
               end if;

               --  We update the map as requested
               declare
                  Component_Association : Node_Id :=
                    First (Component_Associations (First (Expressions (N))));
                  Choice                : Node_Id;
                  --  Iterators for the 'Update (...) expression

                  Expr_Vars : Flow_Id_Sets.Set;
                  FS        : Flow_Id_Sets.Set;

                  E : Entity_Id;

               begin
                  Indent;
                  while Present (Component_Association) loop
                     Choice := First (Choices (Component_Association));
                     while Present (Choice) loop
                        E := Unique_Component (Entity (Choice));

                        if Debug_Trace_Untangle_Fields then
                           Write_Str ("Updating component ");
                           Sprint_Node_Inline (E);
                           Write_Eol;
                        end if;

                        --  Composite update

                        if Is_Record_Type (Get_Type (E, Scope)) then

                           --  We should call Untangle_Record_Aggregate here.
                           --  For now we us a safe default (all fields depend
                           --  on everything).

                           case Nkind (Expression (Component_Association)) is
                              --  when N_Aggregate =>
                              --     null;

                              when others =>
                                 if Fold_Functions = Inputs then
                                    Expr_Vars :=
                                      Get_Vars_Wrapper
                                        (Expression (Component_Association));

                                    --  Not sure what to do, so set all
                                    --  sensible fields to the given variables.

                                    FS :=
                                      Flatten_Variable
                                        (Add_Component (Current_Field, E),
                                         Scope);

                                    for F of FS loop
                                       M.Replace (F, Expr_Vars);
                                    end loop;

                                 else
                                    All_Vars.Union
                                      (Get_Variables
                                         (N                       =>
                                            Expression (Component_Association),
                                          Scope                   => Scope,
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
                              Expr_Vars :=
                                Get_Vars_Wrapper
                                  (Expression (Component_Association));

                              M.Replace
                                (Add_Component (Current_Field, E), Expr_Vars);
                           else
                              All_Vars.Union
                                (Get_Variables
                                   (N                       =>
                                      Expression (Component_Association),
                                    Scope                   => Scope,
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

                        Next (Choice);
                     end loop;
                     Next (Component_Association);
                  end loop;
                  Outdent;
               end;

            when N_Selected_Component =>
               declare
                  Comp : constant Entity_Id := Entity (Selector_Name (N));
                  Root_Entity : constant Entity_Id := Entity (Root_Node);

                  pragma Assert (Ekind (Comp) in E_Component
                                               | E_Discriminant);

                  pragma Assert (Is_Object (Root_Entity));

                  E : constant Entity_Id := Unique_Component (Comp);

                  New_Map : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;

               begin
                  --  We trim the result map

                  if Debug_Trace_Untangle_Fields then
                     Write_Str ("Trimming for: ");
                     Sprint_Node_Inline (E);
                     Write_Eol;
                  end if;

                  for C in M.Iterate loop
                     declare
                        K : Flow_Id          renames Flow_Id_Maps.Key (C);
                        V : Flow_Id_Sets.Set renames M (C);

                     begin
                        if K.Kind = Record_Field
                          and then Natural (K.Component.Length) >= Comp_Id
                          and then K.Component (Comp_Id) = E
                        then
                           New_Map.Insert (K, V);
                        end if;
                     end;
                  end loop;

                  Flow_Id_Maps.Move (Target => M,
                                     Source => New_Map);

                  Current_Field := Add_Component (Current_Field, E);
                  Comp_Id       := Comp_Id + 1;
               end;

            when others =>
               raise Why.Unexpected_Node;
            end case;

            if Debug_Trace_Untangle_Fields then
               Print_Flow_Map (M);
            end if;
         end loop;

         --  We merge what is left after trimming

         for S of M loop
            Depends_Vars.Union (S);
         end loop;

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
            when N_Ignored_In_SPARK =>
               return Skip;

            when N_Entry_Call_Statement
               | N_Function_Call
               | N_Procedure_Call_Statement
            =>
               pragma Assert (not Ctx.Assume_In_Expression or else
                                Nkind (N) = N_Function_Call);

               Variables.Union (Do_Subprogram_Call (N));
               return Skip;

            --  Operator nodes represent calls to intrinsic subprograms, which
            --  we assume to have Global => null. Variables referenced as
            --  operator parameters will be picked when processing their own
            --  nodes.

            when N_Op =>
               pragma Assert (Is_Intrinsic_Subprogram (Entity (N)));

            when N_Abstract_Subprogram_Declaration
               | N_Body_Stub
               | N_Entry_Body
               | N_Entry_Declaration
               | N_Package_Declaration
               | N_Proper_Body
               | N_Representation_Clause
               | N_Single_Task_Declaration
               | N_Subprogram_Declaration
               | N_Task_Type_Declaration
            =>
               pragma Assert (not Ctx.Assume_In_Expression);

               --  These should allow us to go through package specs and bodies
               return Skip;

            when N_Identifier | N_Expanded_Name =>
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
                     pragma Assert (not Comes_From_Source (Entity (N)));
                     Variables.Union
                       (Recurse (Expression (Parent (Entity (N)))));
                  else
                     Variables.Union (Do_Entity (Entity (N)));
                  end if;
               end if;
               return Skip;

            --  Within expression, a defining identifier only appears as a
            --  declaration for a compiler-generated temporary or as a
            --  parameter of a quantified expression (effectively, it declares
            --  a local object). Such identifiers are not considered as "uses"
            --  of any variable, so we ignore them.
            --
            --  ??? we also get here type indentifiers, when Get_Variables
            --  is called on an entire type declaration and not just on its
            --  constraint expressions; such calls of Get_Variables feel wrong.

            when N_Defining_Identifier =>
               if Is_Type (N) then
                  Variables.Union (Do_Entity (N));
               else
                  pragma Assert (Is_Internal (N)
                                  or else Is_Quantified_Loop_Param (N));
               end if;

            when N_Aggregate =>
               Variables.Union (Recurse (Aggregate_Bounds (N)));

            when N_Selected_Component =>
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

            when N_Type_Conversion =>
               if Is_Record_Type (Get_Type (N, Ctx.Scope)) then
                  --  We use Untangle_Record_Assignment as this can deal with
                  --  view conversions.

                  declare
                     M : constant Flow_Id_Maps.Map :=
                       Untangle_Record_Assignment
                         (N,
                          Map_Root                =>
                            Direct_Mapping_Id (Etype (N)),
                          Map_Type                =>
                            Get_Type (N, Ctx.Scope),
                          Scope                   => Ctx.Scope,
                          Fold_Functions          => Ctx.Fold_Functions,
                          Use_Computed_Globals    =>
                            Ctx.Use_Computed_Globals,
                          Expand_Internal_Objects =>
                            Ctx.Expand_Internal_Objects);

                  begin
                     for FS of M loop
                        Variables.Union (FS);
                     end loop;
                  end;

                  return Skip;

               else
                  return OK;
               end if;

            when N_Attribute_Reference =>
               Variables.Union (Do_Attribute_Reference (N));
               return Skip;

            when N_Membership_Test =>
               --  Membership tests involving type with predicates have the
               --  predicate flow into the variable set returned.

               declare
                  procedure Process_Type (E : Entity_Id);
                  --  Merge variables used in predicate functions for the given
                  --  type.

                  ------------------
                  -- Process_Type --
                  ------------------

                  procedure Process_Type (E : Entity_Id) is
                     P : constant Entity_Id := Predicate_Function (E);

                  begin
                     if Present (P) then

                        --  Filter the predicate function parameter from
                        --  variables referenced in the predicate, because the
                        --  parameter is only visible within that expression
                        --  (similar to what we do for quantified expression).

                        declare
                           Param : constant Entity_Id := First_Formal (P);

                        begin
                           for V of Recurse
                             (Get_Expr_From_Return_Only_Func (P))
                           loop
                              if V.Kind in Direct_Mapping | Record_Field
                                and then V.Node = Param
                              then
                                 null;
                              else
                                 Variables.Include (V);
                              end if;
                           end loop;
                        end;
                     end if;
                  end Process_Type;

                  P : Node_Id;

               begin
                  if Present (Right_Opnd (N)) then

                     --  x in t

                     P := Right_Opnd (N);
                     if Nkind (P) in N_Identifier | N_Expanded_Name
                        and then Is_Type (Entity (P))
                     then
                        Process_Type (Get_Type (P, Ctx.Scope));
                     end if;

                  else

                     --  x in t | 1 .. y | u

                     P := First (Alternatives (N));
                     loop
                        if Nkind (P) in N_Identifier | N_Expanded_Name
                          and then Is_Type (Entity (P))
                        then
                           Process_Type (Get_Type (P, Ctx.Scope));
                        end if;
                        Next (P);

                        exit when No (P);
                     end loop;
                  end if;
               end;

            when N_Quantified_Expression =>
               declare
                  pragma Assert
                    (Present (Iterator_Specification (N)) xor
                       Present (Loop_Parameter_Specification (N)));

                  It : constant Node_Id :=
                    (if Present (Iterator_Specification (N))
                     then Iterator_Specification (N)
                     else Loop_Parameter_Specification (N));

                  E : constant Entity_Id := Defining_Identifier (It);

               begin
                  Variables.Union (Recurse (It));

                  --  Filter the quantified expression parameter from variables
                  --  referenced in the predicate, because the parameter is
                  --  only visible within that predicate (similar to what we
                  --  do for type predicate expressions).

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

            when N_Allocator =>
               Variables.Include
                 (Direct_Mapping_Id (Flow.Dynamic_Memory.Heap_State));

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_More_Proc (Process => Proc);

   --  Start of processing for Get_Variables_Internal

   begin
      Traverse (N);

      --  Sanity check: no constants without variable inputs should come from
      --  the traversal.
      pragma Assert
        (for all V of Variables =>
           (if V.Kind in Direct_Mapping | Record_Field
              and then Ekind (V.Node) = E_Constant
            then Has_Variable_Input (V.Node)));

      Map_Generic_In_Formals (Ctx.Scope, Variables, Entire => False);

      return Variables;
   end Get_Variables_Internal;

   function Get_Variables_Internal (L   : List_Id;
                                    Ctx : Get_Variables_Context)
                                    return Flow_Id_Sets.Set
   is
      P : Node_Id;
   begin
      return Variables : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set do
         P := First (L);
         while Present (P) loop
            Variables.Union (Get_Variables_Internal
                               (P,
                                Ctx'Update (Consider_Extensions => False)));
            Next (P);
         end loop;
      end return;
   end Get_Variables_Internal;

   -----------------------------
   -- Get_Variables_For_Proof --
   -----------------------------

   function Get_Variables_For_Proof (Expr_N  : Node_Id;
                                     Scope_N : Node_Id)
                                     return Flow_Id_Sets.Set
   is
      Entire_Variables : Flow_Id_Sets.Set;

   begin
      --  Ignore references to array bounds of objects (because they are never
      --  mutable) but keep references to array bounds of components (becayse
      --  they might be mutable).

      for V of Get_All_Variables
        (Expr_N,
         Scope                   => Get_Flow_Scope (Scope_N),
         Use_Computed_Globals    => True,
         Assume_In_Expression    => True,
         Expand_Internal_Objects => False)
      loop
         if V.Kind = Direct_Mapping
           and then V.Facet = The_Bounds
         then
            null;
         else
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

   -----------------------
   -- Has_Proof_Globals --
   -----------------------

   function Has_Proof_Globals (Subprogram : Entity_Id) return Boolean is
      Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids : Flow_Types.Flow_Id_Sets.Set;
   begin
      Get_Proof_Globals (Subprogram      => Subprogram,
                         Reads           => Read_Ids,
                         Writes          => Write_Ids,
                         Erase_Constants => True);

      return not Read_Ids.Is_Empty or else not Write_Ids.Is_Empty;
   end Has_Proof_Globals;

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
         Variable_Input_Map.Insert (Key      => C,
                                    New_Item => Answer);

         return Answer;
      end;
   end Has_Variable_Input;

   ---------------------------------
   -- Has_Variable_Input_Internal --
   ---------------------------------

   function Has_Variable_Input_Internal (C : Entity_Id) return Boolean is
      E    : Entity_Id := C;
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
         E    := Full_View (E);
         Expr := Expression (Declaration_Node (E));
      end if;

      if not Entity_In_SPARK (E) then
         --  We are dealing with an entity that is not in SPARK so we assume
         --  that it does not have variable input.
         return False;
      end if;

      Vars := Get_Variables
        (Expr,
         Scope                => Get_Flow_Scope (E),
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
              (for some F of Get_Functions (Expr, Include_Predicates => False)
                 => not Has_User_Supplied_Globals (F)
                     and then
                    not In_Predefined_Unit (F));
         end if;

      --  If any variable was found then return True

      else
         return True;
      end if;

   end Has_Variable_Input_Internal;

   ----------------
   -- Has_Bounds --
   ----------------

   function Has_Bounds
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Boolean
   is
      T : Entity_Id;
   begin
      case F.Kind is
         when Null_Value | Synthetic_Null_Export | Magic_String =>
            return False;

         when Direct_Mapping =>
            T := Get_Type (F.Node, Scope);

         when Record_Field =>
            if F.Facet = Normal_Part then
               T := Get_Type (F.Component.Last_Element, Scope);
            else
               return False;
            end if;
      end case;

      return Is_Array_Type (T)
        and then not Is_Constrained (T);
   end Has_Bounds;

   ---------------------
   -- Is_Ghost_Entity --
   ---------------------

   function Is_Ghost_Entity (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            return Is_Ghost_Entity (Get_Direct_Mapping_Id (F));

         when Magic_String =>
            return GG_Is_Ghost_Entity (F.Name);

         when others =>
            return False;
      end case;
   end Is_Ghost_Entity;

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
               return Ekind (E) = E_Variable
                 and then Is_Constant_After_Elaboration (E);
            end;

         when Magic_String =>
            return GG_Is_CAE_Entity (F.Name);

         when others =>
            raise Program_Error;
      end case;
   end Is_Constant_After_Elaboration;

   -----------------------------------
   -- Is_Initialized_At_Elaboration --
   -----------------------------------

   function Is_Initialized_At_Elaboration (F : Flow_Id;
                                           S : Flow_Scope)
                                           return Boolean
   is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            return Is_Initialized_At_Elaboration (Get_Direct_Mapping_Id (F),
                                                  S);

         when Magic_String =>
            return GG_Is_Initialized_At_Elaboration (F.Name);

         when Synthetic_Null_Export =>
            return False;

         when Null_Value =>
            raise Program_Error;
      end case;
   end Is_Initialized_At_Elaboration;

   -------------------------------------
   -- Is_Initialized_In_Specification --
   -------------------------------------

   function Is_Initialized_In_Specification (F : Flow_Id;
                                             S : Flow_Scope)
                                             return Boolean
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

                  when others =>
                     pragma Assert (Nkind (Parent (E)) = N_Object_Declaration);
                     return Present (Expression (Parent (E)));

               end case;
            end;

         when Magic_String =>
            --  The fact it is a Magic_String instead of an entity means that
            --  it comes from another compilation unit (via an indirect call)
            --  and therefore has to have already been elaborated.
            return True;

         when others =>
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
            when N_Identifier | N_Expanded_Name =>
               return True;
            when N_Type_Conversion | N_Unchecked_Type_Conversion =>
               Ptr := Expression (Ptr);
            when N_Indexed_Component
               | N_Slice
               | N_Selected_Component
               | N_Explicit_Dereference
            =>
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
               --  Constants that are visibly of an access type are treated
               --  like variables. Hence using Is_Access_Type instead of
               --  Has_Access_Type here.

               if Ekind (E) = E_Constant then
                  return Is_Access_Type (Etype (E))
                    or else Has_Variable_Input (E);
               else
                  return True;
               end if;
            end;

         when Magic_String =>
            return True;

         --  Consider anything that is not a Direct_Mapping or a Record_Field
         --  to be a variable.

         when Synthetic_Null_Export =>
            return True;

         when Null_Value =>
            raise Program_Error;
      end case;
   end Is_Variable;

   --------------------
   -- Is_Constituent --
   --------------------

   function Is_Constituent (N : Node_Id) return Boolean
   is
      (Nkind (N) in N_Entity
       and then Ekind (N) in E_Abstract_State
                           | E_Constant
                           | E_Variable
       and then Present (Encapsulating_State (N))
       and then Ekind (Encapsulating_State (N)) = E_Abstract_State);

   -----------------------
   -- Is_Abstract_State --
   -----------------------

   function Is_Abstract_State (N : Node_Id) return Boolean
   is
     (Nkind (N) in N_Entity
      and then Ekind (N) = E_Abstract_State);

   ------------------------------
   -- Rely_On_Generated_Global --
   ------------------------------

   function Rely_On_Generated_Global
     (E     : Entity_Id;
      Scope : Flow_Scope)
      return Boolean
   is
   begin
      return Entity_Body_In_SPARK (E)
        and then Is_Visible (Get_Body (E), Scope)
        and then Refinement_Needed (E);
   end Rely_On_Generated_Global;

   ----------------------
   -- Remove_Constants --
   ----------------------

   procedure Remove_Constants
     (Objects : in out Flow_Id_Sets.Set)
   is
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
                    and then not Has_Variable_Input (E)
                  then
                     Constants.Insert (F);
                  end if;
               end;

            when Magic_String =>
               null;

            when Synthetic_Null_Export =>
               null;

            when Null_Value =>
               raise Program_Error;
         end case;
      end loop;

      Objects.Difference (Constants);
   end Remove_Constants;

   ----------------------------------------------
   -- Is_Generic_Actual_Without_Variable_Input --
   ----------------------------------------------

   function Is_Generic_Actual_Without_Variable_Input
     (E : Entity_Id)
      return Boolean
   is
     (Ekind (E) = E_Constant
      and then In_Generic_Actual (E)
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
     (Unit   : Entity_Id;
      Output : Entity_Id;
      Input  : Entity_Id := Empty)
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

            when N_Null =>
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

            when N_Attribute_Reference =>
               pragma Assert (Get_Attribute_Id (Attribute_Name (Item)) =
                              Attribute_Result);

               if Entity (Prefix (Item)) = Output then
                  Needle := First_Name_Node (Prefix (Item));
                  if Present (Input) then
                     Find_Input (Expression (N));
                  end if;
                  return;
               end if;

            --  Handle clauses like "(X, X.Y, Z'Result, Z.Y'Result) => ..."

            when N_Aggregate =>
               declare
                  Single_Item : Node_Id := First (Expressions (Item));

               begin
                  loop
                     case Nkind (Single_Item) is
                        when N_Identifier | N_Expanded_Name =>
                           if Canonical_Entity (Entity (Single_Item), Unit) =
                             Output
                           then
                              Needle := First_Name_Node (Single_Item);
                              if Present (Input) then
                                 Find_Input (Expression (N));
                              end if;
                              return;
                           end if;

                        when N_Attribute_Reference =>
                           pragma Assert
                             (Get_Attribute_Id (Attribute_Name (Single_Item)) =
                                Attribute_Result);

                           if Entity (Prefix (Single_Item)) = Output then
                              Needle := First_Name_Node (Prefix (Single_Item));
                              if Present (Input) then
                                 Find_Input (Expression (N));
                              end if;
                              return;
                           end if;

                        when others =>
                           raise Program_Error;
                     end case;

                     Next (Single_Item);

                     exit when No (Single_Item);
                  end loop;
               end;

            when others =>
               raise Program_Error;

         end case;
      end Find_Output;

      ----------------
      -- Find_Input --
      ----------------

      procedure Find_Input (N : Node_Id) is
      begin
         case Nkind (N) is
            when N_Null =>
               --  ??? a null RHS is syntactically possible, but this routine
               --  is not called in that case.
               raise Program_Error;

            --  Handle contracts like "... => X" and "... => X.Y"

            when N_Identifier | N_Expanded_Name =>
               if Canonical_Entity (Entity (N), Unit) = Input then
                  Needle := First_Name_Node (N);
               end if;

            --  Handle contracts like "... => (X, X.Y)"

            when N_Aggregate =>
               declare
                  Item : Node_Id := First (Expressions (N));

               begin
                  loop
                     pragma Assert
                       (Nkind (Item) in N_Identifier | N_Expanded_Name);

                     if Canonical_Entity (Entity (Item), Unit) = Input then
                        Needle := First_Name_Node (Item);
                        return;
                     end if;

                     Next (Item);

                     exit when No (Item);
                  end loop;
               end;

            when others =>
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

            when N_Null =>
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

            when others =>
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

         return (if Present (Needle)
                 then Needle
                 else Contract_N);
      else
         return Unit;
      end if;

   end Search_Depends_Contract;

   ---------------------------------
   -- Search_Initializes_Contract --
   ---------------------------------

   function Search_Initializes_Contract
     (Unit   : Entity_Id;
      Output : Entity_Id;
      Input  : Entity_Id := Empty)
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

            when N_Null =>
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

            when others =>
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

            when N_Aggregate =>
               declare
                  RHS : Node_Id := First (Expressions (N));

               begin
                  loop
                     pragma Assert
                       (Nkind (RHS) in N_Identifier | N_Expanded_Name);

                     if Canonical_Entity (Entity (RHS), Unit) = Input then
                        Needle := First_Name_Node (RHS);
                        return;
                     end if;

                     Next (RHS);

                     exit when No (RHS);
                  end loop;
               end;

            when others =>
               raise Program_Error;

         end case;
      end Scan_Inputs;

   --  Start of processing for Search_Initializes_Contract

   begin
      if Present (Contract) then
         Scan_Initialization_Spec (Expression (Get_Argument (Contract, Unit)));

         return (if Present (Needle)
                 then Needle
                 else Contract);
      else
         return Unit;
      end if;

   end Search_Initializes_Contract;

   --------------------
   -- To_Flow_Id_Set --
   --------------------

   function To_Flow_Id_Set
     (NS   : Name_Sets.Set;
      View : Flow_Id_Variant := Normal_Use)
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
      Scope                   : Flow_Scope;
      Fold_Functions          : Reference_Kind;
      Use_Computed_Globals    : Boolean;
      Expand_Internal_Objects : Boolean;
      Extensions_Irrelevant   : Boolean := True)
      return Flow_Id_Maps.Map
   is
      --  !!! Join/Merge need to be able to deal with private parts and
      --      extensions (i.e. non-normal facets).

      function Get_Vars_Wrapper (N : Node_Id) return Flow_Id_Sets.Set
      is (Get_Variables
            (N,
             Scope                   => Scope,
             Fold_Functions          => Fold_Functions,
             Use_Computed_Globals    => Use_Computed_Globals,
             Expand_Internal_Objects => Expand_Internal_Objects))
      with Pre => Nkind (N) in N_Subexpr;
      --  Helpful wrapper for calling Get_Variables

      function Recurse_On
        (N              : Node_Id;
         Map_Root       : Flow_Id;
         Map_Type       : Entity_Id := Empty;
         Ext_Irrelevant : Boolean   := Extensions_Irrelevant)
         return Flow_Id_Maps.Map
      is (Untangle_Record_Assignment
            (N,
             Map_Root                => Map_Root,
             Map_Type                => (if Present (Map_Type)
                                         then Map_Type
                                         else Get_Type (N, Scope)),
             Scope                   => Scope,
             Fold_Functions          => Fold_Functions,
             Use_Computed_Globals    => Use_Computed_Globals,
             Expand_Internal_Objects => Expand_Internal_Objects,
             Extensions_Irrelevant   => Ext_Irrelevant))
      with Pre => Nkind (N) in N_Subexpr
                    and then
                  (if not Extensions_Irrelevant
                   then not Ext_Irrelevant);
      --  Helpful wrapper for recursing. Note that once extensions are not
      --  irrelevant its not right to start ignoring them again.

      function Join (A, B   : Flow_Id;
                     Offset : Natural := 0)
                     return Flow_Id
      with Pre => A.Kind in Direct_Mapping | Record_Field and then
                  B.Kind in Direct_Mapping | Record_Field,
           Post => Join'Result.Facet = B.Facet;
      --  Glues components of B to A, starting at offset. For example
      --  consider A = Obj.X and B = R.X.Y and Offset = 1. Then joining
      --  will return Obj.X.Y.
      --
      --  Similarly, if A = Obj.X and B = R.X'Private_Part and Offset = 1,
      --  then joining will produce Obj.X'Private_Part.

      procedure Merge (M         : in out Flow_Id_Maps.Map;
                       Component : Entity_Id;
                       Input     : Node_Id)
      with Pre => Is_Unique_Component (Component)
                    and then
                  (No (Input) or else Nkind (Input) in N_Subexpr);
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
      --  aggregate), then we don't do anything.

      ----------
      -- Join --
      ----------

      function Join (A, B   : Flow_Id;
                     Offset : Natural := 0)
                     return Flow_Id
      is
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

      -----------
      -- Merge --
      -----------

      procedure Merge (M         : in out Flow_Id_Maps.Map;
                       Component : Entity_Id;
                       Input     : Node_Id)
      is
         F   : constant Flow_Id := Add_Component (Map_Root, Component);
         Tmp : Flow_Id_Maps.Map;
      begin
         case Ekind (Get_Type (Component, Scope)) is
            when Record_Kind =>
               if Present (Input) then
                  Tmp := Recurse_On (Input, F);

                  for C in Tmp.Iterate loop
                     declare
                        Output : Flow_Id          renames Flow_Id_Maps.Key (C);
                        Inputs : Flow_Id_Sets.Set renames Tmp (C);
                     begin
                        M.Insert (Output, Inputs);
                     end;
                  end loop;
               end if;

            when others =>
               declare
                  Outputs : constant Flow_Id_Sets.Set :=
                    Flatten_Variable (F, Scope);

                  Inputs  : constant Flow_Id_Sets.Set :=
                    Get_Vars_Wrapper (Input);

               begin
                  for Output of Outputs loop
                     M.Insert (Output, Inputs);
                  end loop;
               end;
         end case;
      end Merge;

      --  Local variables

      M : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;

   --  Start of processing for Untangle_Record_Assignment

   begin
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

      case Nkind (N) is
         when N_Aggregate =>
            pragma Assert (No (Expressions (N)));
            --  The front-end should rewrite this for us.

            if Debug_Trace_Untangle_Record then
               Write_Str ("processing aggregate");
               Write_Eol;
            end if;

            declare
               Component_Association : Node_Id;

               Input  : Node_Id;
               Target : Node_Id;
               Done   : Node_Sets.Set;

            begin
               Component_Association := First (Component_Associations (N));
               while Present (Component_Association) loop
                  if Box_Present (Component_Association) then
                     Input := Empty;
                  else
                     Input := Expression (Component_Association);
                  end if;
                  Target := First (Choices (Component_Association));
                  while Present (Target) loop
                     Merge (M, Component => Unique_Component (Entity (Target)),
                            Input => Input);
                     Done.Insert (Unique_Component (Entity (Target)));
                     --  ??? repeated calls to Unique_Component
                     Next (Target);
                  end loop;
                  Next (Component_Association);
               end loop;

               --  If the aggregate is more constrained than the type would
               --  suggest, we fill in the "missing" fields with null, so
               --  that they appear initialized.
               for Component of Unique_Components (Map_Type) loop
                  if not Done.Contains (Component) then
                     for F of
                       Flatten_Variable
                         (Add_Component (Map_Root, Component),
                          Scope)
                     loop
                        M.Insert (F, Flow_Id_Sets.Empty_Set);
                     end loop;
                  end if;
               end loop;
            end;

         when N_Selected_Component =>
            if Debug_Trace_Untangle_Record then
               Write_Line ("processing selected component");
            end if;

            declare
               Tmp : constant Flow_Id_Maps.Map :=
                 Recurse_On (Prefix (N),
                             Direct_Mapping_Id (Etype (Prefix (N))));

               Selector : constant Entity_Id :=
                 Unique_Component (Entity (Selector_Name (N)));

            begin
               for C in Tmp.Iterate loop
                  declare
                     Output : Flow_Id          renames Flow_Id_Maps.Key (C);
                     Inputs : Flow_Id_Sets.Set renames Tmp (C);

                  begin
                     if Output.Component.First_Element = Selector then
                        M.Insert (Join (Map_Root, Output, 1), Inputs);
                     end if;
                  end;
               end loop;
            end;

         when N_Identifier | N_Expanded_Name =>
            if Debug_Trace_Untangle_Record then
               Write_Str ("processing direct assignment");
               Write_Eol;
            end if;

            declare
               E : constant Entity_Id := Entity (N);

               Is_Pure_Constant : constant Boolean :=
                 Fold_Functions /= Inputs
                   or else
                 (Ekind (E) = E_Constant
                  and then not Has_Variable_Input (E));
               --  If we are assigning a pure constant, we don't really want to
               --  see it (just like if we assign integer/string/... literals
               --  then we don't want to see them in flow). However, we can't
               --  just pretend that the RHS is an empty map; it is a map
               --  (i.e. a certain structure) with empty elements, e.g. the
               --  private extension part.
               --  Same when we detect Proof_Ins/Null_Deps and see a plain
               --  object reference.

               LHS : constant Flow_Id_Sets.Set :=
                 Flatten_Variable (Map_Root, Scope);

               LHS_Ext : constant Flow_Id :=
                 Map_Root'Update (Facet => Extension_Part);

               RHS : Flow_Id_Sets.Set :=
                 (if Is_Concurrent_Component_Or_Discr (E) then
                    Flatten_Variable
                      (Add_Component
                         (Direct_Mapping_Id (Sinfo.Scope (E)),
                          E),
                       Scope)

                  elsif Is_Part_Of_Concurrent_Object (E) then
                    Flatten_Variable
                      (Add_Component
                         (Direct_Mapping_Id
                            (Etype (Encapsulating_State (E))),
                          E),
                       Scope)

                  else Flatten_Variable (E, Scope));

               To_Ext : Flow_Id_Sets.Set;
               F      : Flow_Id;

               LHS_Pos : Flow_Id_Maps.Cursor;
               Unused  : Boolean;

            begin
               if Extensions_Visible (E, Scope)
                 and then
                   ((Is_Class_Wide_Type (Map_Type)
                     and then not Is_Class_Wide_Type (Etype (N)))
                    or else not Extensions_Irrelevant)
               then
                  --  This is an implicit conversion to class wide, or we
                  --  for some other reason care specifically about the
                  --  extensions.
                  RHS.Insert (Direct_Mapping_Id (E,
                                                 Facet => Extension_Part));
                  --  RHS.Insert (Direct_Mapping_Id (E,
                  --                                 Facet => The_Tag));
               end if;

               for Input of RHS loop
                  F := Join (Map_Root, Input);
                  if LHS.Contains (F) then
                     M.Insert (F, (if Is_Pure_Constant
                               then Flow_Id_Sets.Empty_Set
                               else Flow_Id_Sets.To_Set (Input)));
                  else
                     To_Ext.Insert (Input);
                  end if;
               end loop;

               if not To_Ext.Is_Empty
                 and then Is_Tagged_Type (Map_Type)
               then
                  --  Attempt to insert an empty set
                  M.Insert (Key      => LHS_Ext,
                            Position => LHS_Pos,
                            Inserted => Unused);

                  if not Is_Pure_Constant then
                     M (LHS_Pos).Union (To_Ext);
                  end if;
               end if;
            end;

         when N_Type_Conversion =>
            if Debug_Trace_Untangle_Record then
               Write_Str ("processing type/view conversion");
               Write_Eol;
            end if;

            declare
               T_From : constant Entity_Id := Get_Type (Expression (N), Scope);
               T_To   : constant Entity_Id := Get_Type (N, Scope);

               --  To_Class_Wide : constant Boolean :=
               --    Is_Class_Wide_Type (T_To);

               Class_Wide_Conversion : constant Boolean :=
                 not Is_Class_Wide_Type (T_From)
                 and then Is_Class_Wide_Type (T_To);

               Tmp : constant Flow_Id_Maps.Map :=
                 Recurse_On (Expression (N),
                             Map_Root,
                             Ext_Irrelevant =>
                                not (Class_Wide_Conversion
                                     or not Extensions_Irrelevant));
               --  If we convert to a classwide type then any extensions
               --  are no longer irrelevant.

               Valid_To_Fields : Flow_Id_Sets.Set;

               The_Ext : constant Flow_Id :=
                 Map_Root'Update (Facet => Extension_Part);

               The_Tg : constant Flow_Id :=
                 Map_Root'Update (Facet => The_Tag);

            begin
               if Debug_Trace_Untangle_Record then
                  Write_Str ("from: ");
                  Sprint_Node_Inline (T_From);
                  Write_Str (" (" & Ekind (T_From)'Img & ")");
                  Write_Str (" to: ");
                  Sprint_Node_Inline (T_To);
                  Write_Str (" (" & Ekind (T_To)'Img & ")");
                  Write_Eol;

                  Write_Str ("temporary map: ");
                  Print_Flow_Map (Tmp);
               end if;

               for F of Flatten_Variable (T_To, Scope) loop
                  Valid_To_Fields.Insert (Join (Map_Root, F));
               end loop;

               for C in Tmp.Iterate loop
                  declare
                     Output : Flow_Id          renames Flow_Id_Maps.Key (C);
                     Inputs : Flow_Id_Sets.Set renames Tmp (C);

                  begin
                     if Valid_To_Fields.Contains (Output) then
                        M.Include (Output, Inputs);
                        Valid_To_Fields.Delete (Output);
                     end if;
                  end;
               end loop;

               if Valid_To_Fields.Contains (The_Tg) then
                  if not M.Contains (The_Tg) then
                     M.Include (The_Tg, Flow_Id_Sets.Empty_Set);
                  end if;
                  Valid_To_Fields.Delete (The_Tg);
               end if;

               if Valid_To_Fields.Contains (The_Ext) then
                  if not M.Contains (The_Ext) then
                     M.Include (The_Ext, Flow_Id_Sets.Empty_Set);
                  end if;
                  Valid_To_Fields.Delete (The_Ext);
                  M (The_Ext).Union (Valid_To_Fields);
               end if;
            end;

         when N_Qualified_Expression =>
            --  We can completely ignore these.
            M := Recurse_On (Expression (N), Map_Root, Map_Type);

         when N_Attribute_Reference =>
            case Get_Attribute_Id (Attribute_Name (N)) is
               when Attribute_Update =>
                  if Debug_Trace_Untangle_Record then
                     Write_Str ("processing update expression");
                     Write_Eol;
                  end if;

                  declare
                     pragma Assert (List_Length (Expressions (N)) = 1);
                     The_Aggregate : constant Node_Id :=
                       First (Expressions (N));
                     pragma Assert (No (Expressions (The_Aggregate)));

                     Output : Node_Id;
                     Input  : Node_Id;
                     Ptr    : Node_Id;
                     F      : Flow_Id;

                     Class_Wide_Conversion : constant Boolean :=
                       not Is_Class_Wide_Type (Get_Type (N, Scope))
                       and then Is_Class_Wide_Type (Map_Type);

                  begin
                     M := Recurse_On (Prefix (N),
                                      Map_Root,
                                      Ext_Irrelevant =>
                                        not (Class_Wide_Conversion or
                                               not Extensions_Irrelevant));

                     Ptr := First (Component_Associations (The_Aggregate));
                     while Present (Ptr) loop
                        pragma Assert (Nkind (Ptr) = N_Component_Association);

                        Input  := Expression (Ptr);
                        Output := First (Choices (Ptr));
                        while Present (Output) loop

                           F := Add_Component (Map_Root, Entity (Output));

                           if Is_Record_Type
                             (Get_Type (Entity (Output), Scope))
                           then
                              for C in Recurse_On (Input, F).Iterate loop
                                 M.Replace (Flow_Id_Maps.Key (C),
                                            Flow_Id_Maps.Element (C));
                              end loop;
                           else
                              M.Replace (F, Get_Vars_Wrapper (Input));
                           end if;

                           Next (Output);
                        end loop;

                        Next (Ptr);
                     end loop;
                  end;

               when Attribute_Result =>
                  if Debug_Trace_Untangle_Record then
                     Write_Str ("processing attribute result");
                     Write_Eol;
                  end if;

                  declare
                     Class_Wide_Conversion : constant Boolean :=
                       not Is_Class_Wide_Type (Get_Type (N, Scope))
                       and then Is_Class_Wide_Type (Map_Type);

                  begin
                     M := Recurse_On (Prefix (N),
                                      Map_Root,
                                      Ext_Irrelevant =>
                                         not (Class_Wide_Conversion
                                              or not Extensions_Irrelevant));
                  end;

               when others =>
                  Error_Msg_N ("cannot untangle attribute", N);
                  raise Why.Not_Implemented;
            end case;

         when N_Explicit_Dereference
            | N_Function_Call
            | N_Indexed_Component
            | N_Unchecked_Type_Conversion
         =>

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

         when others =>
            declare
               S : constant String := Nkind (N)'Img;

            begin
               Error_Msg_N ("cannot untangle node " & S, N);
               raise Why.Unexpected_Node;
            end;
      end case;

      if Debug_Trace_Untangle_Record then
         Outdent;

         Write_Str ("URA result: ");
         Print_Flow_Map (M);
      end if;

      return M;
   end Untangle_Record_Assignment;

   --------------------------------
   -- Untangle_Assignment_Target --
   --------------------------------

   procedure Untangle_Assignment_Target
     (N                    : Node_Id;
      Scope                : Flow_Scope;
      Use_Computed_Globals : Boolean;
      Vars_Defined         : out Flow_Id_Sets.Set;
      Vars_Used            : out Flow_Id_Sets.Set;
      Vars_Proof           : out Flow_Id_Sets.Set;
      Partial_Definition   : out Boolean)
   is
      --  Fold_Functions (a parameter for Get_Variables) is specified as
      --  `false' here because Untangle should only ever be called where we
      --  assign something to something. And you can't assign to function
      --  results (yet).

      function Get_Vars_Wrapper (N    : Node_Id;
                                 Fold : Reference_Kind)
                                 return Flow_Id_Sets.Set
      is (Get_Variables
            (N,
             Scope                => Scope,
             Fold_Functions       => Fold,
             Use_Computed_Globals => Use_Computed_Globals));

      Unused                   : Boolean;
      Base_Node                : Flow_Id;
      Seq                      : Node_Lists.List;

      Idx                      : Positive;
      Process_Type_Conversions : Boolean;

   --  Start of processing for Untangle_Assignment_Target

   begin

      if Debug_Trace_Untangle then
         Write_Str ("Untangle_Assignment_Target on ");
         Sprint_Node_Inline (N);
         Write_Eol;
         Indent;
      end if;

      Get_Assignment_Target_Properties
        (N,
         Partial_Definition => Partial_Definition,
         View_Conversion    => Unused,
         Map_Root           => Base_Node,
         Seq                => Seq);

      if Debug_Trace_Untangle then
         Write_Line ("Seq is:");
         Indent;
         for N of Seq loop
            Print_Tree_Node (N);
         end loop;
         Outdent;

         Write_Str ("Base_Node: ");
         Print_Flow_Id (Base_Node);
         Write_Eol;
      end if;

      --  We now set the variable(s) defined and will start to establish
      --  other variables that might be used.

      Vars_Defined := Flatten_Variable (Base_Node, Scope);

      if Debug_Trace_Untangle then
         Write_Str ("Components: ");
         Print_Node_Set (Vars_Defined);
      end if;

      Vars_Used    := Flow_Id_Sets.Empty_Set;
      Vars_Proof   := Flow_Id_Sets.Empty_Set;

      --  We go through the sequence. At each point we might do one of the
      --  following, depending on the operation:
      --
      --    * Type conversion: we trim the variables defined to remove the
      --      fields we no longer change. For this we use Idx to work out
      --      which level of components (in the Flow_Id) we are looking at.
      --
      --    * Array index and slice: we process the expressions and add to
      --      the variables used in code and proof. We also make sure to
      --      not process any future type conversions as flow analysis can
      --      no longer distinguish elements.
      --
      --    * Component selection: we increment Idx.

      Process_Type_Conversions := True;
      Idx                      := 1;

      for N of Seq loop
         case Valid_Assignment_Kinds (Nkind (N)) is
            when N_Type_Conversion =>
               if Process_Type_Conversions then
                  declare
                     Old_Typ  : constant Entity_Id := Etype (Expression (N));
                     New_Typ  : constant Entity_Id := Etype (N);

                     Old_Vars : constant Flow_Id_Sets.Set := Vars_Defined;

                     function In_Type (Old_Comp : Entity_Id) return Boolean is
                       (for some New_Comp of Unique_Components (New_Typ) =>
                           New_Comp = Old_Comp);

                  begin
                     if Is_Tagged_Type (Old_Typ)
                       and then Is_Tagged_Type (New_Typ)
                     then
                        Vars_Defined := Flow_Id_Sets.Empty_Set;
                        for F of Old_Vars loop
                           if F.Kind = Record_Field
                             and then In_Type (F.Component (Idx))
                           then
                              Vars_Defined.Include (F);
                           elsif F.Kind = Direct_Mapping then
                              case F.Facet is
                                 when Extension_Part =>
                                    if Is_Class_Wide_Type (New_Typ) then
                                       Vars_Defined.Include (F);
                                    end if;
                                 when others =>
                                    Vars_Defined.Include (F);
                              end case;
                           end if;
                        end loop;
                     else
                        Process_Type_Conversions := False;
                     end if;
                  end;
               end if;

            when N_Indexed_Component =>
               declare
                  Expr : Node_Id := First (Expressions (N));

               begin
                  while Present (Expr) loop
                     Vars_Used.Union
                       (Get_Vars_Wrapper (Expr, Fold => Inputs));
                     Vars_Proof.Union
                       (Get_Vars_Wrapper (Expr, Fold => Proof_Ins));

                     Next (Expr);
                  end loop;
               end;
               Process_Type_Conversions := False;

            when N_Slice =>
               Vars_Used.Union
                 (Get_Vars_Wrapper (Discrete_Range (N), Fold => Inputs));
               Vars_Proof.Union
                 (Get_Vars_Wrapper (Discrete_Range (N), Fold => Proof_Ins));

               Process_Type_Conversions := False;

            when N_Selected_Component
            =>
               Idx := Idx + 1;

            when N_Unchecked_Type_Conversion
               | N_Explicit_Dereference
            =>
               null;

            when others =>
               raise Why.Unexpected_Node;

         end case;
      end loop;

      if Nkind (N) = N_Type_Conversion
        and then Is_Class_Wide_Type (Etype (N))
        and then Extensions_Visible (Base_Node, Scope)
      then
         Vars_Defined.Include (Base_Node'Update (Facet => Extension_Part));
      end if;

      if Debug_Trace_Untangle then
         Write_Str ("Variables ");
         if Partial_Definition then
            Write_Str ("partially ");
         end if;
         Write_Str ("defined: ");
         Print_Node_Set (Vars_Defined);

         Write_Str ("Variables used: ");
         Print_Node_Set (Vars_Used);

         Write_Str ("Proof variables used: ");
         Print_Node_Set (Vars_Proof);

         Outdent;
      end if;
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
               when N_Record_Definition =>
                  --  Ordinary record declaration, we just check if its either
                  --  null or there are no components.
                  return No (Component_List (Def))
                    or else Null_Present (Component_List (Def));

               when N_Derived_Type_Definition =>
                  declare
                     Root_T : constant Entity_Id :=
                       Etype (Subtype_Indication (Def));
                     Ext    : constant Node_Id := Record_Extension_Part (Def);
                  begin
                     return Is_Empty_Record_Type (Root_T)
                       and then
                       (not Present (Ext)
                          or else Null_Present (Ext)
                          or else No (Component_List (Ext)));
                  end;

               when others =>
                  null;
            end case;

         when N_Subtype_Declaration =>
            --  A subtype can be null too, we just check if the thing we're
            --  deriving it from is null.
            return Is_Empty_Record_Type (Etype (Subtype_Indication (Decl)));

         when others =>
            null;
      end case;

      return False;
   end Is_Empty_Record_Type;

   -----------------------------
   -- Is_Dummy_Abstract_State --
   -----------------------------

   function Is_Dummy_Abstract_State
     (F : Flow_Id;
      S : Flow_Scope)
      return Boolean
   is
   begin
      if F.Kind = Direct_Mapping then
         declare
            E : constant Entity_Id := Get_Direct_Mapping_Id (F);
         begin
            return Ekind (E) = E_Abstract_State
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

      Contract := Find_Contract (E, Pragma_Refined_Global);

      if Present (Contract) then
         return Parse_Global_Contract (E, Contract);
      end if;

      Contract := Find_Contract (E, Pragma_Refined_Depends);

      if Present (Contract) then
         return Parse_Depends_Contract (E, Contract);
      end if;

      Contract := Find_Contract (E, Pragma_Global);

      if Present (Contract) then
         return Parse_Global_Contract (E, Contract);
      end if;

      Contract := Find_Contract (E, Pragma_Depends);

      if Present (Contract) then
         return Parse_Depends_Contract (E, Contract);
      end if;

      pragma Assert (Is_Pure (E));

      return (Proof_Ins => Node_Sets.Empty_Set,
              Inputs    => Node_Sets.Empty_Set,
              Outputs   => Node_Sets.Empty_Set);
   end Contract_Globals;

   ----------------------------
   -- Parse_Depends_Contract --
   ----------------------------

   function Parse_Depends_Contract
     (Subprogram   : Entity_Id;
      Depends_Node : Node_Id)
      return Raw_Global_Nodes
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
            Output : Flow_Id          renames Dependency_Maps.Key (C);
            Inputs : Flow_Id_Sets.Set renames Raw_Depends (C);

         begin
            pragma Assert (Output.Kind in Null_Value | Direct_Mapping);

            --  Filter function'Result and parameters
            if Present (Output) then
               declare
                  Item : constant Entity_Id := Get_Direct_Mapping_Id (Output);

               begin
                  if Item /= Subprogram
                    and then not Params.Contains (Item)
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
         return Ekind (E) = E_Abstract_State
           or else not Entity_In_SPARK (E);
      else
         return True;
      end if;
   end Is_Opaque_For_Proof;

   -------------
   -- Find_In --
   -------------

   function Find_In (User : Node_Sets.Set; G : Entity_Id) return Entity_Id
   is
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

   function Strip_Child_Prefixes (EN : String) return String is
     (if EN'Length > Child_Prefix'Length and then
      EN (EN'First .. EN'First + Child_Prefix'Length - 1) = Child_Prefix
      then Strip_Child_Prefixes (EN
                                 (EN'First + Child_Prefix'Length .. EN'Last))
      else EN);

   ---------------------
   -- Path_To_Flow_Id --
   ---------------------

   function Path_To_Flow_Id (Expr : Node_Id) return Flow_Id is
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
      while Nkind (N) not in N_Expanded_Name | N_Identifier loop
         Seq.Prepend (N);

         N :=
           (case Nkind (N) is
               when N_Explicit_Dereference
                  | N_Indexed_Component
                  | N_Slice
                  | N_Selected_Component
               =>
                  Prefix (N),

               when N_Qualified_Expression
                  | N_Type_Conversion
                  | N_Unchecked_Type_Conversion
               =>
                  Expression (N),

               when others =>
                  raise Program_Error);
      end loop;

      declare
         Root_Entity : constant Entity_Id := Entity (N);

      begin
         Obj :=
           (if Is_Protected_Component (Root_Entity) then
              Add_Component
                (Direct_Mapping_Id (Scope (Root_Entity)),
                 Root_Entity)

            elsif Is_Part_Of_Concurrent_Object (Root_Entity) then
              Add_Component
                (Direct_Mapping_Id
                   (Etype (Encapsulating_State (Root_Entity))),
                 Root_Entity)

            else
               Direct_Mapping_Id (Root_Entity));
      end;

      for N of Seq loop
         case Nkind (N) is
            when N_Explicit_Dereference
               | N_Indexed_Component
               | N_Slice
            =>
               return Obj;

            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion
            =>
               null;

            when N_Selected_Component =>
               Obj := Add_Component (Obj, Entity (Selector_Name (N)));

            when others =>
               raise Program_Error;
         end case;
      end loop;

      return Obj;
   end Path_To_Flow_Id;

end Flow_Utility;
