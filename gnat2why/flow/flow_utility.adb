------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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

with Ada.Characters.Latin_1;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Maps;
with Ada.Strings.Unbounded;           use Ada.Strings.Unbounded;

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

with Common_Iterators;                use Common_Iterators;
with Gnat2Why_Args;
with Gnat2Why.External_Axioms;        use Gnat2Why.External_Axioms;
with Gnat2Why.Util;
with SPARK_Definition;                use SPARK_Definition;
with SPARK_Frame_Conditions;          use SPARK_Frame_Conditions;
with SPARK_Util.External_Axioms;      use SPARK_Util.External_Axioms;
with SPARK_Util.Subprograms;          use SPARK_Util.Subprograms;
with SPARK_Util.Types;                use SPARK_Util.Types;
with Why;

with Flow_Classwide;
with Flow_Debug;                      use Flow_Debug;
with Flow_Generated_Globals.Phase_2;  use Flow_Generated_Globals.Phase_2;
with Flow_Refinement;                 use Flow_Refinement;
with Graphs;

package body Flow_Utility is

   use type Flow_Id_Sets.Set;

   ----------------------------------------------------------------------
   --  Debug
   ----------------------------------------------------------------------

   Debug_Record_Component      : constant Boolean := False;
   --  Enable this to generate record component pdf file.

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
   --  Component_Graphs
   ----------------------------------------------------------------------

   package Component_Graphs is new Graphs
     (Vertex_Key   => Entity_Id,
      Key_Hash     => Node_Hash,
      Edge_Colours => Natural,
      Null_Key     => Empty,
      Test_Key     => "=");

   Comp_Graph  : Component_Graphs.Graph;

   Temp_String : Unbounded_String := Null_Unbounded_String;

   procedure Add_To_Temp_String (S : String);
   --  Nasty nasty hack to add the given string to a global variable,
   --  Temp_String. We use this to pretty print nodes via Sprint_Node.

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

   package Component_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Entity_Id,
      Hash                => Component_Hash,
      Equivalent_Elements => Same_Component);

   function Components (E : Entity_Id) return Node_Lists.List
   with Pre => Is_Type (E);
   --  Return components in SPARK of the given entity E, similar to
   --  {First,Next}_Component_Or_Discriminant, with the difference that any
   --  components of private ancestors are included.
   --  @param E a type entity
   --  @return all component and discriminants of the type that are in SPARK or
   --    the empty list if none exists.

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

   ------------------------
   -- Add_To_Temp_String --
   ------------------------

   procedure Add_To_Temp_String (S : String) is
      Whitespace : constant Ada.Strings.Maps.Character_Set :=
        Ada.Strings.Maps.To_Set
        (" " & Ada.Characters.Latin_1.CR & Ada.Characters.Latin_1.LF);
   begin
      Append (Temp_String,
              Trim (To_Unbounded_String (S), Whitespace, Whitespace));
      Append (Temp_String, "\n");
   end Add_To_Temp_String;

   -------------------------------------------
   -- Collect_Functions_And_Read_Locked_POs --
   -------------------------------------------

   procedure Collect_Functions_And_Read_Locked_POs
     (N                  : Node_Id;
      Functions_Called   : out Node_Sets.Set;
      Tasking            : in out Tasking_Info;
      Generating_Globals : Boolean)
   is
      Scop : constant Flow_Scope := Get_Flow_Scope (N);

      function Proc (N : Node_Id) return Traverse_Result;
      --  If the node being processed is an N_Function_Call, store a
      --  corresponding Entity_Id; for protected functions store the
      --  read-locked protected object.

      procedure Process_Type (E : Entity_Id) with Pre => Generating_Globals;
      --  Merge predicate function for the given type

      ------------------
      -- Process_Type --
      ------------------

      procedure Process_Type (E : Entity_Id) is
         P : constant Entity_Id := Predicate_Function (E);
      begin
         if Present (P) then
            Functions_Called.Include (P);
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

            when N_In | N_Not_In =>
               --  Membership tests involving type with predicates have the
               --  predicate function appear during GG, but not in phase 2.
               --  See mirroring code in Get_Variables that deals with this
               --  as well.
               if Generating_Globals then
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

      procedure Traverse is new Traverse_Proc (Process => Proc);
      --  AST traversal procedure

   --  Start of processing for Collect_Functions_And_Read_Locked_POs

   begin
      Functions_Called := Node_Sets.Empty_Set;
      Traverse (N);
   end Collect_Functions_And_Read_Locked_POs;

   --------------------
   -- Component_Hash --
   --------------------

   function Component_Hash (E : Entity_Id) return Ada.Containers.Hash_Type is
     (if Is_Part_Of_Concurrent_Object (E)
      then Node_Hash (E)
      else Component_Graphs.Cluster_Hash
             (Comp_Graph.Get_Cluster (Comp_Graph.Get_Vertex (E))));

   ----------------
   -- Components --
   ----------------

   function Components (E : Entity_Id) return Node_Lists.List is
   begin
      if Is_Record_Type (E)
        or else Is_Concurrent_Type (E)
        or else Is_Incomplete_Or_Private_Type (E)
        or else Has_Discriminants (E)
      then
         declare
            function Up (E : Entity_Id) return Entity_Id with Pure_Function;
            --  Get parent type, but don't consider record subtypes' ancestors

            --------
            -- Up --
            --------

            function Up (E : Entity_Id) return Entity_Id is
               A : constant Entity_Id := Etype (E);
               B : Entity_Id;
            begin
               if Ekind (E) = E_Record_Subtype then
                  B := Up (A);
                  if A /= B then
                     return B;
                  else
                     return E;
                  end if;
               else
                  return A;
               end if;
            end Up;

            --  Local variables

            Ptr : Entity_Id;
            T   : Entity_Id          := E;
            L   : Node_Lists.List    := Node_Lists.Empty_List;
            S   : Component_Sets.Set := Component_Sets.Empty_Set;

         begin
            loop
               Ptr := First_Component_Or_Discriminant (T);
               while Present (Ptr) loop
                  declare
                     Inserted : Boolean;
                     Unused   : Component_Sets.Cursor;

                  begin
                     if Component_Is_Visible_In_SPARK (Ptr) then
                        S.Insert (New_Item => Ptr,
                                  Position => Unused,
                                  Inserted => Inserted);
                        if Inserted then
                           L.Append (Ptr);
                        end if;
                     end if;
                  end;
                  Next_Component_Or_Discriminant (Ptr);
               end loop;
               exit when Up (T) = T;
               T := Up (T);
            end loop;

            return L;
         end;

      --  No components or discriminants to return

      else
         return Node_Lists.Empty_List;
      end if;
   end Components;

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
               T : Entity_Id;
               --  Type of F

               Classwide : Boolean;
               --  True iff F has a classwide type

               Results : Flow_Id_Sets.Set;

               Contains_Non_Visible : Boolean := False;
               Root_Components      : Node_Sets.Set;

               subtype Private_Nonrecord_Kind is Private_Kind with
                 Static_Predicate =>
                   Private_Nonrecord_Kind not in E_Record_Type_With_Private |
                                                 E_Record_Subtype_With_Private;
               --  Non-record private types

               procedure Debug (Msg : String);
               --  Output debug message

               function Get_Root_Component (C : Entity_Id) return Entity_Id
               with Pre => Ekind (C) in E_Component | E_Discriminant;
               --  Returns C's equilavent component of the root type. If this
               --  is not available then E's Original_Record_Component is
               --  returned instead.
               --
               --  @param C is the component who's equivalent we are looking
               --    for
               --  @return the equivalent component of the root type if one
               --    exists or the Original_Record_Component of C otherwise.

               ------------------------
               -- Get_Root_Component --
               ------------------------

               function Get_Root_Component (C : Entity_Id) return Entity_Id is
                  ORC : constant Entity_Id := Original_Record_Component (C);
               begin
                  --  If Same_Component is True for one of the Root_Components
                  --  then return that instead.
                  for Comp of Root_Components loop
                     if Same_Component (ORC, Comp) then
                        return Comp;
                     end if;
                  end loop;

                  --  No Same_Component found. Fall back to C's
                  --  Original_Record_Component.
                  return ORC;
               end Get_Root_Component;

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

               T         := Get_Type (F, Scope);
               Classwide := Is_Class_Wide_Type (T);
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

               --  If we are dealing with a derived type then we want to get to
               --  the root, if this is in SPARK, and then populate the
               --  Root_Components set. However, we don't want to consider
               --  Itypes.
               if Is_Derived_Type (T)
                 and then not Full_View_Not_In_SPARK (T)
               then
                  declare
                     Root : Node_Id := T;

                  begin
                     while (Is_Derived_Type (Root) or else Is_Itype (Root))
                       and then Etype (Root) /= Root
                     loop
                        Root := Etype (Root);
                     end loop;

                     --  Make sure we have the Full_View
                     while Is_Private_Type (Root)
                       and then Present (Full_View (Root))
                     loop
                        Root := Full_View (Root);
                     end loop;

                     for Comp of Components (Root) loop
                        Root_Components.Include
                          (Original_Record_Component (Comp));
                     end loop;
                  end;
               end if;

               case Type_Kind'(Ekind (T)) is
                  when Private_Nonrecord_Kind =>
                     Debug ("processing private type");

                     if Has_Discriminants (T) then
                        for C of Components (T) loop
                           if Is_Visible (Get_Root_Component (C), Scope) then
                              Results.Include (Add_Component (F, C));
                           else
                              Contains_Non_Visible := True;
                           end if;
                        end loop;
                        Results.Include (F'Update (Facet => Private_Part));
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
                     if Components (T).Is_Empty then
                        --  If the record has an empty component list then we
                        --  add the variable itself...
                        --  Note that this happens also when the components are
                        --  hidden behind a SPARK_Mode => Off.
                        Results.Insert (F);

                     else
                        --  ...else we add each visible component
                        for Ptr of Components (T) loop
                           if Is_Visible (Get_Root_Component (Ptr), Scope) then
                              --  Here we union disjoint sets, so possibly we
                              --  could optimize this.
                              Results.Union
                                (Flatten_Variable
                                   (Add_Component (F, Ptr), Scope));

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
                           Results.Include (F'Update (Facet => Private_Part));
                        end if;
                     end if;

                     if Classwide then
                        --  Ids.Include (F'Update (Facet => The_Tag)); ???
                        Results.Include (F'Update (Facet => Extension_Part));
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
               Map_Root := Add_Component (Map_Root,
                                          Original_Record_Component
                                            (Entity (Selector_Name (N))));

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
      Use_Computed_Globals : Boolean := True;
      Callsite             : Node_Id := Empty)
   is
      pragma Unreferenced (Classwide);
      --  For now we assume classwide globals are the same as the actual
      --  globals.

      Depends_N : constant Node_Id :=
        Get_Contract_Node (Subprogram, Scope, Depends_Contract);

      pragma Assert
        (Present (Depends_N)
         and then Get_Pragma_Id (Depends_N) in Pragma_Depends
                                             | Pragma_Refined_Depends);

      Contract_Relation : constant Dependency_Maps.Map :=
        Parse_Depends (Depends_N);
      --  Step 1: Parse the appropriate dependency relation

      Trimming_Required : constant Boolean :=
        (Get_Pragma_Id (Depends_N) = Pragma_Depends
           and then Mentions_State_With_Visible_Refinement (Depends_N, Scope));
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
      --  Step 4: If we are dealing with a protected operation and the Callsite
      --  is present then we need to substitute references to the protected
      --  type with references to the protected object.
      ----------------------------------------------------------------------

      if Present (Callsite)
        and then Ekind (Sinfo.Scope (Subprogram)) = E_Protected_Type
        and then Is_External_Call (Callsite)
      then
         declare
            The_PO : constant Entity_Id :=
              Get_Enclosing_Object (Prefix (Name (Callsite)));

            PO_Type : constant Entity_Id := Sinfo.Scope (Subprogram);

            pragma Assert (Ekind (The_PO) = E_Variable);

         begin
            --  Substitute reference on LHS

            if Depends.Contains (Direct_Mapping_Id (PO_Type)) then
               declare
                  Position : Dependency_Maps.Cursor;
                  Inserted : Boolean;

               begin
                  Depends.Insert (Key      => Direct_Mapping_Id (The_PO),
                                  Position => Position,
                                  Inserted => Inserted);

                  pragma Assert (Inserted);

                  Flow_Id_Sets.Move
                    (Target => Depends (Position),
                     Source => Depends (Direct_Mapping_Id (PO_Type)));

                  Depends.Delete (Direct_Mapping_Id (PO_Type));
               end;
            end if;

            --  Substitute references on RHS

            for Inputs of Depends loop
               declare
                  C : constant Flow_Id_Sets.Cursor :=
                    Inputs.Find (Direct_Mapping_Id (PO_Type));

               begin
                  if Flow_Id_Sets.Has_Element (C) then
                     Inputs.Replace_Element
                       (Position => C,
                        New_Item => Direct_Mapping_Id (The_PO));
                  end if;
               end;
            end loop;
         end;
      end if;

      ----------------------------------------------------------------------
      --  Step 5: If we are dealing with a task unit T then, as per SPARK RM
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
     (Scop : Flow_Scope; Objects : in out Flow_Id_Sets.Set)
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
                                Fold_Functions       => True,
                                Use_Computed_Globals => False);

                        begin
                           --  Retain the variant of the original Object, which
                           --  is either In_View for those coming from
                           --  Get_Global or Normal_Use for those coming from
                           --  other contexts.

                           Mapped.Union
                             (Change_Variant (To_Entire_Variables (Inputs),
                                              Object.Variant));
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

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Scope                  : Flow_Scope;
                          Classwide              : Boolean;
                          Globals                : out Global_Flow_Ids;
                          Use_Deduced_Globals    : Boolean := True;
                          Ignore_Depends         : Boolean := False)
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
              and then Mentions_State_With_Visible_Refinement
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
         else Get_Flow_Scope ((if Entity_Body_In_SPARK (Subprogram)
                               then Get_Body_Entity (Subprogram)
                               else Subprogram)));

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

      Get_Globals
        (Subprogram          => E,
         Scope               => S,
         Classwide           => True,
         Globals             => Globals,
         Use_Deduced_Globals => True);

      --  Expand all variables; it is more efficent to process Proof_Ins and
      --  Reads separaterly, because they are disjoint and there is no point
      --  in computing their union.
      Reads := Flow_Id_Sets.Union (Expand_Abstract_States (Globals.Proof_Ins),
                                   Expand_Abstract_States (Globals.Inputs));

      Writes := Expand_Abstract_States (Globals.Outputs);

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
         elsif Present (Defining_Identifier (N)) then
            --  N can be some kind of type declaration
            Defining_Identifier (N)
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

   -------------------
   -- Get_Variables --
   -------------------

   type Get_Variables_Context is record
      Scope                        : Flow_Scope;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean;
      Assume_In_Expression         : Boolean;
      Expand_Synthesized_Constants : Boolean;
      Consider_Extensions          : Boolean;
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
     (N                            : Node_Id;
      Scope                        : Flow_Scope;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Assume_In_Expression         : Boolean := True;
      Expand_Synthesized_Constants : Boolean := False;
      Consider_Extensions          : Boolean := False)
      return Flow_Id_Sets.Set
   is
      Ctx : constant Get_Variables_Context :=
        (Scope                        => Scope,
         Fold_Functions               => Fold_Functions,
         Use_Computed_Globals         => Use_Computed_Globals,
         Reduced                      => Reduced,
         Assume_In_Expression         => Assume_In_Expression,
         Expand_Synthesized_Constants => Expand_Synthesized_Constants,
         Consider_Extensions          => Consider_Extensions);

   begin
      return Get_Variables_Internal (N, Ctx);
   end Get_Variables;

   function Get_Variables
     (L                            : List_Id;
      Scope                        : Flow_Scope;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Assume_In_Expression         : Boolean := True;
      Expand_Synthesized_Constants : Boolean := False)
      return Flow_Id_Sets.Set
   is
      Ctx : constant Get_Variables_Context :=
        (Scope                        => Scope,
         Fold_Functions               => Fold_Functions,
         Use_Computed_Globals         => Use_Computed_Globals,
         Reduced                      => Reduced,
         Assume_In_Expression         => Assume_In_Expression,
         Expand_Synthesized_Constants => Expand_Synthesized_Constants,
         Consider_Extensions          => False);

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

      function Do_Entity (E : Entity_Id) return Flow_Id_Sets.Set
      with Pre => Nkind (E) in N_Entity;
      --  Process the given entity and return the variables associated with it

      function Do_N_Attribute_Reference (N : Node_Id) return Flow_Id_Sets.Set
      with Pre => Nkind (N) = N_Attribute_Reference;
      --  Process the given attribute reference. Do not follow children after
      --  calling this.

      procedure Merge_Entity (Variables : in out Flow_Id_Sets.Set;
                              E         : Entity_Id)
      with Pre => Nkind (E) in N_Entity;
      --  Add the given entity to Variables, respecting the Context (in
      --  particular the flag Reduced).

      function Merge_Entity (E : Entity_Id) return Flow_Id_Sets.Set
      with Pre => Nkind (E) in N_Entity;
      --  Return a set that can be merged into Variables, as above

      function Recurse (N                   : Node_Id;
                        Consider_Extensions : Boolean := False)
                        return Flow_Id_Sets.Set;
      --  Helper function to recurse on N

      function Untangle_Record_Fields
        (N                            : Node_Id;
         Scope                        : Flow_Scope;
         Fold_Functions               : Boolean;
         Use_Computed_Globals         : Boolean;
         Expand_Synthesized_Constants : Boolean)
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
      --  Scope, Use_Computed_Globals, Expand_Synthesized_Constants will be
      --  passed on to Get_Variables if necessary.
      --
      --  Get_Variables will be called with Reduced set to False (as this
      --  function should never be called when it's True...).

      function Untangle_With_Context (N : Node_Id)
                                      return Flow_Id_Sets.Set
      is (Untangle_Record_Fields
           (N,
            Scope                        => Ctx.Scope,
            Fold_Functions               => Ctx.Fold_Functions,
            Use_Computed_Globals         => Ctx.Use_Computed_Globals,
            Expand_Synthesized_Constants =>
              Ctx.Expand_Synthesized_Constants));
      --  Helper function to call Untangle_Record_Fields with the appropriate
      --  context.

      function Discriminant_Constraints (E : Entity_Id)
                                         return Flow_Id_Sets.Set
      with Pre => Ekind (E) in E_Constant
                             | E_Variable
                             | E_Component;
      --  Returns the discriminant constraints for E if it is of a record or
      --  concurrent type with discriminants, returns the empty set otherwise.

      ------------------------------
      -- Discriminant_Constraints --
      ------------------------------

      function Discriminant_Constraints (E : Entity_Id)
                                         return Flow_Id_Sets.Set
      is
         Typ : constant Entity_Id := Etype (E);
      begin
         if (Is_Record_Type (Typ)
             or else Is_Concurrent_Type (Typ))
           and then Is_Constrained (Typ)
           and then Has_Discriminants (Typ)
         then
            declare
               Discriminants : Flow_Id_Sets.Set;

            begin
               --  Loop over the list of discriminant constraints
               for Discr of Iter (Discriminant_Constraint (Typ)) loop
                  Discriminants.Union (Recurse (Discr));
               end loop;

               return Discriminants;
            end;
         else
            return Flow_Id_Sets.Empty_Set;
         end if;
      end Discriminant_Constraints;

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

      procedure Merge_Entity (Variables : in out Flow_Id_Sets.Set;
                              E         : Entity_Id)
      is
      begin
         Variables.Union (Merge_Entity (E));
      end Merge_Entity;

      function Merge_Entity (E : Entity_Id) return Flow_Id_Sets.Set is
      begin
         if Ctx.Reduced then
            if Is_Concurrent_Component_Or_Discr (E) then
               return
                 Flow_Id_Sets.To_Set (Direct_Mapping_Id (Scope (E)));

            elsif Is_Part_Of_Concurrent_Object (E) then
               return
                 Flow_Id_Sets.To_Set
                   (Direct_Mapping_Id (Etype (Encapsulating_State (E))));

            else
               return
                 Flow_Id_Sets.To_Set (Direct_Mapping_Id (Unique_Entity (E)));
            end if;
         else
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
           Ctx.Fold_Functions
           and then Ekind (Subprogram) = E_Function
           and then Has_Depends (Subprogram);

         Used_Reads : Flow_Id_Sets.Set;

         V          : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

         procedure Handle_Parameter (Formal : Entity_Id; Actual : Node_Id);
         --  Processing related to parameter of a call

         ----------------------
         -- Handle_Parameter --
         ----------------------

         procedure Handle_Parameter (Formal : Entity_Id; Actual : Node_Id)
         is
            May_Use_Extensions : constant Boolean :=
              Has_Extensions_Visible (Subprogram) or else
              Ekind (Get_Type (Formal, Ctx.Scope)) in Class_Wide_Kind;
            --  True if we have the aspect set (so we know the subprogram might
            --  convert to a classwide type), or we're dealing with a classwide
            --  type directly (since that may or may not have extensions).
         begin
            if not Folding
              or else Used_Reads.Contains (Direct_Mapping_Id (Formal))
            then
               V.Union (Recurse (Actual, May_Use_Extensions));
            end if;
         end Handle_Parameter;

         procedure Handle_Parameters is
            new Iterate_Call_Parameters (Handle_Parameter);

      --  Start of processing for Do_Subprogram_Call

      begin
         --  Determine the global effects of the called program

         Get_Globals (Subprogram          => Subprogram,
                      Scope               => Ctx.Scope,
                      Classwide           =>
                        Flow_Classwide.Is_Dispatching_Call (Callsite),
                      Globals             => Globals,
                      Use_Deduced_Globals => Ctx.Use_Computed_Globals);

         if not Ctx.Fold_Functions then

            --  If we fold functions we're interested in real world, otherwise
            --  (this case) we're interested in the proof world too.

            Globals.Inputs.Union (Globals.Proof_Ins);
         end if;

         --  If this is an external call to protected subprogram then we also
         --  need to add the enclosing object to the variables we're using.
         --  This is not needed for internal calls, since the enclosing object
         --  already is an implicit parameter of the caller.

         if Ekind (Scope (Subprogram)) = E_Protected_Type
           and then Is_External_Call (Callsite)
         then
            Merge_Entity
              (V,
               Get_Enclosing_Object (Prefix (Name (Callsite))));
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
                            Use_Computed_Globals => Ctx.Use_Computed_Globals,
                            Callsite             => Callsite);

               pragma Assert (Depends.Length in 1 .. 2);
               --  For functions Depends always mentions the 'Result
               --  (user-written or synthesized) and possibly also null.

               Flow_Id_Sets.Move
                 (Target => Used_Reads,
                  Source => Depends (Direct_Mapping_Id (Subprogram)));
            end;
         end if;

         --  Apply sanity check for functions

         if Nkind (Callsite) = N_Function_Call
           and then not Globals.Outputs.Is_Empty
         then
            Error_Msg_NE
              (Msg => "side effects of function & are not modeled in SPARK",
               N   => Callsite,
               E   => Subprogram);
         end if;

         --  Merge globals into the variables used

         for G of Globals.Inputs loop
            if not Folding
              or else Used_Reads.Contains (Change_Variant (G, Normal_Use))
            then
               V.Include (Change_Variant (G, Normal_Use));
               if Extensions_Visible (G, Ctx.Scope)
                 and then not Ctx.Reduced
               then
                  V.Include (Change_Variant (G, Normal_Use)'Update
                               (Facet => Extension_Part));
               end if;
            end if;
         end loop;

         for G of Globals.Outputs loop
            V.Include (Change_Variant (G, Normal_Use));
            if Extensions_Visible (G, Ctx.Scope) and then not Ctx.Reduced then
               V.Include (Change_Variant (G, Normal_Use)'Update
                            (Facet => Extension_Part));
            end if;
         end loop;

         --  Merge the actuals into the set of variables used

         Handle_Parameters (Callsite);

         --  Finally, expand the collected set (if necessary)

         if Ctx.Reduced then
            return V;
         else
            return R : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set do
               for Tmp of V loop
                  if Tmp.Kind = Record_Field then
                     R.Include (Tmp);
                  else
                     R.Union (Flatten_Variable (Tmp, Ctx.Scope));
                  end if;
               end loop;
            end return;
         end if;
      end Do_Subprogram_Call;

      ---------------
      -- Do_Entity --
      ---------------

      function Do_Entity (E : Entity_Id) return Flow_Id_Sets.Set is
      begin
         case Ekind (E) is
            --------------------------------------------
            -- Entities requiring some kind of action --
            --------------------------------------------

            when E_Constant =>
               if Ctx.Expand_Synthesized_Constants
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

                  return Merge_Entity (E) or Discriminant_Constraints (E);
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

                  if not Ctx.Reduced
                    and then Ctx.Consider_Extensions
                    and then Extensions_Visible (E, Ctx.Scope)
                  then
                     Vars.Include
                       (Direct_Mapping_Id (Unique_Entity (E),
                                           Facet => Extension_Part));
                  end if;

                  --  For variables of a constrained record or concurrent type
                  --  we want to detect their discriminant constraints.

                  if Ekind (E) = E_Variable then
                     Vars.Union (Discriminant_Constraints (E));
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
               --  Dealt with when dealing with N_Subprogram_Call nodes
               null;

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

      ------------------------------
      -- Do_N_Attribute_Reference --
      ------------------------------

      function Do_N_Attribute_Reference (N : Node_Id) return Flow_Id_Sets.Set
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
            when Attribute_Update =>
               if Ctx.Reduced or else Is_Tagged_Type (Get_Type (N, Ctx.Scope))
               then
                  --  !!! Precise analysis is disabled for tagged types, so we
                  --      just do the usual instead.
                  null;

               else
                  return Untangle_With_Context (N);
               end if;

            when Attribute_Constrained =>
               if not Ctx.Reduced then
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
               else
                  null;
                  --  Otherwise, we do the usual
               end if;

            when Attribute_First
               | Attribute_Last
               | Attribute_Length
               | Attribute_Range
            =>
               declare
                  T  : constant Entity_Id := Get_Type (Prefix (N), Ctx.Scope);
                  pragma Assert (Nkind (T) in N_Entity);
                  LB : Node_Id;
                  HB : Node_Id;
               begin
                  if Is_Constrained (T) then
                     if Is_Array_Type (T) then
                        LB := Type_Low_Bound (Etype (First_Index (T)));
                        HB := Type_High_Bound (Etype (First_Index (T)));
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

                  elsif not Ctx.Reduced then
                     for F of Recurse (Prefix (N)) loop
                        if F.Kind in Direct_Mapping | Record_Field
                          and then F.Facet = Normal_Part
                          and then Has_Bounds (F, Ctx.Scope)
                        then
                           --  This is not a bound variable, but it requires
                           --  bounds tracking. We make it a bound variable.
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

            when Attribute_Callable
               | Attribute_Caller
               | Attribute_Count
               | Attribute_Terminated
            =>
               --  Add the implicit use of
               --  Ada.Task_Identification.Tasking_State
               Merge_Entity (Variables, RTE (RE_Tasking_State));

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
      end Do_N_Attribute_Reference;

      ----------------------------
      -- Untangle_Record_Fields --
      ----------------------------

      function Untangle_Record_Fields
        (N                            : Node_Id;
         Scope                        : Flow_Scope;
         Fold_Functions               : Boolean;
         Use_Computed_Globals         : Boolean;
         Expand_Synthesized_Constants : Boolean)
      return Flow_Id_Sets.Set
      is
         function Is_Ignored_Node (N : Node_Id) return Boolean
         is (Nkind (N) = N_Attribute_Reference
             and then
             Get_Attribute_Id (Attribute_Name (N)) in
               Attribute_Old | Attribute_Loop_Entry);

         function Get_Vars_Wrapper (N : Node_Id) return Flow_Id_Sets.Set
         is (Get_Variables
             (N,
              Scope                        => Scope,
              Fold_Functions               => Fold_Functions,
              Use_Computed_Globals         => Use_Computed_Globals,
              Reduced                      => False,
              Expand_Synthesized_Constants => Expand_Synthesized_Constants));

         M             : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;

         Root_Node     : Node_Id := N;

         Component     : Entity_Vectors.Vector := Entity_Vectors.Empty_Vector;

         Seq           : Node_Lists.List := Node_Lists.Empty_List;

         E             : Entity_Id;
         Comp_Id       : Positive;
         Current_Field : Flow_Id;

         Must_Abort    : Boolean := False;

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
              Is_Record_Type (Get_Full_Type_Without_Checking (Root_Node)))
           or else
             Is_Ignored_Node (Root_Node)
         loop
            if Nkind (Root_Node) = N_Selected_Component then
               Component.Prepend
                 (Original_Record_Component
                    (Entity (Selector_Name (Root_Node))));
            end if;

            if not Is_Ignored_Node (Root_Node) then
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

         if Nkind (Root_Node) not in N_Identifier | N_Expanded_Name or else
           not Is_Record_Type (Get_Full_Type_Without_Checking (Root_Node))
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
                        Ptr : Node_Id :=
                          First (Component_Associations
                                   (First (Expressions (N))));

                     begin
                        while Present (Ptr) loop
                           Vars.Union (Get_Vars_Wrapper (Ptr));
                           Next (Ptr);
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

         --  Ok, so the root is an entire variable, we can untangle this
         --  further.

         pragma Assert (Nkind (Root_Node) in N_Identifier | N_Expanded_Name);
         pragma Assert (not Must_Abort);

         --  We set up an identity map of all fields of the original record.
         --  For example a record with two fields would produce this kind of
         --  map:
         --
         --     r.x -> r.x
         --     r.y -> r.y

         declare
            Root_Entity : constant Entity_Id := Entity (Root_Node);

            FS : constant Flow_Id_Sets.Set :=
              (if Is_Protected_Component (Root_Entity) then
                 Flatten_Variable
                   (Add_Component
                      (Direct_Mapping_Id (Sinfo.Scope (Root_Entity)),
                       Root_Entity),
                    Scope)

               elsif Is_Part_Of_Concurrent_Object (Root_Entity) then
                 Flatten_Variable
                   (Add_Component
                      (Direct_Mapping_Id
                         (Etype (Encapsulating_State (Root_Entity))),
                       Root_Entity),
                    Scope)

               else Flatten_Variable (Root_Entity, Scope));

         begin
            for F of FS loop
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
         --  For example, if we get an update 'update (y => z) then we change
         --  the map accordingly:
         --
         --     r.x -> r.x
         --     r.y -> z
         --
         --  = Access =
         --  Otherwise, we trim down the map. For example .y will throw away
         --  any entries in the map that are not related:
         --
         --     r.y -> z
         --
         --  Once we have processed all instructions, then the set of relevant
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

         Comp_Id       := 1;
         Current_Field := Direct_Mapping_Id (Entity (Root_Node));

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
                  Ptr       : Node_Id := First (Component_Associations
                                                (First (Expressions (N))));
                  Field_Ptr : Node_Id;
                  Tmp       : Flow_Id_Sets.Set;
                  FS        : Flow_Id_Sets.Set;
               begin
                  Indent;
                  while Present (Ptr) loop
                     Field_Ptr := First (Choices (Ptr));
                     while Present (Field_Ptr) loop
                        E := Original_Record_Component (Entity (Field_Ptr));

                        if Debug_Trace_Untangle_Fields then
                           Write_Str ("Updating component ");
                           Sprint_Node_Inline (E);
                           Write_Eol;
                        end if;

                        if Is_Record_Type (Get_Type (E, Scope)) then
                           --  Composite update

                           --  We should call Untangle_Record_Aggregate
                           --  here. For now we us a safe default (all
                           --  fields depend on everything).

                           case Nkind (Expression (Ptr)) is
                              --  when N_Aggregate =>
                              --     null;

                              when others =>
                                 Tmp := Get_Vars_Wrapper (Expression (Ptr));

                                 --  Not sure what to do, so set all sensible
                                 --  fields to the given variables.

                                 FS := Flatten_Variable
                                   (Add_Component (Current_Field, E), Scope);

                                 for F of FS loop
                                    M.Replace (F, Tmp);
                                    All_Vars.Union (Tmp);
                                 end loop;
                           end case;
                        else

                           --  Direct field update of M

                           Tmp := Get_Vars_Wrapper (Expression (Ptr));
                           M.Replace (Add_Component (Current_Field, E), Tmp);
                           All_Vars.Union (Tmp);
                        end if;

                        Next (Field_Ptr);
                     end loop;
                     Next (Ptr);
                  end loop;
                  Outdent;
               end;

            when N_Selected_Component =>

               declare
                  Comp_E : constant Entity_Id := Entity (Selector_Name (N));
                  Root_Entity : constant Entity_Id := Entity (Root_Node);

                  pragma Assert (Ekind (Comp_E) in E_Component
                                                 | E_Discriminant);

                  pragma Assert (Ekind (Root_Entity) in Object_Kind);

                  Discr_Constraints : constant Flow_Id_Sets.Set :=
                    (if Ekind (Comp_E) = E_Component
                     then Discriminant_Constraints (Comp_E)
                     else
                       (if Ekind (Root_Entity) in E_Constant
                                                | E_Variable
                                                | E_Component
                        then Discriminant_Constraints (Root_Entity)
                        else Flow_Id_Sets.Empty_Set));

               begin
                  --  We trim the result map

                  E := Original_Record_Component (Comp_E);

                  if Debug_Trace_Untangle_Fields then
                     Write_Str ("Trimming for: ");
                     Sprint_Node_Inline (E);
                     Write_Eol;
                  end if;

                  declare
                     New_Map : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;

                  begin
                     for C in M.Iterate loop
                        declare
                           K : Flow_Id          renames Flow_Id_Maps.Key (C);
                           V : Flow_Id_Sets.Set renames M (C);

                        begin
                           if K.Kind = Record_Field
                             and then Natural (K.Component.Length) >= Comp_Id
                             and then K.Component (Comp_Id) = E
                           then
                              New_Map.Insert (K, Discr_Constraints or V);
                           end if;
                        end;
                     end loop;

                     M := New_Map;
                  end;
               end;

               Current_Field := Add_Component (Current_Field, E);
               Comp_Id       := Comp_Id + 1;

            when others =>
               raise Why.Unexpected_Node;
            end case;

            if Debug_Trace_Untangle_Fields then
               Print_Flow_Map (M);
            end if;
         end loop;

         --  We merge what is left after trimming

         for S of M loop
            All_Vars.Union (S);
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

         if Fold_Functions then
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
               | N_Call_Marker
               | N_Entry_Body
               | N_Entry_Declaration
               | N_Freeze_Entity
               | N_Freeze_Generic_Entity
               | N_Later_Decl_Item
               | N_Renaming_Declaration
               | N_Representation_Clause
               | N_Variable_Reference_Marker
            =>
               pragma Assert (not Ctx.Assume_In_Expression);

               --  These should allow us to go through package specs and bodies
               return Skip;

            when N_Identifier | N_Expanded_Name =>
               if Present (Entity (N)) then
                  Variables.Union (Do_Entity (Entity (N)));
               end if;

            --  Within expression, a defining identifier only appears as a
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
                  pragma Assert (Is_Quantified_Loop_Param (N));
               end if;

            when N_Aggregate =>
               Variables.Union (Recurse (Aggregate_Bounds (N)));

            when N_Selected_Component =>
               if Is_Subprogram_Or_Entry (Entity (Selector_Name (N))) then

                  --  Here we are dealing with a call of a protected
                  --  entry/function. This appears on the tree as a selected
                  --  component of the protected object.

                  Variables.Union (Recurse (Prefix (N)));

               elsif Ctx.Reduced then
                  --  In reduced mode we just keep traversing the tree, but we
                  --  need to turn off consider_extensions.
                  Variables.Union (Recurse (Prefix (N)));

               else
                  Variables.Union (Untangle_With_Context (N));
               end if;
               return Skip;

            when N_Type_Conversion =>
               if Ctx.Reduced then
                  return OK;

               elsif Is_Record_Type (Get_Type (N, Ctx.Scope)) then
                  --  We use Untangle_Record_Assignment as this can deal with
                  --  view conversions.

                  declare
                     M : constant Flow_Id_Maps.Map :=
                       Untangle_Record_Assignment
                         (N,
                          Map_Root                     =>
                            Direct_Mapping_Id (Etype (N)),
                          Map_Type                     =>
                            Get_Type (N, Ctx.Scope),
                          Scope                        => Ctx.Scope,
                          Fold_Functions               => Ctx.Fold_Functions,
                          Use_Computed_Globals         =>
                            Ctx.Use_Computed_Globals,
                          Expand_Synthesized_Constants =>
                            Ctx.Expand_Synthesized_Constants);

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
               Variables.Union (Do_N_Attribute_Reference (N));
               return Skip;

            when N_In | N_Not_In =>
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

                     Globals : Global_Flow_Ids;
                  begin
                     if No (P) then
                        return;
                     end if;

                     --  Something to note here: we include the predicate
                     --  function in the set of called subprograms during GG,
                     --  but not in phase 2. The idea is that 'calling' the
                     --  subprogram will introduce the dependencies on its
                     --  global, wheras in phase 2 we directly include its
                     --  globals.

                     Get_Globals
                       (Subprogram          => P,
                        Scope               => Ctx.Scope,
                        Classwide           => False,
                        Globals             => Globals,
                        Use_Deduced_Globals => Ctx.Use_Computed_Globals);

                     pragma Assert (Globals.Outputs.Is_Empty);
                     --  No function folding to deal with for predicate
                     --  functions (they always consume their single input).

                     declare
                        Effects : constant Flow_Id_Sets.Set :=
                          Globals.Proof_Ins or Globals.Inputs;

                     begin
                        for F of Effects loop
                           Variables.Include (Change_Variant (F, Normal_Use));
                        end loop;
                     end;
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

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);

   --  Start of processing for Get_Variables_Internal

   begin
      Traverse (N);

      return S : Flow_Id_Sets.Set do

         --  We need to do some post-processing on the result here. First we
         --  check each variable to see if it is the result of an action. For
         --  flow analysis its more helpful to talk about the original
         --  variables, so we undo these actions whenever possible.

         for F of Variables loop
            case F.Kind is
               when Direct_Mapping | Record_Field =>
                  declare
                     N : constant Node_Id := Parent (F.Node);

                  begin
                     if Nkind (N) = N_Object_Declaration
                       and then Is_Action (N)
                     then
                        declare
                           Expr : constant Node_Id := Expression (N);

                        begin
                           case Nkind (Expr) is
                              when N_Identifier | N_Expanded_Name =>
                                 S.Include
                                   (F'Update
                                      (Node =>
                                         Unique_Entity (Entity (Expr))));

                              when others =>
                                 S.Union (Recurse (Expr));
                           end case;
                        end;
                     else
                        S.Include (F);
                     end if;
                  end;

               when others =>
                  S.Include (F);
            end case;
         end loop;

         --  And finally, we remove all local constants
         Remove_Constants (S);

         Map_Generic_In_Formals (Ctx.Scope, S);
      end return;
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
      Ctx : constant Get_Variables_Context :=
        (Scope                        => Get_Flow_Scope (Scope_N),
         Fold_Functions               => False,
         Use_Computed_Globals         => True,
         Reduced                      => True,
         Assume_In_Expression         => True,
         Expand_Synthesized_Constants => False,
         Consider_Extensions          => False);

   begin
      return
        Expand_Abstract_States
          (Get_Variables_Internal (Expr_N, Ctx));
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
         Fold_Functions       => True,
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

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
      use Component_Graphs;

      procedure Process (E : Entity_Id);
      --  Extract information about entity E into flow's internal data
      --  structure. Currently it deals with record components and
      --  discriminants.

      function Node_Info (G : Graph;
                          V : Vertex_Id)
                          return Node_Display_Info;

      function Edge_Info (G      : Graph;
                          A      : Vertex_Id;
                          B      : Vertex_Id;
                          Marked : Boolean;
                          Colour : Natural)
                          return Edge_Display_Info;
      ---------------
      -- Node_Info --
      ---------------

      function Node_Info (G : Graph;
                          V : Vertex_Id)
                          return Node_Display_Info
      is
      begin
         Temp_String := Null_Unbounded_String;
         Set_Special_Output (Add_To_Temp_String'Access);
         Print_Tree_Node (G.Get_Key (V));
         Cancel_Special_Output;

         return (Show        => True,
                 Shape       => Shape_Oval,
                 Colour      => To_Unbounded_String ("black"),
                 Fill_Colour => Null_Unbounded_String,
                 Label       => Temp_String);
      end Node_Info;

      ---------------
      -- Edge_Info --
      ---------------

      function Edge_Info (G      : Graph;
                          A      : Vertex_Id;
                          B      : Vertex_Id;
                          Marked : Boolean;
                          Colour : Natural)
                          return Edge_Display_Info
      is
         pragma Unreferenced (G, A, B, Marked, Colour);
      begin
         return (Show   => True,
                 Shape  => Edge_Normal,
                 Colour => To_Unbounded_String ("black"),
                 Label  => Null_Unbounded_String);
      end Edge_Info;

      -------------
      -- Process --
      -------------

      procedure Process (E : Entity_Id) is
         Comp : Entity_Id;
         --  Component or discriminant of entity E

      begin
         if Is_Record_Type (E)
           or else Is_Incomplete_Or_Private_Type (E)
           or else Is_Concurrent_Type (E)
         then
            Comp := First_Component_Or_Discriminant (E);

            while Present (Comp) loop
               --  We add a component to the graph if it is in SPARK
               if Component_Is_Visible_In_SPARK (Comp) then
                  Comp_Graph.Include_Vertex (Comp);

                  Comp_Graph.Include_Vertex (Original_Record_Component (Comp));

                  if Ekind (Comp) = E_Discriminant
                    and then Present (Corresponding_Discriminant (Comp))
                  then
                     Comp_Graph.Include_Vertex
                       (Corresponding_Discriminant (Comp));
                  end if;
               end if;

               Next_Component_Or_Discriminant (Comp);
            end loop;
         end if;
      end Process;

      --  Local variables

      S    : Node_Sets.Set;
      Ptr  : Entity_Id;
      Ptr2 : Entity_Id;

   --  Start of processing for Initialize

   begin
      Comp_Graph := Component_Graphs.Create;

      for E of Entities_To_Translate loop
         Process (E);

         if Ekind (E) = E_Package
           and then Entity_In_Ext_Axioms (E)
         then
            Process_External_Entities (E, Process'Access);
         end if;
      end loop;

      for V of Comp_Graph.Get_Collection (All_Vertices) loop
         Ptr := Comp_Graph.Get_Key (V);
         S.Insert (Ptr);

         Comp_Graph.Add_Edge (V_1 => Ptr,
                              V_2 => Original_Record_Component (Ptr));

         if Ekind (Ptr) = E_Discriminant
           and then Present (Corresponding_Discriminant (Ptr))
         then
            Comp_Graph.Add_Edge
              (V_1 => Ptr,
               V_2 => Corresponding_Discriminant (Ptr));
         end if;

         for V2 of Comp_Graph.Get_Collection (All_Vertices) loop
            exit when V = V2;
            Ptr2 := Comp_Graph.Get_Key (V2);
            if Sloc (Ptr) = Sloc (Ptr2) then
               Comp_Graph.Add_Edge (V_1 => V, V_2 => V2);
            end if;
         end loop;
      end loop;

      while not S.Is_Empty loop
         declare
            Work_List : Node_Sets.Set :=
              Node_Sets.To_Set (S.First_Element);
            --  Work list seeded with a random element

            C : Cluster_Id;

         begin
            --  Create a new component
            Comp_Graph.New_Cluster (C);

            --  Flood current component
            loop
               Ptr := Work_List.First_Element;

               S.Exclude (Ptr);

               Comp_Graph.Set_Cluster (Comp_Graph.Get_Vertex (Ptr), C);

               for Neighbour_Kind in Collection_Type_T range
                 Out_Neighbours .. In_Neighbours
               loop
                  for V of Comp_Graph.Get_Collection
                    (Comp_Graph.Get_Vertex (Ptr), Neighbour_Kind)
                  loop
                     Ptr2 := Comp_Graph.Get_Key (V);
                     if S.Contains (Ptr2) then
                        Work_List.Include (Ptr2);
                     end if;
                  end loop;
               end loop;

               Work_List.Delete (Ptr);

               exit when Work_List.Is_Empty;
            end loop;
         end;
      end loop;

      if Debug_Record_Component then
         Comp_Graph.Write_Pdf_File (Filename  => "component_graph",
                                    Node_Info => Node_Info'Access,
                                    Edge_Info => Edge_Info'Access);
      end if;

      Init_Done := True;
   end Initialize;

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

   ---------------------------
   -- Is_Precondition_Check --
   ---------------------------

   function Is_Precondition_Check (N : Node_Id) return Boolean is
      A : constant Node_Id := First (Pragma_Argument_Associations (N));
   begin
      pragma Assert (Nkind (Expression (A)) = N_Identifier);
      return Chars (Expression (A)) in Name_Pre | Name_Precondition;
   end Is_Precondition_Check;

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
               if Ekind (E) = E_Constant then
                  return Has_Variable_Input (E);
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
                  pragma Assert (Nkind (E) = N_Defining_Identifier);

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

   --------------------
   -- Same_Component --
   --------------------

   function Same_Component (C1, C2 : Entity_Id) return Boolean is
      use type Component_Graphs.Cluster_Id;

   begin
      return C1 = C2 or else
        Comp_Graph.Get_Cluster (Comp_Graph.Get_Vertex (C1)) =
          Comp_Graph.Get_Cluster (Comp_Graph.Get_Vertex (C2));
   end Same_Component;

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
     (N                            : Node_Id;
      Map_Root                     : Flow_Id;
      Map_Type                     : Entity_Id;
      Scope                        : Flow_Scope;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Expand_Synthesized_Constants : Boolean;
      Extensions_Irrelevant        : Boolean := True)
      return Flow_Id_Maps.Map
   is
      --  !!! Join/Merge need to be able to deal with private parts and
      --      extensions (i.e. non-normal facets).

      function Get_Vars_Wrapper (N : Node_Id) return Flow_Id_Sets.Set
      is (Get_Variables
            (N,
             Scope                        => Scope,
             Fold_Functions               => Fold_Functions,
             Use_Computed_Globals         => Use_Computed_Globals,
             Reduced                      => False,
             Expand_Synthesized_Constants => Expand_Synthesized_Constants))
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
             Map_Root                     => Map_Root,
             Map_Type                     => (if Present (Map_Type)
                                              then Map_Type
                                              else Get_Type (N, Scope)),
             Scope                        => Scope,
             Fold_Functions               => Fold_Functions,
             Use_Computed_Globals         => Use_Computed_Globals,
             Expand_Synthesized_Constants => Expand_Synthesized_Constants,
             Extensions_Irrelevant        => Ext_Irrelevant))
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
      with Pre => Ekind (Component) in E_Component | E_Discriminant
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

      function Discriminant_Constraints (Typ : Entity_Id)
                                         return Flow_Id_Sets.Set
      with Pre => Is_Type (Typ);
      --  Returns the discriminant constraints for Typ if it is a record or
      --  concurrent type with discriminants, returns the empty set otherwise.

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

      ------------------------------
      -- Discriminant_Constraints --
      ------------------------------

      function Discriminant_Constraints (Typ : Entity_Id)
                                         return Flow_Id_Sets.Set
      is
      begin
         if (Is_Record_Type (Typ)
             or else Is_Concurrent_Type (Typ))
           and then Is_Constrained (Typ)
           and then Has_Discriminants (Typ)
         then
            declare
               Discriminants : Flow_Id_Sets.Set;

            begin
               --  Loop over the list of discriminant constraints

               for Discr of Iter (Discriminant_Constraint (Typ)) loop
                  Discriminants.Union (Get_Vars_Wrapper (Discr));
               end loop;

               return Discriminants;
            end;
         else
            return Flow_Id_Sets.Empty_Set;
         end if;
      end Discriminant_Constraints;

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
               Done   : Component_Sets.Set;

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
                     Merge (M, Component => Entity (Target), Input => Input);
                     Done.Insert (Original_Record_Component (Entity (Target)));
                     Next (Target);
                  end loop;
                  Next (Component_Association);
               end loop;

               --  If the aggregate is more constrained than the type would
               --  suggest, we fill in the "missing" fields with null, so
               --  that they appear initialized.
               for Component of Components (Map_Type) loop
                  declare
                     ORC : constant Entity_Id :=
                       Original_Record_Component (Component);
                     FS  : Flow_Id_Sets.Set;

                  begin
                     if not Done.Contains (ORC) then
                        FS := Flatten_Variable (Add_Component (Map_Root, ORC),
                                                Scope);

                        for F of FS loop
                           M.Insert (F, Flow_Id_Sets.Empty_Set);
                        end loop;
                     end if;
                  end;
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

               Selector : constant Entity_Id := Entity (Selector_Name (N));

            begin
               for C in Tmp.Iterate loop
                  declare
                     Output : Flow_Id          renames Flow_Id_Maps.Key (C);
                     Inputs : Flow_Id_Sets.Set renames Tmp (C);

                  begin
                     if Same_Component (Output.Component.First_Element,
                                        Selector)
                     then
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
                 Ekind (E) = E_Constant
                 and then not Has_Variable_Input (E);
               --  If we are assigning a pure constant, we don't really want to
               --  see it (just like if we assign integer/string/... literals
               --  then we don't want to see them in flow). However, we can't
               --  just pretend that the RHS is an empty map; it is a map
               --  (i.e. a certain structure) with empty elements, e.g. the
               --  private extension part.

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
               --    Ekind (T_To) in Class_Wide_Kind;

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

               Discr_Constraints : constant Flow_Id_Sets.Set :=
                 Discriminant_Constraints (T_From);

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
                        M.Include (Output, Inputs or Discr_Constraints);
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

         when N_Function_Call
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
                                 Fold : Boolean)
                                 return Flow_Id_Sets.Set
      is (Get_Variables
            (N,
             Scope                => Scope,
             Fold_Functions       => Fold,
             Use_Computed_Globals => Use_Computed_Globals,
             Reduced              => False));

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

                     function In_Type (C : Entity_Id) return Boolean is
                       (for some Ptr of Components (New_Typ) =>
                          Same_Component (C, Ptr));

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
                                    if Ekind (New_Typ) in Class_Wide_Kind then
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
                  A, B : Flow_Id_Sets.Set;

               begin
                  while Present (Expr) loop
                     A := Get_Vars_Wrapper (Expr, Fold => False);
                     B := Get_Vars_Wrapper (Expr, Fold => True);
                     Vars_Used.Union (B);
                     Vars_Proof.Union (A - B);

                     Next (Expr);
                  end loop;
               end;
               Process_Type_Conversions := False;

            when N_Slice =>
               declare
                  A, B : Flow_Id_Sets.Set;

               begin
                  A := Get_Vars_Wrapper (Discrete_Range (N), Fold => False);
                  B := Get_Vars_Wrapper (Discrete_Range (N), Fold => True);
                  Vars_Used.Union (B);
                  Vars_Proof.Union (A - B);
               end;
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
        and then Ekind (Etype (N)) in Class_Wide_Kind
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

   ----------------------
   -- Replace_Flow_Ids --
   ----------------------

   function Replace_Flow_Ids
     (Of_This   : Entity_Id;
      With_This : Entity_Id;
      The_Set   : Flow_Id_Sets.Set)
      return Flow_Id_Sets.Set
   is
      FS : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for F of The_Set loop
         if F.Kind in Direct_Mapping | Record_Field
           and then Get_Direct_Mapping_Id (F) = Of_This
         then
            FS.Insert (F'Update (Node => With_This));
         else
            FS.Insert (F);
         end if;
      end loop;
      return FS;
   end Replace_Flow_Ids;

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

end Flow_Utility;
