------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2013-2017, Altran UK Limited                 --
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
with Namet;                           use Namet;
with Nlists;                          use Nlists;
with Output;                          use Output;
with Rtsfind;                         use Rtsfind;
with Sem_Aux;                         use Sem_Aux;
with Sem_Type;                        use Sem_Type;
with Sprint;                          use Sprint;
with Treepr;                          use Treepr;

with Common_Iterators;                use Common_Iterators;
with Gnat2Why_Args;
with Gnat2Why.Util;
with SPARK_Definition;                use SPARK_Definition;
with SPARK_Frame_Conditions;          use SPARK_Frame_Conditions;
with SPARK_Util;                      use SPARK_Util;
with SPARK_Util.Subprograms;          use SPARK_Util.Subprograms;
with SPARK_Util.Types;                use SPARK_Util.Types;
with Why;

with Flow_Classwide;                  use Flow_Classwide;
with Flow_Debug;                      use Flow_Debug;
with Flow_Generated_Globals.Phase_2;  use Flow_Generated_Globals.Phase_2;
with Graphs;

package body Flow_Utility is

   use type Flow_Id_Sets.Set;
   use type Node_Sets.Set;

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

   Loop_Info_Frozen : Boolean       := False;
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
   --  Return components of the given entity E, similar to
   --  {First,Next}_Component_Or_Discriminant, with the difference that any
   --  components of private ancestors are included.
   --  @param E a type entity
   --  @return all component and discriminants of the type or the empty list
   --    if none exists

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

   --------------
   -- Add_Loop --
   --------------

   procedure Add_Loop (E : Entity_Id) is
   begin
      pragma Assert (not Loop_Info_Frozen);
      Loop_Info.Insert (E, Flow_Id_Sets.Empty_Set);
   end Add_Loop;

   ---------------------
   -- Add_Loop_Writes --
   ---------------------

   procedure Add_Loop_Writes (Loop_E : Entity_Id;
                              Writes : Flow_Id_Sets.Set)
   is
   begin
      pragma Assert (not Loop_Info_Frozen);
      Loop_Info (Loop_E).Union (Writes);
   end Add_Loop_Writes;

   -------------------------
   -- Add_To_Temp_String  --
   -------------------------

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
                  Functions_Called.Include (Called_Func);

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
     (Component_Graphs.Cluster_Hash
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
            Ptr : Entity_Id;
            T   : Entity_Id          := E;
            L   : Node_Lists.List    := Node_Lists.Empty_List;
            S   : Component_Sets.Set := Component_Sets.Empty_Set;

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

         begin
            loop
               Ptr := First_Component_Or_Discriminant (T);
               while Present (Ptr) loop
                  declare
                     Inserted : Boolean;
                     Unused   : Component_Sets.Cursor;
                  begin
                     S.Insert (New_Item => Ptr,
                               Position => Unused,
                               Inserted => Inserted);
                     if Inserted then
                        L.Append (Ptr);
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

   ---------------------------
   -- Expand_Abstract_State --
   ---------------------------

   function Expand_Abstract_State
     (F               : Flow_Id;
      Erase_Constants : Boolean)
      return Flow_Id_Sets.Set
   is
   begin
      case F.Kind is
         when Direct_Mapping =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               --  Expand abstract states as much as possible while respecting
               --  the SPARK_Mode barrier.
               if Ekind (E) = E_Abstract_State then
                  declare
                     Pkg : constant Entity_Id := Scope (E);
                     --  Package
                     pragma Assert (Ekind (Pkg) = E_Package);

                     Result : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

                  begin
                     --  If the state is null, this is known right at its
                     --  declaration and is not affected by the SPARK_Mode.

                     if Is_Null_State (E) then
                        return Flow_Id_Sets.Empty_Set;
                     else
                        --  Use the Refined_State aspect, if visible
                        if Entity_Body_In_SPARK (Pkg) then

                           --  At this point we know whether the state has a
                           --  null refinement; if it does, then we ignore it.
                           if Has_Null_Refinement (E) then
                              return Flow_Id_Sets.Empty_Set;
                           else
                              for C of Iter (Refinement_Constituents (E)) loop
                                 Result.Union
                                   (Expand_Abstract_State
                                      (Direct_Mapping_Id (C, F.Variant),
                                       Erase_Constants));
                              end loop;

                              return Result;
                           end if;

                        --  Pick the Part_Of constituents from the private part
                        --  of the package, if visible.

                        elsif Present
                          (Private_Declarations (Package_Specification (Pkg)))
                          and then Private_Spec_In_SPARK (Pkg)
                        then
                           for C of Iter (Part_Of_Constituents (E)) loop
                              Result.Union
                                (Expand_Abstract_State
                                   (Direct_Mapping_Id (C, F.Variant),
                                    Erase_Constants));
                           end loop;

                           --  There might be more constituents in the package
                           --  body, but we can't see them. The state itself
                           --  will represent them.

                           Result.Insert (F);

                           return Result;

                        --  None of the constituents are visible. The state
                        --  will behave as a blob of data.

                        else
                           return Flow_Id_Sets.To_Set (F);
                        end if;
                     end if;
                  end;

               --  Entities translated as constants in Why3 should not be
               --  considered as effects for proof. This includes in particular
               --  formal parameters of mode IN.

               elsif Erase_Constants
                 and then not Gnat2Why.Util.Is_Mutable_In_Why (E)
               then
                  return Flow_Id_Sets.Empty_Set;

               --  Otherwise the effect is significant for proof, keep it

               else
                  return Flow_Id_Sets.To_Set (F);
               end if;
            end;

         when Magic_String =>
            return Flow_Id_Sets.To_Set (F);

         when Record_Field | Null_Value | Synthetic_Null_Export =>
            raise Program_Error;
      end case;
   end Expand_Abstract_State;

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
      return Ekind (E) in Formal_Kind
        and then Is_Tagged_Type (T)
        and then Ekind (T) not in Class_Wide_Kind
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
            --  Record fields themselves cannot be classwide.
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

               function Get_Root_Component (N : Node_Id) return Node_Id;
               --  Returns N's equilavent component of the root type. If this
               --  is not available then N's Original_Record_Component is
               --  returned instead.
               --
               --  @param N is the component who's equivalent we are looking
               --    for
               --  @return the equivalent component of the root type if one
               --    exists or the Original_Record_Component of N otherwise.

               ------------------------
               -- Get_Root_Component --
               ------------------------

               function Get_Root_Component (N : Node_Id) return Node_Id is
                  ORC : constant Node_Id := Original_Record_Component (N);
               begin
                  --  If Same_Component is True for one of the Root_Components
                  --  then return that instead.
                  for Comp of Root_Components loop
                     if Same_Component (ORC, Comp) then
                        return Comp;
                     end if;
                  end loop;

                  --  No Same_Component found. Fall back to N's
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
               Classwide := Ekind (T) in Class_Wide_Kind;
               while Ekind (T) in Class_Wide_Kind loop
                  T := Get_Type (Etype (T), Scope);
               end loop;

               pragma Assert (Is_Type (T));

               if Debug_Trace_Flatten then
                  Write_Str ("Branching on type: ");
                  Sprint_Node_Inline (T);
                  Write_Line (" (" & Ekind (T)'Img & ")");
               end if;

               --  If we are dealing with a derived type then we want to get to
               --  the root and then populate the Root_Components set. However,
               --  we don't want to consider Itypes.
               if Is_Derived_Type (T) then
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
                        for Ptr of Components (T) loop
                           if Is_Visible (Get_Root_Component (Ptr), Scope) then
                              Results.Include (Add_Component (F, Ptr));
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
                                (Flatten_Variable (Direct_Mapping_Id (C),
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
                                   (Flatten_Variable (Direct_Mapping_Id (C),
                                    Scope));
                              end loop;
                           end if;
                        end;
                     end if;

                     --  Concurrent type represents the "current instance", as
                     --  defined in SPARK RM 6.1.4.
                     Results.Include (F);

                  when Record_Kind =>
                     Debug ("processing record type");

                     --  Include classwide types and privates with
                     --  discriminants.
                     if Components (T).Is_Empty then
                        --  If the record has an empty component list then we
                        --  add the variable itself...
                        Results.Insert (F);
                     else
                        --  ...else we add each visible component
                        for Ptr of Components (T) loop
                           if Is_Visible (Get_Root_Component (Ptr), Scope) then
                              --  Here we union disjoint sets, so possibly we
                              --  could optimize this.
                              Results.Union (Flatten_Variable
                                             ((if Is_Concurrent_Type (T)
                                                then Direct_Mapping_Id (Ptr)
                                                else Add_Component (F, Ptr)),
                                                Scope));
                           else
                              Contains_Non_Visible := True;
                           end if;
                        end loop;
                     end if;

                     if Ekind (T) in Private_Kind then
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

                  when Array_Kind  |
                       Scalar_Kind =>
                     Debug ("processing scalar or array type");

                     Results := Flow_Id_Sets.To_Set (F);

                  when Access_Kind =>
                     --  ??? Pointers come only from globals (hopefully). They
                     --  should be removed when generating globals and here
                     --  we should only get the __HEAP entity name should.
                     Debug ("processing access type");

                     Results := Flow_Id_Sets.To_Set (F);

                  when E_Exception_Type  |
                       E_Subprogram_Type |
                       Incomplete_Kind   =>

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
      Classwide          : out Boolean;
      Map_Root           : out Flow_Id;
      Seq                : out Node_Lists.List)
   is
      subtype Interesting_Nodes is Valid_Assignment_Kinds
        with Static_Predicate => Interesting_Nodes not in
          N_Identifier | N_Expanded_Name;

      Root_Node : Node_Id := N;

   begin
      --  First we turn the tree into a more useful sequence. We also determine
      --  the root node which should be an entire variable.

      Seq := Node_Lists.Empty_List;

      while Nkind (Root_Node) in Interesting_Nodes loop
         Seq.Prepend (Root_Node);

         Root_Node :=
           (case Nkind (Root_Node) is
               when N_Type_Conversion | N_Unchecked_Type_Conversion =>
                  Expression (Root_Node),

               when others =>
                  Prefix (Root_Node));

      end loop;
      pragma Assert (Nkind (Root_Node) in N_Identifier | N_Expanded_Name);

      Partial_Definition := False;
      View_Conversion    := False;
      Classwide          := False;
      Map_Root           := Direct_Mapping_Id (Unique_Entity
                                                 (Entity (Root_Node)));

      --  We now work out which variable (or group of variables) is actually
      --  defined, by following the selected components. If we find an array
      --  slice or index we stop and note that we are dealing with a partial
      --  assignment (the defined variable is implicitly used).

      for N of Seq loop
         case Valid_Assignment_Kinds (Nkind (N)) is
            when N_Selected_Component =>
               Map_Root := Add_Component (Map_Root,
                                          Original_Record_Component
                                            (Entity (Selector_Name (N))));
               Classwide := False;

            when N_Type_Conversion =>
               View_Conversion := True;
               if Ekind (Etype (N)) in Class_Wide_Kind then
                  Classwide := True;
               end if;

            when N_Unchecked_Type_Conversion =>
               null;

            when others =>
               Partial_Definition := True;
               Classwide          := False;
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
         and then Get_Pragma_Id (Depends_N) in Pragma_Depends |
                                               Pragma_Refined_Depends);

      Contract_Relation : constant Dependency_Maps.Map :=
        Parse_Depends (Depends_N);
      --  Step 1: Parse the appropriate dependency relation

      All_Proof_Ins : Flow_Id_Sets.Set;
      All_Reads     : Flow_Id_Sets.Set;
      All_Writes    : Flow_Id_Sets.Set;

      function Trimming_Required return Boolean;
      --  Checks if the projected Depends constituents need to be trimmed
      --  (based on a user-provided Refined_Global aspect).
      --  ??? what is trimming?

      -----------------------
      -- Trimming_Required --
      -----------------------

      function Trimming_Required return Boolean is
        (Get_Pragma_Id (Depends_N) = Pragma_Depends
           and then Mentions_State_With_Visible_Refinement (Depends_N, Scope));

   --  Start of processing for Get_Depends

   begin
      ----------------------------------------------------------------------
      --  Step 2: Expand out any abstract state for which the refinement is
      --  visible, similar to what we do for globals. During this step we
      --  also trim the generated refined depends according to the
      --  user-provided Refined_Global contract.
      ----------------------------------------------------------------------

      --  Initialize Depends map
      Depends := Dependency_Maps.Empty_Map;

      if Trimming_Required then
         --  Use the Refined_Global to trim the down-projected Depends

         --  Collect all global Proof_Ins, Outputs and Inputs
         Get_Globals (Subprogram          => Subprogram,
                      Scope               => Scope,
                      Classwide           => False,
                      Proof_Ins           => All_Proof_Ins,
                      Reads               => All_Reads,
                      Writes              => All_Writes,
                      Use_Deduced_Globals => Use_Computed_Globals);

         --  Remove generic formals without variable input
         Remove_Constants (All_Proof_Ins, Only_Generic_Formals => True);
         Remove_Constants (All_Reads,     Only_Generic_Formals => True);
         Remove_Constants (All_Writes,    Only_Generic_Formals => True);

         --  Change all variants to Normal_Use
         All_Proof_Ins := Change_Variant (All_Proof_Ins, Normal_Use);
         All_Reads     := Change_Variant (All_Reads,     Normal_Use);
         All_Writes    := Change_Variant (All_Writes,    Normal_Use);

         --  Add formal parameters
         for Param of Get_Formals (Subprogram) loop
            declare
               Formal_Param : constant Flow_Id := Direct_Mapping_Id (Param);
            begin
               case Ekind (Param) is
                  when E_In_Parameter     =>
                     All_Reads.Insert (Formal_Param);
                     All_Proof_Ins.Insert (Formal_Param);

                  when E_In_Out_Parameter =>
                     All_Proof_Ins.Insert (Formal_Param);
                     All_Reads.Insert (Formal_Param);
                     All_Writes.Insert (Formal_Param);

                  when E_Out_Parameter    =>
                     All_Writes.Insert (Formal_Param);

                  when others             =>
                     All_Reads.Insert (Formal_Param);
                     All_Proof_Ins.Insert (Formal_Param);
                     if Ekind (Subprogram) /= E_Function then
                        All_Writes.Insert (Formal_Param);
                     end if;
               end case;
            end;
         end loop;

         --  If Subprogram is a function then we need to add it to the
         --  All_Writes set so that Subprogram'Result can appear on the LHS of
         --  the Refined_Depends.
         if Ekind (Subprogram) = E_Function then
            All_Writes.Insert (Direct_Mapping_Id (Subprogram));
         end if;

         for C in Contract_Relation.Iterate loop
            declare
               D_Out : constant Flow_Id_Sets.Set :=
                 (if Present (Dependency_Maps.Key (C)) then
                     To_Flow_Id_Set (Down_Project
                                       (Get_Direct_Mapping_Id
                                          (Dependency_Maps.Key (C)),
                                        Scope))
                  else
                     Flow_Id_Sets.To_Set (Dependency_Maps.Key (C)));

               D_In  : Flow_Id_Sets.Set :=
                 To_Flow_Id_Set
                   (Down_Project (To_Node_Set (Contract_Relation (C)), Scope));

            begin
               for O of D_Out loop
                  if All_Writes.Contains (O) then
                     D_In.Intersection (if O = Null_Flow_Id
                                        then All_Proof_Ins
                                        else All_Reads);
                     Depends.Insert (O, D_In);
                  end if;
               end loop;
            end;
         end loop;

      else
         --  Simply add the dependencies as they are
         for C in Contract_Relation.Iterate loop
            declare
               D_Out : constant Flow_Id_Sets.Set :=
                 (if Present (Dependency_Maps.Key (C)) then
                     To_Flow_Id_Set
                        (Down_Project
                           (Get_Direct_Mapping_Id (Dependency_Maps.Key (C)),
                            Scope))
                  else
                     Flow_Id_Sets.To_Set (Dependency_Maps.Key (C)));

               D_In  : constant Flow_Id_Sets.Set :=
                 To_Flow_Id_Set
                   (Down_Project (To_Node_Set (Contract_Relation (C)), Scope));

            begin
               for O of D_Out loop
                  Depends.Insert (O, D_In);
               end loop;
            end;
         end loop;
      end if;

      ----------------------------------------------------------------------
      --  Step 3: We add all Proof_Ins of the [Refined_]Global contract to
      --  the RHS of the "null => RHS" dependence. This is an implicit
      --  dependency.
      ----------------------------------------------------------------------

      Get_Globals (Subprogram          => Subprogram,
                   Scope               => Scope,
                   Classwide           => False,
                   Proof_Ins           => All_Proof_Ins,
                   Reads               => All_Reads,
                   Writes              => All_Writes,
                   Use_Deduced_Globals => Use_Computed_Globals,
                   Ignore_Depends      => True);

      --  Change variant of All_Proof_Ins to Normal_Use
      if not All_Proof_Ins.Is_Empty then
         All_Proof_Ins := Change_Variant (All_Proof_Ins, Normal_Use);

         --  Create new dependency with "null => All_Proof_Ins" or extend the
         --  existing "null => ..." with All_Proof_Ins.
         declare
            Position : Dependency_Maps.Cursor;
            Inserted : Boolean;

         begin
            Depends.Insert (Key      => Null_Flow_Id,
                            New_Item => All_Proof_Ins,
                            Position => Position,
                            Inserted => Inserted);

            if not Inserted then
               Depends (Position).Union (All_Proof_Ins);
            end if;
         end;
      end if;

      ----------------------------------------------------------------------
      --  Step 4: If we are dealing with a protected operation and the
      --  Callsite is present then we need to substitute references to the
      --  protected type with references to the protected object.
      ----------------------------------------------------------------------

      if Present (Callsite)
        and then Ekind (Sinfo.Scope (Subprogram)) = E_Protected_Type
      then
         declare
            The_PO : constant Entity_Id :=
              Get_Enclosing_Object (Prefix (Name (Callsite)));

            PO_Type : constant Entity_Id := Etype (The_PO);

            pragma Assert (Ekind (The_PO) = E_Variable and then
                           Ekind (PO_Type) = E_Protected_Type);

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
            for D in Depends.Iterate loop
               declare
                  C : constant Flow_Id_Sets.Cursor :=
                    Depends (D).Find (Direct_Mapping_Id (PO_Type));

               begin
                  if Flow_Id_Sets.Has_Element (C) then
                     Depends (D).Replace_Element
                       (Position => C,
                        New_Item => Direct_Mapping_Id (The_PO));
                  end if;
               end;
            end loop;
         end;
      end if;

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
         return Direct_Mapping_Id (Unique_Entity (E), View);
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

   -----------------
   -- Get_Globals --
   -----------------

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Scope                  : Flow_Scope;
                          Classwide              : Boolean;
                          Proof_Ins              : out Flow_Id_Sets.Set;
                          Reads                  : out Flow_Id_Sets.Set;
                          Writes                 : out Flow_Id_Sets.Set;
                          Consider_Discriminants : Boolean := False;
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
      Proof_Ins := Flow_Id_Sets.Empty_Set;
      Reads     := Flow_Id_Sets.Empty_Set;
      Writes    := Flow_Id_Sets.Empty_Set;

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
            pragma Assert
              (List_Length (Pragma_Argument_Associations (Global_Node)) = 1);

            PAA      : constant Node_Id :=
              First (Pragma_Argument_Associations (Global_Node));
            pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

            Row      : Node_Id;
            The_Mode : Name_Id;
            RHS      : Node_Id;

            G_Proof  : Node_Sets.Set := Node_Sets.Empty_Set;
            G_In     : Node_Sets.Set := Node_Sets.Empty_Set;
            G_Out    : Node_Sets.Set := Node_Sets.Empty_Set;

            procedure Process (The_Mode   : Name_Id;
                               The_Global : Entity_Id)
            with Pre => The_Mode in Name_Input
                                  | Name_In_Out
                                  | Name_Output
                                  | Name_Proof_In;
            --  Add the given global to Reads, Writes or Proof_Ins, depending
            --  on the mode.

            -------------
            -- Process --
            -------------

            procedure Process (The_Mode   : Name_Id;
                               The_Global : Entity_Id)
            is
               E : constant Entity_Id :=
                 Canonical_Entity (The_Global, Subprogram);

            begin
               case The_Mode is
                  when Name_Input =>
                     G_In.Insert (E);

                  when Name_In_Out =>
                     G_In.Insert (E);
                     G_Out.Insert (E);

                  when Name_Output =>
                     if Consider_Discriminants and then
                       Contains_Discriminants
                         (Direct_Mapping_Id (E, In_View),
                          Scope)
                     then
                        G_In.Insert (E);
                     end if;
                     G_Out.Insert (E);

                  when Name_Proof_In =>
                     G_Proof.Insert (E);

                  when others =>
                     raise Program_Error;

               end case;
            end Process;

         begin
            ---------------------------------------------------------------
            --  Step 1: Process global annotation, filling in g_proof,
            --  g_in, and g_out.
            ---------------------------------------------------------------

            if Nkind (Expression (PAA)) = N_Null then
               --  global => null
               --  No globals, nothing to do.
               return;

            elsif Nkind (Expression (PAA)) in N_Identifier | N_Expanded_Name
            then
               --  global => foo
               --  A single input
               Process (Name_Input, Entity (Expression (PAA)));

            elsif Nkind (Expression (PAA)) = N_Aggregate
              and then Expressions (Expression (PAA)) /= No_List
            then
               --  global => (foo, bar)
               --  Inputs
               RHS := First (Expressions (Expression (PAA)));
               while Present (RHS) loop
                  case Nkind (RHS) is
                     when N_Identifier | N_Expanded_Name =>
                        Process (Name_Input, Entity (RHS));

                     when N_Numeric_Or_String_Literal =>
                        Process (Name_Input, Original_Constant (RHS));

                     when others =>
                        raise Why.Unexpected_Node;

                  end case;
                  RHS := Next (RHS);
               end loop;

            elsif Nkind (Expression (PAA)) = N_Aggregate
              and then Component_Associations (Expression (PAA)) /= No_List
            then
               --  global => (mode => foo,
               --             mode => (bar, baz))
               --  A mixture of things.

               declare
                  CA : constant List_Id :=
                    Component_Associations (Expression (PAA));
               begin
                  Row := First (CA);
                  while Present (Row) loop
                     pragma Assert (List_Length (Choices (Row)) = 1);
                     The_Mode := Chars (First (Choices (Row)));

                     RHS := Expression (Row);
                     case Nkind (RHS) is
                        when N_Aggregate =>
                           RHS := First (Expressions (RHS));
                           while Present (RHS) loop
                              case Nkind (RHS) is
                                 when N_Numeric_Or_String_Literal =>
                                    Process (The_Mode,
                                             Original_Constant (RHS));

                                 when others =>
                                    Process (The_Mode, Entity (RHS));

                              end case;
                              RHS := Next (RHS);
                           end loop;

                        when N_Identifier | N_Expanded_Name =>
                           Process (The_Mode, Entity (RHS));

                        when N_Null =>
                           null;

                        when N_Numeric_Or_String_Literal =>
                           Process (The_Mode, Original_Constant (RHS));

                        when others =>
                           Print_Node_Subtree (RHS);
                           raise Why.Unexpected_Node;

                     end case;

                     Row := Next (Row);
                  end loop;
               end;

            else
               raise Why.Unexpected_Node;
            end if;

            ---------------------------------------------------------------
            --  Step 2: Expand any abstract state that might be too refined
            --  for our given scope.
            ---------------------------------------------------------------

            G_Proof := Down_Project (G_Proof, Scope);
            G_In    := Down_Project (G_In,    Scope);
            G_Out   := Down_Project (G_Out,   Scope);

            ---------------------------------------------------------------
            --  Step 3: Sanity check that none of the proof ins are
            --  mentioned as ins.
            ---------------------------------------------------------------

            --  pragma Assert ((G_Proof and G_In) = Node_Sets.Empty_Set);

            ---------------------------------------------------------------
            --  Step 4: Trim constituents based on the Refined_Depends.
            --  Only the Inputs are trimmed. Proof_Ins cannot be trimmed
            --  since they do not appear in Refined_Depends and Outputs
            --  cannot be trimmed since all constituents have to be
            --  present in the Refined_Depends.
            ---------------------------------------------------------------

            --  Check if the projected Global constituents need to be
            --  trimmed (based on a user-provided Refined_Depends aspect).
            if not Ignore_Depends
              and then Present (Depends_Node)
              and then Pragma_Name (Global_Node) /= Name_Refined_Global
              and then Pragma_Name (Depends_Node) = Name_Refined_Depends
              and then Mentions_State_With_Visible_Refinement
                         (Global_Node, Scope)
            then
               declare
                  D_Map        : Dependency_Maps.Map;
                  All_Inputs_F : Flow_Id_Sets.Set;
                  All_Inputs_N : Node_Sets.Set;

               begin
                  --  Read the Refined_Depends aspect
                  Get_Depends (Subprogram           => Subprogram,
                               Scope                => Scope,
                               Classwide            => Classwide,
                               Depends              => D_Map,
                               Use_Computed_Globals => Use_Deduced_Globals);

                  --  Gather all inputs
                  for Inputs of D_Map loop
                     All_Inputs_F.Union (Inputs);
                  end loop;

                  --  Convert set of Flow_Ids to a set of Node_Ids
                  for F of All_Inputs_F loop
                     All_Inputs_N.Insert (Get_Direct_Mapping_Id (F));
                  end loop;

                  --  Do the trimming
                  G_In.Intersection (All_Inputs_N);
               end;
            end if;

            ---------------------------------------------------------------
            --  Step 5: Convert to Flow_Id sets
            ---------------------------------------------------------------

            Proof_Ins := To_Flow_Id_Set (G_Proof, In_View);
            Reads     := To_Flow_Id_Set (G_In,    In_View);
            Writes    := To_Flow_Id_Set (G_Out,   Out_View);

            ---------------------------------------------------------------
            --  Step 6: Remove generic formals without variable input
            ---------------------------------------------------------------

            Remove_Constants (Proof_Ins, Only_Generic_Formals => True);
            Remove_Constants (Reads,     Only_Generic_Formals => True);
            Remove_Constants (Writes,    Only_Generic_Formals => True);
         end;

         Debug ("proof ins", Proof_Ins);
         Debug ("reads",     Reads);
         Debug ("writes",    Writes);

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
                           Writes.Include (Change_Variant (Output, Out_View));
                        end if;
                     end;
                  end if;

                  for Input of Inputs loop
                     if Present (Input) then
                        declare
                           E : constant Entity_Id :=
                             Get_Direct_Mapping_Id (Input);
                        begin
                           if not Params.Contains (E) then
                              Reads.Include (Change_Variant (Input, In_View));

                              --  A volatile with effective reads is always
                              --  an output as well (this should be recorded
                              --  in the depends, but the front-end does not
                              --  enforce this).
                              if Has_Effective_Reads (Input) then
                                 Writes.Include
                                   (Change_Variant (Input, Out_View));
                              end if;
                           end if;
                        end;
                     end if;
                  end loop;
               end;
            end loop;

            Debug ("reads", Reads);
            Debug ("writes", Writes);
         end;

      elsif Gnat2Why_Args.Flow_Generate_Contracts
        and then Use_Deduced_Globals
      then

         --  We don't have a global or a depends aspect so we look at the
         --  generated globals.

         Debug ("using generated globals");

         GG_Get_Globals (Subprogram, Scope, Proof_Ins, Reads, Writes);

      --  We don't have user globals and we're not allowed to use computed
      --  globals (i.e. we're trying to compute globals).

      else
         Debug ("defaulting to null globals");

      end if;
   end Get_Globals;

   ---------------------
   -- Get_Loop_Writes --
   ---------------------

   function Get_Loop_Writes (E : Entity_Id) return Flow_Id_Sets.Set is
   begin
      return Loop_Info (E);
   end Get_Loop_Writes;

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
                     Ptr : Node_Id;
                  begin
                     Ptr := First (Component_Associations
                                     (P_CC.First_Element));
                     while Present (Ptr) loop
                        P_Expr.Append (Expression (Ptr));
                        Next (Ptr);
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
      Contract_Case            : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Contract_Cases);
   begin
      if Is_Dispatching_Operation (E) then
         for Pre of Classwide_Pre_Post (E, Pragma_Precondition) loop
            Precondition_Expressions.Append (Pre);
         end loop;
      end if;

      --  If a Contract_Cases aspect was found then we pull out every
      --  condition apart from the others.
      if not Contract_Case.Is_Empty then
         declare
            C_Case    : Node_Id;
            Condition : Node_Id;
         begin
            C_Case := First (Component_Associations
                               (Contract_Case.First_Element));
            while Present (C_Case) loop
               Condition := First (Choices (C_Case));
               if Nkind (Condition) /= N_Others_Choice then
                  Precondition_Expressions.Append (Condition);
               end if;

               C_Case := Next (C_Case);
            end loop;
         end;
      end if;

      return Precondition_Expressions;

   end Get_Precondition_Expressions;

   -----------------------
   -- Get_Proof_Globals --
   -----------------------

   procedure Get_Proof_Globals (Subprogram          : Entity_Id;
                                Classwide           : Boolean;
                                Reads               : out Flow_Id_Sets.Set;
                                Writes              : out Flow_Id_Sets.Set;
                                Use_Deduced_Globals : Boolean := True;
                                Keep_Constants      : Boolean := False)
   is
      Unexpanded_Proof_Ins : Flow_Id_Sets.Set;
      Unexpanded_Reads     : Flow_Id_Sets.Set;
      Unexpanded_Writes    : Flow_Id_Sets.Set;

      S : constant Flow_Scope :=
        Get_Flow_Scope (if Is_In_Analyzed_Files (Subprogram)
                          and then Entity_Body_In_SPARK (Subprogram)
                        then Get_Body_Entity (Subprogram)
                        else Subprogram);

      procedure Expand (Unexpanded :        Flow_Id_Sets.Set;
                        Expanded   : in out Flow_Id_Sets.Set);
      --  Expand abstract states

      ------------
      -- Expand --
      ------------
      procedure Expand (Unexpanded :        Flow_Id_Sets.Set;
                        Expanded   : in out Flow_Id_Sets.Set)
      is
      begin
         for U of Unexpanded loop
            Expanded.Union (Expand_Abstract_State (U, not Keep_Constants));
         end loop;
      end Expand;

   --  Start of processing for Get_Proof_Globals

   begin
      Get_Globals
        (Subprogram             => Subprogram,
         Scope                  => S,
         Classwide              => Classwide,
         Proof_Ins              => Unexpanded_Proof_Ins,
         Reads                  => Unexpanded_Reads,
         Writes                 => Unexpanded_Writes,
         Consider_Discriminants => False,
         Use_Deduced_Globals    => Use_Deduced_Globals);

      --  Reset outputs
      Writes := Flow_Id_Sets.Empty_Set;
      Reads  := Flow_Id_Sets.Empty_Set;

      --  Expand all variables; it is more efficent to process Proof_Ins and
      --  Reads separaterly, because they are disjoint and there is no point
      --  in computing their union.
      Expand (Unexpanded_Proof_Ins, Reads);
      Expand (Unexpanded_Reads,     Reads);
      Expand (Unexpanded_Writes,    Writes);
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
         declare
            Fuller_View : Entity_Id;
         begin
            loop
               pragma Loop_Invariant (Is_Type (T));

               Fuller_View := Full_View (T);

               if Present (Fuller_View)
                 and then Is_Visible (Fuller_View, Scope)
                 and then Fuller_View /= T
               then
                  T := Fuller_View;
               else
                  exit;
               end if;
            end loop;
         end;

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
      Scope                           : Flow_Scope;
      Local_Constants                 : Node_Sets.Set;
      Fold_Functions                  : Boolean;
      Use_Computed_Globals            : Boolean;
      Reduced                         : Boolean;
      Assume_In_Expression            : Boolean;
      Expand_Synthesized_Constants    : Boolean;
      Consider_Extensions             : Boolean;
      Quantified_Variables_Introduced : Node_Sets.Set;
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
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Assume_In_Expression         : Boolean := True;
      Expand_Synthesized_Constants : Boolean := False;
      Consider_Extensions          : Boolean := False)
      return Flow_Id_Sets.Set
   is
      Ctx : constant Get_Variables_Context :=
        (Scope                           => Scope,
         Local_Constants                 => Local_Constants,
         Fold_Functions                  => Fold_Functions,
         Use_Computed_Globals            => Use_Computed_Globals,
         Reduced                         => Reduced,
         Assume_In_Expression            => Assume_In_Expression,
         Expand_Synthesized_Constants    => Expand_Synthesized_Constants,
         Consider_Extensions             => Consider_Extensions,
         Quantified_Variables_Introduced => Node_Sets.Empty_Set);
   begin
      return Get_Variables_Internal (N, Ctx);
   end Get_Variables;

   function Get_Variables
     (L                            : List_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Assume_In_Expression         : Boolean := True;
      Expand_Synthesized_Constants : Boolean := False)
      return Flow_Id_Sets.Set
   is
      Ctx : constant Get_Variables_Context :=
        (Scope                           => Scope,
         Local_Constants                 => Local_Constants,
         Fold_Functions                  => Fold_Functions,
         Use_Computed_Globals            => Use_Computed_Globals,
         Reduced                         => Reduced,
         Assume_In_Expression            => Assume_In_Expression,
         Expand_Synthesized_Constants    => Expand_Synthesized_Constants,
         Consider_Extensions             => False,
         Quantified_Variables_Introduced => Node_Sets.Empty_Set);
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

      function Do_Subprogram_Call (Callsite : Node_Id)
                                   return Flow_Id_Sets.Set
      with Pre => Nkind (Callsite) in N_Entry_Call_Statement |
                                      N_Subprogram_Call;
      --  Work out which variables (including globals) are used in the
      --  entry/subprogram call and add them to the given set. Do not follow
      --  children after calling this.

      function Do_Entity (E : Entity_Id)
                          return Flow_Id_Sets.Set
      with Pre => Nkind (E) in N_Entity;
      --  Process the given entity and return the variables associated with it

      function Do_N_Attribute_Reference (N : Node_Id)
                                         return Flow_Id_Sets.Set
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

      function Filter (Variables : Flow_Id_Sets.Set) return Flow_Id_Sets.Set;
      --  Some functions called by Get_Variables do not know about the context
      --  we've built up, so we may need to strip some variables from their
      --  returned set. In particular, we remove quantified variables.

      function Recurse (N                        : Node_Id;
                        Consider_Extensions      : Boolean   := False;
                        With_Quantified_Variable : Entity_Id := Empty)
                        return Flow_Id_Sets.Set
      with Pre => (if Present (With_Quantified_Variable)
                   then Nkind (With_Quantified_Variable) in N_Entity);
      --  Helper function to recurse on N

      function Untangle_With_Context (N : Node_Id)
                                      return Flow_Id_Sets.Set
      is (Filter (Untangle_Record_Fields
           (N,
            Scope                        => Ctx.Scope,
            Local_Constants              => Ctx.Local_Constants,
            Fold_Functions               => Ctx.Fold_Functions,
            Use_Computed_Globals         => Ctx.Use_Computed_Globals,
            Expand_Synthesized_Constants =>
              Ctx.Expand_Synthesized_Constants)));
      --  Helper function to call Untangle_Record_Fields with the appropriate
      --  context, but also filtering out quantified variables.

      -------------
      -- Recurse --
      -------------

      function Recurse (N                        : Node_Id;
                        Consider_Extensions      : Boolean   := False;
                        With_Quantified_Variable : Entity_Id := Empty)
                        return Flow_Id_Sets.Set
      is
         New_Ctx : Get_Variables_Context := Ctx;
      begin
         New_Ctx.Consider_Extensions := Consider_Extensions;
         if Present (With_Quantified_Variable) then
            New_Ctx.Quantified_Variables_Introduced.Insert
              (With_Quantified_Variable);
         end if;
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
            return Flow_Id_Sets.To_Set (Direct_Mapping_Id (Unique_Entity (E)));
         else
            return Flatten_Variable (E, Ctx.Scope);
         end if;
      end Merge_Entity;

      ------------
      -- Filter --
      ------------

      function Filter (Variables : Flow_Id_Sets.Set) return Flow_Id_Sets.Set
      is
      begin
         return Filtered_Variables : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set
         do
            for V of Variables loop
               if V.Kind not in Direct_Mapping | Record_Field
                 or else
                 not Ctx.Quantified_Variables_Introduced.Contains (V.Node)
               then
                  Filtered_Variables.Insert (V);
               end if;
            end loop;
         end return;
      end Filter;

      ------------------------
      -- Do_Subprogram_Call --
      ------------------------

      function Do_Subprogram_Call (Callsite : Node_Id)
                                   return Flow_Id_Sets.Set
      is
         Subprogram    : constant Entity_Id := Get_Called_Entity (Callsite);

         Global_Reads  : Flow_Id_Sets.Set;
         Global_Writes : Flow_Id_Sets.Set;

         Folding       : constant Boolean :=
           Ctx.Fold_Functions
           and then Ekind (Subprogram) = E_Function
           and then Has_Depends (Subprogram);

         Used_Reads    : Flow_Id_Sets.Set;

         V             : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

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

         declare
            Proof_Reads : Flow_Id_Sets.Set;
         begin
            Get_Globals (Subprogram          => Subprogram,
                         Scope               => Ctx.Scope,
                         Classwide           =>
                           Is_Dispatching_Call (Callsite),
                         Proof_Ins           => Proof_Reads,
                         Reads               => Global_Reads,
                         Writes              => Global_Writes,
                         Use_Deduced_Globals => Ctx.Use_Computed_Globals);

            if not Ctx.Fold_Functions then
               --  If we fold functions we're interested in real world,
               --  otherwise (this case) we're interested in the proof world
               --  too.
               Global_Reads.Union (Proof_Reads);
            end if;
         end;

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
                              Is_Dispatching_Call (Callsite),
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
           and then not Global_Writes.Is_Empty
         then
            Error_Msg_NE
              (Msg => "side effects of function & are not modeled in SPARK",
               N   => Callsite,
               E   => Subprogram);
         end if;

         --  Merge globals into the variables used

         for G of Global_Reads loop
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

         for G of Global_Writes loop
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

      function Do_Entity (E : Entity_Id)
                          return Flow_Id_Sets.Set
      is
      begin
         if Ctx.Quantified_Variables_Introduced.Contains (E) then
            return Flow_Id_Sets.Empty_Set;
         end if;

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

               elsif Ctx.Local_Constants.Contains (E)
                 or else Has_Variable_Input (E)
               then
                  --  If this constant:
                  --    * comes from source and is in Local_Constants
                  --    * or has variable input
                  --  then add it.
                  return Merge_Entity (E);

               end if;

            when E_Component
               --  E_Constant is dealt with in the above case
               | E_Discriminant
               | E_Loop_Parameter
               | E_Variable
               | E_Out_Parameter
               | E_In_Out_Parameter
               | E_In_Parameter
            =>
               if Ekind (E) = E_In_Parameter
                 and then Present (Discriminal_Link (E))
               then
                  return Do_Entity (Discriminal_Link (E));
               end if;

               --  Ignore discriminants and components unless they come
               --  from task or protected types.
               if Ekind (E) in E_Discriminant | E_Component
                 and then Ekind (Scope (E)) not in E_Protected_Type
                                                 | E_Task_Type
               then
                  return Flow_Id_Sets.Empty_Set;
               end if;

               return V : Flow_Id_Sets.Set := Merge_Entity (E) do
                  --  If we've extensions (and we care about them) then we
                  --  need to add them now.
                  if not Ctx.Reduced
                    and then Ctx.Consider_Extensions
                    and then Extensions_Visible (E, Ctx.Scope)
                  then
                     V.Include (Direct_Mapping_Id
                                  (Unique_Entity (E),
                                   Facet => Extension_Part));
                  end if;
               end return;

            when Scalar_Kind =>
               --  Types mostly get dealt with by membership tests here, but
               --  sometimes they just appear (for example in a for loop over a
               --  type).
               if Is_Constrained (E) then
                  declare
                     SR : constant Node_Id := Scalar_Range (E);
                     LB : constant Node_Id := Low_Bound (SR);
                     HB : constant Node_Id := High_Bound (SR);
                  begin
                     return Recurse (LB) or Recurse (HB);
                  end;
               end if;

            ---------------------------------------------------------
            -- Entities with no flow consequence (or not in SPARK) --
            ---------------------------------------------------------

            when E_Generic_In_Out_Parameter
               | E_Generic_In_Parameter
               | E_Generic_Function
               | E_Generic_Procedure
               | E_Generic_Package
            =>
               --  These are not in SPARK itself (we analyze instantiations
               --  instead of generics). So if we get one here, we are trying
               --  do something very wrong.
               raise Program_Error;

            when E_Void =>
               --  We should never feed a null node into this function
               raise Program_Error;

            when Access_Kind
               | E_Entry_Family
               | E_Entry_Index_Parameter
            =>
               --  Not in SPARK (at least for now)
               raise Why.Unexpected_Node;

            when E_Abstract_State =>
               --  Abstract state cannot directly appear in expressions, so if
               --  we have called this function on something that involves
               --  state then we've messed up somewhere.
               --
               --  Otherwise, we'll expand out into all the state we can see.
               pragma Assert (not Ctx.Assume_In_Expression);

               return Variables : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set
               do
                  for Constituent of Down_Project (E, Ctx.Scope) loop
                     if Ekind (Constituent) = E_Abstract_State then
                        Variables.Include (Direct_Mapping_Id (E));
                     else
                        Variables.Union (Do_Entity (Constituent));
                     end if;
                  end loop;
               end return;

            when Composite_Kind =>
               --  Dealt with using membership tests, if applicable
               null;

            when E_Named_Integer
               | E_Named_Real
               | E_Enumeration_Literal
            =>
               --  All of these are simply constants, with no flow concern
               null;

            when E_Function
               | E_Operator
               | E_Procedure
               | E_Entry
               | E_Subprogram_Type
            =>
               --  Dealt with when dealing with N_Subprogram_Call nodes
               null;

            when E_Block
               | E_Exception
               | E_Exception_Type
               | E_Label
               | E_Loop
               | E_Package
               | E_Package_Body
               | E_Protected_Object
               | E_Protected_Body
               | E_Task_Body
               | E_Subprogram_Body
               | E_Return_Statement
            =>
               --  Nothing to do for these directly
               null;

         end case;

         return Flow_Id_Sets.Empty_Set;
      end Do_Entity;

      ------------------------------
      -- Do_N_Attribute_Reference --
      ------------------------------

      function Do_N_Attribute_Reference (N : Node_Id)
                                         return Flow_Id_Sets.Set
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
                        pragma Assert (Ekind (T) in Scalar_Kind);
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
                           --  This is something else. We just copy it.
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
         --  looking at the prefix (i.e. address) or do something strange (i.e.
         --  update).

         Variables.Union (Recurse (Prefix (N)));

         declare
            Ptr : Node_Id := Empty;
         begin
            if Present (Expressions (N)) then
               Ptr := First (Expressions (N));
            end if;
            while Present (Ptr) loop
               Variables.Union (Recurse (Ptr));
               Next (Ptr);
            end loop;
         end;

         return Variables;
      end Do_N_Attribute_Reference;

      ------------------------------------------------
      -- Subprograms that *do* write into Variables --
      ------------------------------------------------

      Variables : Flow_Id_Sets.Set;

      function Proc (N : Node_Id) return Traverse_Result;
      --  Adds each identifier or defining_identifier found to Variables,
      --  as long as we are dealing with:
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

            when N_Later_Decl_Item =>
               pragma Assert (not Ctx.Assume_In_Expression);

               --  These should allow us to go through package specs and bodies
               return Skip;

            when N_Identifier | N_Expanded_Name =>
               if Present (Entity (N)) then
                  Variables.Union (Do_Entity (Entity (N)));
               end if;

            when N_Defining_Identifier =>
               Variables.Union (Do_Entity (N));

            when N_Aggregate =>
               Variables.Union (Recurse (Aggregate_Bounds (N)));

            when N_Selected_Component =>
               if Is_Subprogram_Or_Entry (Entity (Selector_Name (N))) then

                  --  Here we are dealing with a call of a protected
                  --  entry/function. This appears on the tree as a selected
                  --  component of the protected object.

                  Variables.Union (Do_Subprogram_Call (Parent (N)));

               elsif Ctx.Reduced then
                  --  In reduced mode we just keep traversing the tree, but
                  --  we need to turn off consider_extensions.
                  Variables.Union (Recurse (Prefix (N)));

               else
                  Variables.Union (Untangle_With_Context (N));
               end if;
               return Skip;

            when N_Type_Conversion =>
               if Ctx.Reduced then
                  return OK;

               elsif Ekind (Get_Type (N, Ctx.Scope)) in Record_Kind then
                  --  We use Untangle_Record_Assignment as this can deal
                  --  with view conversions.

                  declare
                     M : constant Flow_Id_Maps.Map :=
                       Untangle_Record_Assignment
                       (N,
                        Map_Root                     =>
                          Direct_Mapping_Id (Etype (N)),
                        Map_Type                     =>
                          Get_Type (N, Ctx.Scope),
                        Scope                        => Ctx.Scope,
                        Local_Constants              => Ctx.Local_Constants,
                        Fold_Functions               => Ctx.Fold_Functions,
                        Use_Computed_Globals         =>
                          Ctx.Use_Computed_Globals,
                        Expand_Synthesized_Constants =>
                          Ctx.Expand_Synthesized_Constants);
                  begin
                     for FS of M loop
                        Variables.Union (Filter (FS));
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
                  --  Merge variables used in predicate functions for the
                  --  given type.

                  ------------------
                  -- Process_Type --
                  ------------------

                  procedure Process_Type (E : Entity_Id) is
                     P : constant Entity_Id := Predicate_Function (E);

                     GP, GI, GO : Flow_Id_Sets.Set;
                  begin
                     if No (P) then
                        return;
                     end if;

                     --  Something to note here: we include the predicate
                     --  function in the set of called subprograms during
                     --  GG, but not in phase 2. The idea is that 'calling'
                     --  the subprogram will introduce the dependencies on
                     --  its global, wheras in phase 2 we directly include
                     --  its globals.

                     Get_Globals
                       (Subprogram          => P,
                        Scope               => Ctx.Scope,
                        Classwide           => False,
                        Proof_Ins           => GP,
                        Reads               => GI,
                        Writes              => GO,
                        Use_Deduced_Globals => Ctx.Use_Computed_Globals);
                     pragma Assert (GO.Is_Empty);
                     --  No function folding to deal with for predicate
                     --  functions (they always consume their single input).

                     declare
                        Effects : constant Flow_Id_Sets.Set := GP or GI;
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
                  Variables.Union (Recurse (It,
                                            With_Quantified_Variable => E));
                  Variables.Union (Recurse (Condition (N),
                                            With_Quantified_Variable => E));
               end;
               return Skip;

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);

   --  Start of processing for Get_Variables

   begin
      Traverse (N);

      return S : Flow_Id_Sets.Set do
         --  We need to do some post-processing on the result here. First
         --  we check each variable to see if it is the result of an
         --  action. For flow analysis its more helpful to talk about the
         --  original variables, so we undo these actions whenever
         --  possible.
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
         Remove_Constants (S, Skip => Ctx.Local_Constants);
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
            P := Next (P);
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
        (Scope                           => Get_Flow_Scope (Scope_N),
         Local_Constants                 => Node_Sets.Empty_Set,
         Fold_Functions                  => False,
         Use_Computed_Globals            => True,
         Reduced                         => True,
         Assume_In_Expression            => True,
         Expand_Synthesized_Constants    => False,
         Consider_Extensions             => False,
         Quantified_Variables_Introduced => Node_Sets.Empty_Set);
   begin
      return Get_Variables_Internal (Expr_N, Ctx);
   end Get_Variables_For_Proof;

   -----------------
   -- Has_Depends --
   -----------------

   function Has_Depends (Subprogram : Entity_Id) return Boolean is
   begin
      return Present (Find_Contract (Subprogram, Pragma_Depends));
   end Has_Depends;

   ----------------------------
   -- Has_Proof_Global_Reads --
   ----------------------------

   function Has_Proof_Global_Reads (Subprogram : Entity_Id;
                                    Classwide  : Boolean)
                                    return Boolean
   is
      Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids : Flow_Types.Flow_Id_Sets.Set;
   begin
      Get_Proof_Globals (Subprogram => Subprogram,
                         Classwide  => Classwide,
                         Reads      => Read_Ids,
                         Writes     => Write_Ids);
      return not Read_Ids.Is_Empty;
   end Has_Proof_Global_Reads;

   -----------------------------
   -- Has_Proof_Global_Writes --
   -----------------------------

   function Has_Proof_Global_Writes (Subprogram : Entity_Id;
                                     Classwide  : Boolean)
                                     return Boolean
   is
      Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids : Flow_Types.Flow_Id_Sets.Set;
   begin
      Get_Proof_Globals (Subprogram => Subprogram,
                         Classwide  => Classwide,
                         Reads      => Read_Ids,
                         Writes     => Write_Ids);
      return not Write_Ids.Is_Empty;
   end Has_Proof_Global_Writes;

   ------------------------
   -- Has_Variable_Input --
   ------------------------

   function Has_Variable_Input (C : Entity_Id) return Boolean is
      E    : Entity_Id := C;
      Decl : Node_Id;
      FS   : Flow_Id_Sets.Set;

   begin
      --  This routine is mirrored in Variable_Inputs_Of_Constants;
      --  any change here should be reflected there.
      --  ??? ideally, this should be refactored

      if Is_Imported (E) then
         --  If we are dealing with an imported constant, we consider this to
         --  have potentially variable input.
         return True;
      end if;

      Decl := Declaration_Node (E);
      if No (Expression (Decl)) then
         --  We are dealing with a deferred constant so we need to get to the
         --  full view.
         E    := Full_View (E);
         Decl := Declaration_Node (E);
      end if;

      if not Entity_In_SPARK (E) then
         --  We are dealing with an entity that is not in SPARK so we assume
         --  that it does not have variable input.
         return False;
      end if;

      FS := Get_Variables
        (Expression (Decl),
         Scope                => Get_Flow_Scope (E),
         Local_Constants      => Node_Sets.Empty_Set,
         Fold_Functions       => True,
         Use_Computed_Globals => GG_Has_Been_Generated);
      --  Note that Get_Variables calls Has_Variable_Input when it finds a
      --  constant. This means that there might be some mutual recursion here
      --  (but this should be fine).

      if not FS.Is_Empty then
         --  If any variable was found then return True
         return True;
      end if;

      if GG_Has_Been_Generated
        or else
        Get_Functions (Expression (Decl),
                       Include_Predicates => False).Is_Empty
      then
         --  If we reach this point then the constant does not have variable
         --  input.
         return False;
      else
         --  Globals have not yet been computed. If we find any function calls
         --  we consider the constant to have variable inputs (this is the safe
         --  thing to do).
         return True;
      end if;
   end Has_Variable_Input;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
      use Component_Graphs;

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

      Ptr      : Entity_Id;
      Ptr2     : Entity_Id;

      S        : Node_Sets.Set;

      Inserted : Boolean;
      --  Indicates than an element was inserted to a set

      Unused   : Node_Sets.Cursor;
      --  Dummy variable required by the standard containers API

   --  Start of processing for Initialize

   begin
      Comp_Graph := Component_Graphs.Create;

      S := Node_Sets.Empty_Set;
      for E of Marked_Entities loop
         --  ??? we should iterate over Entities_To_Translate, which only
         --  contains entities in SPARK; currently we iterate over
         --  Marked_Entities, which includes types not in SPARK.
         if Is_Record_Type (E)
           or else Ekind (E) in E_Protected_Type | E_Task_Type
         then
            Ptr := First_Component_Or_Discriminant (E);

            while Present (Ptr) loop
               S.Insert (New_Item => Ptr,
                         Position => Unused,
                         Inserted => Inserted);

               if Inserted then
                  Comp_Graph.Add_Vertex (Ptr);
               end if;

               declare
                  Orig_Rec_Comp : constant Node_Id :=
                    Original_Record_Component (Ptr);
               begin
                  if Present (Orig_Rec_Comp) then
                     S.Insert (New_Item => Orig_Rec_Comp,
                               Position => Unused,
                               Inserted => Inserted);
                     if Inserted then
                        Comp_Graph.Add_Vertex (Orig_Rec_Comp);
                     end if;
                  end if;
               end;

               if Ekind (Ptr) = E_Discriminant then
                  declare
                     Corr_Discr : constant Node_Id :=
                       Corresponding_Discriminant (Ptr);
                  begin
                     if Present (Corr_Discr) then
                        S.Insert (New_Item => Corr_Discr,
                                  Position => Unused,
                                  Inserted => Inserted);
                        if Inserted then
                           Comp_Graph.Add_Vertex (Corr_Discr);
                        end if;
                     end if;
                  end;
               end if;

               Next_Component_Or_Discriminant (Ptr);
            end loop;
         end if;
      end loop;

      S := Node_Sets.Empty_Set;
      for V of Comp_Graph.Get_Collection (All_Vertices) loop
         Ptr := Comp_Graph.Get_Key (V);
         S.Include (Ptr);
         if Present (Original_Record_Component (Ptr)) then
            Comp_Graph.Add_Edge (V_1    => Ptr,
                                 V_2    => Original_Record_Component (Ptr),
                                 Colour => 0);
         end if;
         case Ekind (Ptr) is
            when E_Discriminant =>
               if Present (Corresponding_Discriminant (Ptr)) then
                  Comp_Graph.Add_Edge
                    (V_1    => Ptr,
                     V_2    => Corresponding_Discriminant (Ptr),
                     Colour => 0);
               end if;
            when E_Component =>
               null;
            when others =>
               raise Program_Error;
         end case;
         for V2 of Comp_Graph.Get_Collection (All_Vertices) loop
            exit when V = V2;
            Ptr2 := Comp_Graph.Get_Key (V2);
            if Sloc (Ptr) = Sloc (Ptr2) then
               Comp_Graph.Add_Edge (V_1    => V,
                                    V_2    => V2,
                                    Colour => 0);
            end if;
         end loop;
      end loop;

      declare
         C         : Cluster_Id;
         Work_List : Node_Sets.Set;
      begin
         while not S.Is_Empty loop
            --  Pick an element at random.
            Ptr := S.First_Element;
            S.Exclude (Ptr);

            --  Create a new component.
            Comp_Graph.New_Cluster (C);

            --  Seed the work list.
            Work_List := Node_Sets.To_Set (Ptr);

            --  Flood current component.
            while not Work_List.Is_Empty loop
               Ptr := Work_List.First_Element;
               S.Exclude (Ptr);
               Work_List.Exclude (Ptr);

               Comp_Graph.Set_Cluster (Comp_Graph.Get_Vertex (Ptr), C);

               for Neighbour_Kind in Collection_Type_T range
                 Out_Neighbours .. In_Neighbours
               loop
                  for V of Comp_Graph.Get_Collection
                    (Comp_Graph.Get_Vertex (Ptr), Neighbour_Kind)
                  loop
                     Ptr := Comp_Graph.Get_Key (V);
                     if S.Contains (Ptr) then
                        Work_List.Include (Ptr);
                     end if;
                  end loop;
               end loop;
            end loop;
         end loop;
      end;

      if Debug_Record_Component then
         Comp_Graph.Write_Pdf_File (Filename  => "component_graph",
                                    Node_Info => Node_Info'Access,
                                    Edge_Info => Edge_Info'Access);
      end if;

      Init_Done := True;
   end Initialize;

   ---------------------
   -- Is_Ghost_Object --
   ---------------------

   function Is_Ghost_Object (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               return Is_Object (E)
                 and then Is_Ghost_Entity (E);
            end;

         when others =>
            return False;
      end case;
   end Is_Ghost_Object;

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
   -- Is_Non_Visible_Constituent --
   --------------------------------

   function Is_Non_Visible_Constituent
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Boolean
   is
   begin
      if F.Kind = Direct_Mapping then
         declare
            E : constant Entity_Id := Get_Direct_Mapping_Id (F);
         begin
            --  Up-projecting makes sense only if the following is True
            --  ??? use Is_Constituent here
            return Ekind (E) in E_Abstract_State | E_Constant | E_Variable
              and then (Present (Encapsulating_State (E))
                          or else Belongs_To_Concurrent_Type (F))
              and then not Is_Visible (E, Scope);
         end;

      --  We can't possibly up-project something that does not correspond to a
      --  direct mapping.

      else
         return False;
      end if;
   end Is_Non_Visible_Constituent;

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
            when N_Identifier | N_Expanded_Name =>
               return True;
            when N_Type_Conversion | N_Unchecked_Type_Conversion =>
               Ptr := Expression (Ptr);
            when N_Indexed_Component | N_Slice | N_Selected_Component =>
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

   -----------------------
   -- Loop_Writes_Known --
   -----------------------

   function Loop_Writes_Known (E : Entity_Id) return Boolean is
   begin
      return Loop_Info_Frozen and then Loop_Info.Contains (E);
   end Loop_Writes_Known;

   -----------------------
   -- Original_Constant --
   -----------------------

   function Original_Constant (N : Node_Id) return Entity_Id is
      Orig_Node : constant Node_Id := Original_Node (N);
      pragma Assert (N /= Orig_Node);

   begin
      return Entity (Orig_Node);
   end Original_Constant;

   --------------------------
   -- Quantified_Variables --
   --------------------------

   function Quantified_Variables (N : Node_Id) return Flow_Id_Sets.Set is
      RV : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

      function Proc (N : Node_Id) return Traverse_Result;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) = N_Quantified_Expression then
            pragma Assert (Present (Iterator_Specification (N))
                             xor
                           Present (Loop_Parameter_Specification (N)));

            RV.Insert (Direct_Mapping_Id
                       (Defining_Identifier
                          (if Present (Iterator_Specification (N))
                           then Iterator_Specification (N)
                           else Loop_Parameter_Specification (N))));
         end if;

         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Proc);

   --  Start of processing for Quantified_Variables

   begin
      Traverse (N);
      return RV;
   end Quantified_Variables;

   ------------------------------
   -- Rely_On_Generated_Global --
   ------------------------------

   function Rely_On_Generated_Global
     (E     : Entity_Id;
      Scope : Flow_Scope)
      return Boolean
   is
      Body_E : constant Entity_Id := Get_Body_Entity (E);
   begin
      return Present (Body_E)
        and then Entity_Body_In_SPARK (E)
        and then Is_Visible (Body_E, Scope)
        and then Refinement_Needed (E);
   end Rely_On_Generated_Global;

   ----------------------
   -- Remove_Constants --
   ----------------------

   procedure Remove_Constants
     (Objects              : in out Flow_Id_Sets.Set;
      Skip                 :        Node_Sets.Set := Node_Sets.Empty_Set;
      Only_Generic_Formals :        Boolean       := False)
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
                    and then not Skip.Contains (E)
                    and then not Has_Variable_Input (E)
                    and then (In_Generic_Actual (E)
                              or else not Only_Generic_Formals)
                  then
                     Constants.Insert (F);
                  end if;
               end;

            when Magic_String =>
               pragma Assert (not Only_Generic_Formals);
               --  Filtering magic strings for generic formals is meaningless

            when Synthetic_Null_Export =>
               null;

            when Null_Value =>
               raise Program_Error;
         end case;
      end loop;

      Objects.Difference (Constants);
   end Remove_Constants;

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
   -- Search_Contract --
   ---------------------

   function Search_Contract (Unit     : Entity_Id;
                             Contract : Pragma_Id;
                             Output   : Entity_Id;
                             Input    : Entity_Id := Empty)
                             return Node_Id
   is

      Contract_N : Node_Id;
      Needle     : Node_Id := Empty;

      function Proc (N : Node_Id) return Traverse_Result;
      --  Searches under contract for Output and sets Needle to the node, if
      --  found.

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
         Tmp, Tmp2 : Node_Id;
         O, I      : Entity_Id;
      begin
         case Nkind (N) is
            when N_Component_Association =>
               Tmp := First (Choices (N));
               while Present (Tmp) loop
                  case Nkind (Tmp) is
                     when N_Attribute_Reference =>
                        O := Entity (Prefix (Tmp));
                     when N_Identifier | N_Expanded_Name =>
                        O := Entity (Tmp);
                     when N_Null | N_Aggregate =>
                        O := Empty;
                     when N_Numeric_Or_String_Literal =>
                        --  We should only ever get here if we are
                        --  dealing with a rewritten constant.
                        pragma Assert (Tmp /= Original_Node (Tmp));

                        --  We process the entity of the
                        --  Original_Node instead
                        O := Entity (Original_Node (Tmp));

                     when others =>
                        raise Program_Error;
                  end case;
                  if O = Output then
                     Needle := Tmp;
                     if No (Input) then
                        return Abandon;
                     end if;

                     --  Look for specific input Input of export
                     Tmp2 := Expression (Parent (Tmp));
                     case Nkind (Tmp2) is
                        when N_Attribute_Reference =>
                           I := Entity (Prefix (Tmp2));
                        when N_Identifier | N_Expanded_Name =>
                           I := Entity (Tmp2);
                        when N_Null =>
                           I := Empty;
                        when N_Aggregate =>
                           Tmp2 := First (Expressions (Tmp2));

                           while Present (Tmp2) loop
                              case Nkind (Tmp2) is
                                 when N_Attribute_Reference =>
                                    I := Entity (Prefix (Tmp2));
                                 when N_Identifier | N_Expanded_Name =>
                                    I := Entity (Tmp2);
                                 when N_Null | N_Aggregate =>
                                    I := Empty;
                                 when N_Numeric_Or_String_Literal =>
                                    --  We should only ever get here
                                    --  if we are dealing with a
                                    --  rewritten constant.
                                    pragma Assert
                                      (Tmp2 /= Original_Node (Tmp2));

                                    --  We process the entity of the
                                    --  Original_Node instead
                                    I := Entity (Original_Node (Tmp2));

                                 when others =>
                                    raise Program_Error;
                              end case;
                              if I = Input then
                                 Needle := Tmp2;
                                 return Abandon;
                              end if;
                              Tmp2 := Next (Tmp2);
                           end loop;
                        when N_Numeric_Or_String_Literal =>
                           --  We should only ever get here if we are
                           --  dealing with a rewritten constant.
                           pragma Assert (Tmp2 /= Original_Node (Tmp2));

                           --  We process the entity of the
                           --  Original_Node instead
                           I := Entity (Original_Node (Tmp2));

                        when others =>
                           raise Program_Error;
                     end case;

                     if I = Input then
                        Needle := Tmp2;
                        return Abandon;
                     end if;

                  end if;
                  Tmp := Next (Tmp);
               end loop;
               return Skip;

            when N_Aggregate =>
               --  We only want to process the aggregate if it hangs
               --  directly under the pragma.
               --
               --  Note that in this kind of tree we cannot possibly
               --  find an Input (since no inputs exist). We can at
               --  best find the Output.
               if Nkind (Parent (N)) /= N_Pragma_Argument_Association then
                  return OK;
               end if;

               Tmp := First (Expressions (N));
               while Present (Tmp) loop
                  case Nkind (Tmp) is
                     when N_Attribute_Reference =>
                        O := Entity (Prefix (Tmp));
                     when N_Identifier | N_Expanded_Name =>
                        O := Entity (Tmp);
                     when N_Null | N_Aggregate =>
                        O := Empty;
                     when N_Numeric_Or_String_Literal =>
                        --  We should only ever get here if we are
                        --  dealing with a rewritten constant.
                        pragma Assert (Tmp /= Original_Node (Tmp));

                        --  We process the entity of the Original_Node
                        --  instead.
                        O := Entity (Original_Node (Tmp));

                     when others =>
                        raise Program_Error;
                  end case;
                  if O = Output then
                     Needle := Tmp;
                     return Abandon;
                  end if;
                  Tmp := Next (Tmp);
               end loop;

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Find_Export_Internal is new Traverse_Proc (Proc);

   --  Start of processing for Search_Contract

   begin
      case Contract is
         when Pragma_Depends =>
            Contract_N := Find_Contract (Unit, Pragma_Refined_Depends);

            if No (Contract_N) then
               Contract_N := Find_Contract (Unit, Pragma_Depends);
            end if;

         when Pragma_Initializes =>
            Contract_N := Get_Pragma (Unit, Pragma_Initializes);

         when others =>
            raise Program_Error;
      end case;

      if Present (Contract_N) then
         Find_Export_Internal (Contract_N);

         return (if Present (Needle)
                   then Needle
                   else Contract_N);
      else
         return Unit;
      end if;

   end Search_Contract;

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
      Local_Constants              : Node_Sets.Set;
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
             Local_Constants              => Local_Constants,
             Fold_Functions               => Fold_Functions,
             Use_Computed_Globals         => Use_Computed_Globals,
             Reduced                      => False,
             Expand_Synthesized_Constants => Expand_Synthesized_Constants));
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
             Local_Constants              => Local_Constants,
             Fold_Functions               => Fold_Functions,
             Use_Computed_Globals         => Use_Computed_Globals,
             Expand_Synthesized_Constants => Expand_Synthesized_Constants,
             Extensions_Irrelevant        => Ext_Irrelevant))
      with Pre => (if not Extensions_Irrelevant
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

      procedure Merge (Component : Entity_Id;
                       Input     : Node_Id)
      with Pre => Nkind (Component) in N_Entity
                  and then Ekind (Component) in E_Component | E_Discriminant
                  and then Present (Input);
      --  Merge the assignment map for Input into our current assignment
      --  map M. For example, if the input is (X => A, Y => B) and
      --  Component is C, and Map_Root is Obj, then we include in M the
      --  following: Obj.C.X => A, Obj.C.Y => B.
      --
      --  If Input is not some kind of record, we simply include a single
      --  field. For example if the input is simply Foo, then (all other
      --  things being equal to the example above) we include Obj.C => Foo.

      M : Flow_Id_Maps.Map := Flow_Id_Maps.Empty_Map;

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
         if B.Kind in Record_Field then
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

      procedure Merge (Component : Entity_Id;
                       Input     : Node_Id)
      is
         F   : constant Flow_Id := Add_Component (Map_Root, Component);
         Tmp : Flow_Id_Maps.Map;
      begin
         case Ekind (Get_Type (Component, Scope)) is
            when Record_Kind =>
               Tmp := Recurse_On (Input, F);

               for C in Tmp.Iterate loop
                  declare
                     Output : Flow_Id          renames Flow_Id_Maps.Key (C);
                     Inputs : Flow_Id_Sets.Set renames Tmp (C);
                  begin
                     M.Include (Output, Inputs);
                  end;
               end loop;

            when others =>
               declare
                  FS : constant Flow_Id_Sets.Set :=
                    Flatten_Variable (F, Scope);
               begin
                  for Id of FS loop
                     M.Include (Id, Get_Vars_Wrapper (Input));
                  end loop;
               end;
         end case;
      end Merge;

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
               Ptr     : Node_Id;
               Input   : Node_Id;
               Target  : Node_Id;
               Missing : Component_Sets.Set := Component_Sets.Empty_Set;
               FS      : Flow_Id_Sets.Set;
            begin
               for Ptr of Components (Map_Type) loop
                  Missing.Include (Original_Record_Component (Ptr));
               end loop;

               Ptr := First (Component_Associations (N));
               while Present (Ptr) loop
                  Input  := Expression (Ptr);
                  Target := First (Choices (Ptr));
                  while Present (Target) loop
                     Merge (Entity (Target), Input);
                     Missing.Delete (Original_Record_Component
                                       (Entity (Target)));
                     Next (Target);
                  end loop;
                  Next (Ptr);
               end loop;

               --  If the aggregate is more constrained than the type would
               --  suggest, we fill in the "missing" fields with null, so
               --  that they appear initialized.
               for Missing_Component of Missing loop
                  FS := Flatten_Variable (Add_Component (Map_Root,
                                                         Missing_Component),
                                          Scope);
                  for F of FS loop
                     M.Insert (F, Flow_Id_Sets.Empty_Set);
                  end loop;
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
               Output : Flow_Id;
               Inputs : Flow_Id_Sets.Set;
            begin
               for C in Tmp.Iterate loop
                  Output := Flow_Id_Maps.Key (C);
                  Inputs := Flow_Id_Maps.Element (C);

                  if Same_Component (Output.Component.First_Element,
                                     Entity (Selector_Name (N)))
                  then
                     M.Include (Join (Map_Root, Output, 1), Inputs);
                  end if;
               end loop;
            end;

         when N_Identifier | N_Expanded_Name =>
            if Debug_Trace_Untangle_Record then
               Write_Str ("processing direct assignment");
               Write_Eol;
            end if;

            declare
               Simplify : constant Boolean :=
                 Ekind (Entity (N)) = E_Constant and then
                 not Local_Constants.Contains (Entity (N));
               --  We're assigning a local constant; and currently we just
               --  use get_variable_set to "look through" it. We simply
               --  assign all fields of the LHS to the RHS. Not as precise
               --  as it could be, but it works for now...

               LHS : constant Flow_Id_Sets.Set :=
                 Flatten_Variable (Map_Root, Scope);

               LHS_Ext : constant Flow_Id :=
                 Map_Root'Update (Facet => Extension_Part);

               RHS : Flow_Id_Sets.Set :=
                 Flatten_Variable (Entity (N), Scope);

               To_Ext : Flow_Id_Sets.Set;
               F      : Flow_Id;
            begin
               if Extensions_Visible (Entity (N), Scope)
                 and then ((Is_Class_Wide_Type (Map_Type) and then
                              not Is_Class_Wide_Type (Etype (N)))
                             or else not Extensions_Irrelevant)
               then
                  --  This is an implicit conversion to class wide, or we
                  --  for some other reason care specifically about the
                  --  extensions.
                  RHS.Include (Direct_Mapping_Id (Entity (N),
                                                  Facet => Extension_Part));
                  --  RHS.Include (Direct_Mapping_Id (Entity (N),
                  --                                  Facet => The_Tag));
               end if;
               if Simplify then
                  for Input of RHS loop
                     M.Include (Join (Map_Root, Input),
                                Get_Vars_Wrapper (N));
                  end loop;
               else
                  To_Ext := Flow_Id_Sets.Empty_Set;
                  for Input of RHS loop
                     F := Join (Map_Root, Input);
                     if LHS.Contains (F) then
                        M.Include (F, Flow_Id_Sets.To_Set (Input));
                     else
                        To_Ext.Include (Input);
                     end if;
                  end loop;
                  if not To_Ext.Is_Empty
                    and then Is_Tagged_Type (Map_Type)
                  then
                     if not M.Contains (LHS_Ext) then
                        M.Include (LHS_Ext, Flow_Id_Sets.Empty_Set);
                     end if;
                     M (LHS_Ext).Union (To_Ext);
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
                 not Is_Class_Wide_Type (T_From) and then
                 Is_Class_Wide_Type (T_To);

               Tmp : constant Flow_Id_Maps.Map :=
                 Recurse_On (Expression (N),
                             Map_Root,
                             Ext_Irrelevant =>
                               not (Class_Wide_Conversion or
                                      not Extensions_Irrelevant));
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

               Valid_To_Fields := Flow_Id_Sets.Empty_Set;
               for F of Flatten_Variable (T_To, Scope) loop
                  Valid_To_Fields.Include (Join (Map_Root, F));
               end loop;

               for C in Tmp.Iterate loop
                  declare
                     Output : Flow_Id          renames Flow_Id_Maps.Key (C);
                     Inputs : Flow_Id_Sets.Set renames Tmp (C);
                  begin
                     if Valid_To_Fields.Contains (Output) then
                        M.Include (Output, Inputs);
                        Valid_To_Fields.Exclude (Output);
                     end if;
                  end;
               end loop;

               if Valid_To_Fields.Contains (The_Tg) then
                  if not M.Contains (The_Tg) then
                     M.Include (The_Tg, Flow_Id_Sets.Empty_Set);
                  end if;
                  Valid_To_Fields.Exclude (The_Tg);
               end if;

               if Valid_To_Fields.Contains (The_Ext) then
                  if not M.Contains (The_Ext) then
                     M.Include (The_Ext, Flow_Id_Sets.Empty_Set);
                  end if;
                  Valid_To_Fields.Exclude (The_Ext);
                  M (The_Ext).Union (Valid_To_Fields);
               end if;
            end;

         when N_Qualified_Expression =>
            --  We can completely ignore these.
            M := Recurse_On (Expression (N), Map_Root, Map_Type);

         when N_Unchecked_Type_Conversion =>
            raise Why.Not_Implemented;

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
                         and then
                       Is_Class_Wide_Type (Map_Type);
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

               when others =>
                  Error_Msg_N ("cannot untangle attribute", N);
                  raise Why.Not_Implemented;
            end case;

         when N_Function_Call | N_Indexed_Component =>
            --  For these we just summarize the entire blob.

            declare
               FS  : constant Flow_Id_Sets.Set := Get_Vars_Wrapper (N);
               LHS : Flow_Id_Sets.Set;
            begin
               if M.Is_Empty then
                  LHS := Flatten_Variable (Map_Root, Scope);

                  for Comp of LHS loop
                     M.Include (Comp, FS);
                  end loop;
               else
                  for Output of M loop
                     Output.Union (FS);
                  end loop;
               end if;
            end;

         when others =>
            declare
               S : constant String := Nkind (N)'Img;
            begin
               Error_Msg_Strlen := S'Length;
               Error_Msg_String (1 .. Error_Msg_Strlen) := S;
               Error_Msg_N ("cannot untangle node ~", N);
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

   ----------------------------
   -- Untangle_Record_Fields --
   ----------------------------

   function Untangle_Record_Fields
     (N                            : Node_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
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
             Local_Constants              => Local_Constants,
             Fold_Functions               => Fold_Functions,
             Use_Computed_Globals         => Use_Computed_Globals,
             Reduced                      => False,
             Expand_Synthesized_Constants => Expand_Synthesized_Constants));

      M             : Flow_Id_Maps.Map          := Flow_Id_Maps.Empty_Map;

      Root_Node     : Node_Id                   := N;

      Component     : Entity_Vectors.Vector     := Entity_Vectors.Empty_Vector;

      Seq           : Node_Lists.List           := Node_Lists.Empty_List;

      E             : Entity_Id;
      Comp_Id       : Natural;
      Current_Field : Flow_Id;

      Must_Abort    : Boolean                   := False;

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
      --  We also note all components (bar, z), 'update nodes and the order in
      --  which they access or update fields (bar, the_update, z).

      while Nkind (Root_Node) = N_Selected_Component or else
        (Is_Attribute_Update (Root_Node) and then
           Is_Record_Type (Get_Full_Type_Without_Checking (Root_Node)))
          or else
        Is_Ignored_Node (Root_Node)
      loop
         if Nkind (Root_Node) = N_Selected_Component then
            Component.Prepend
              (Original_Record_Component (Entity (Selector_Name (Root_Node))));
         end if;
         if not Is_Ignored_Node (Root_Node) then
            Seq.Prepend (Root_Node);
         end if;
         Root_Node := Prefix (Root_Node);
      end loop;

      if Root_Node = N then
         --  In some case Arr'Update (...) we need to make sure that Seq
         --  contains the 'Update so that the early abort can handle
         --  things...
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

      --  If the root node is not an entire record variable, we recurse
      --  here and then simply merge all variables we find here and then
      --  abort.

      if Nkind (Root_Node) not in N_Identifier | N_Expanded_Name or else
        not Is_Record_Type (Get_Full_Type_Without_Checking (Root_Node))
      then
         return Vars : Flow_Id_Sets.Set do
            --  Recurse on root.
            Vars := Get_Vars_Wrapper (Root_Node);

            --  Add anything we might find in 'Update expressions
            for N of Seq loop
               case Nkind (N) is
                  when N_Attribute_Reference =>
                     pragma Assert (Get_Attribute_Id (Attribute_Name (N)) =
                                      Attribute_Update);
                     pragma Assert (List_Length (Expressions (N)) = 1);

                     declare
                        Ptr : Node_Id := First (Component_Associations
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
      --  further...

      pragma Assert (Nkind (Root_Node) in N_Identifier | N_Expanded_Name);
      pragma Assert (not Must_Abort);

      --  We set up an identity map of all fields of the original record.
      --  For example a record with two fields would produce this kind of
      --  map:
      --
      --     r.x -> r.x
      --     r.y -> r.y

      declare
         FS : constant Flow_Id_Sets.Set :=
           Flatten_Variable (Entity (Root_Node), Scope);
      begin
         for F of FS loop
            M.Insert (F, Flow_Id_Sets.To_Set (F));
         end loop;
         if Debug_Trace_Untangle_Fields then
            Print_Flow_Map (M);
         end if;
      end;

      --  We then process Seq (the sequence of actions we have been asked
      --  to take) and update the map or eliminate entries from it.
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

      --  Finally a note about function folding: on each update we merge
      --  all variables used in All_Vars so that subsequent trimmings don't
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
               pragma Assert (Get_Attribute_Id (Attribute_Name (N)) =
                                Attribute_Update);

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
               --  We trim the result map
               E := Original_Record_Component (Entity (Selector_Name (N)));
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
                           New_Map.Insert (K, V);
                        end if;
                     end;
                  end loop;
                  M := New_Map;
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

   --------------------------------
   -- Untangle_Assignment_Target --
   --------------------------------

   procedure Untangle_Assignment_Target
     (N                    : Node_Id;
      Scope                : Flow_Scope;
      Local_Constants      : Node_Sets.Set;
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
             Local_Constants      => Local_Constants,
             Fold_Functions       => Fold,
             Use_Computed_Globals => Use_Computed_Globals,
             Reduced              => False));

      Unused                   : Boolean;
      Classwide                : Boolean;
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
         Classwide          => Classwide,
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
                     Old_Typ  : constant Entity_Id        :=
                       Etype (Expression (N));
                     New_Typ  : constant Entity_Id        := Etype (N);
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
                  Ptr  : Node_Id := First (Expressions (N));
                  A, B : Flow_Id_Sets.Set;
               begin
                  while Present (Ptr) loop
                     A := Get_Vars_Wrapper (Ptr, Fold => False);
                     B := Get_Vars_Wrapper (Ptr, Fold => True);
                     Vars_Used.Union (B);
                     Vars_Proof.Union (A - B);

                     Next (Ptr);
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

            when N_Selected_Component =>
               Idx := Idx + 1;

            when N_Unchecked_Type_Conversion =>
               null;

            when others =>
               raise Why.Unexpected_Node;

         end case;
      end loop;

      if Classwide then
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

   ----------------------------
   -- Up_Project_Constituent --
   ----------------------------

   function Up_Project_Constituent
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Flow_Id
   is
      Enclosing_F : Flow_Id;
      Enclosing_E : Entity_Id;
   begin
      Enclosing_F := F;
      Enclosing_E := Get_Direct_Mapping_Id (F);
      while Is_Non_Visible_Constituent (Enclosing_F, Scope) loop
         declare
            State : constant Entity_Id := Encapsulating_State (Enclosing_E);
         begin
            Enclosing_E := (if Present (State)
                            then State
                            else Enclosing_Concurrent_Type (F));
         end;
         Enclosing_F := Direct_Mapping_Id (Enclosing_E, Variant => F.Variant);
      end loop;

      return Enclosing_F;
   end Up_Project_Constituent;

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

   ------------------
   -- Parent_State --
   ------------------

   function Parent_State (E : Entity_Id) return Entity_Id is
     (if Ekind (E) in E_Abstract_State |
                      E_Constant       |
                      E_Variable
      then Encapsulating_State (E)
      else Empty);

   ----------------------
   -- Canonical_Entity --
   ----------------------

   function Canonical_Entity
     (Ref     : Entity_Id;
      Context : Entity_Id)
      return Entity_Id
   is
   begin
      if Is_Single_Concurrent_Object (Ref)
        and then Is_CCT_Instance (Ref_Id => Etype (Ref), Context_Id => Context)
      then
         return Etype (Ref);
      else
         return Unique_Entity (Ref);
      end if;
   end Canonical_Entity;

end Flow_Utility;
