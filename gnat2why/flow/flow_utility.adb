------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2013-2015, Altran UK Limited                 --
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
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Elists;                     use Elists;
with Errout;                     use Errout;
with Flow_Classwide;             use Flow_Classwide;
with Flow_Debug;                 use Flow_Debug;
with Flow_Generated_Globals;     use Flow_Generated_Globals;
with Gnat2Why.Util;
with Graphs;
with Namet;                      use Namet;
with Nlists;                     use Nlists;
with Output;                     use Output;
with Sem_Aux;                    use Sem_Aux;
with Sem_Eval;                   use Sem_Eval;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Util;                 use SPARK_Util;
with Sprint;                     use Sprint;
with Treepr;                     use Treepr;
with Why;

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

   function Filter_Out_Constants
     (S : Flow_Id_Sets.Set;
      C : Node_Sets.Set)
      return Flow_Id_Sets.Set;
   --  Remove from set S all Flow_Ids that do not correspond to
   --  constants that have Has_Variable_Input and are not
   --  contained in C.
   --  @param S is the initial set of Flow_Ids
   --  @param C is the set of Node base on which filtering will occur
   --  @return a subset of S so that all Flow_Ids that do not correspond to
   --    constants that Has_Variable_Input or constants that are not
   --    contained in C have been removed.

   --------------
   -- Add_Loop --
   --------------

   procedure Add_Loop (E : Entity_Id) is
   begin
      pragma Assert (not Loop_Info_Frozen);
      Loop_Info.Insert (E, Flow_Id_Sets.Empty_Set);
   end Add_Loop;

   --------------------
   -- Add_Loop_Write --
   --------------------

   procedure Add_Loop_Write (E : Entity_Id;
                             F : Flow_Id)
   is
   begin
      pragma Assert (not Loop_Info_Frozen);
      pragma Assert (Loop_Info.Contains (E));
      Loop_Info (E).Include (F);
   end Add_Loop_Write;

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
      Append (Temp_String, '\');
      Append (Temp_String, 'n');
   end Add_To_Temp_String;

   --------------------
   -- All_Components --
   --------------------

   function All_Components (E : Entity_Id) return Node_Lists.List is
      Ptr : Entity_Id;
      T   : Entity_Id          := E;
      L   : Node_Lists.List    := Node_Lists.Empty_List;
      S   : Component_Sets.Set := Component_Sets.Empty_Set;

      function Up (E : Entity_Id) return Entity_Id;
      --  Get parent type, but don't consider record subtypes' ancestors.

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
      if not (Is_Record_Type (E)
                or else Is_Concurrent_Type (E)
                or else Is_Incomplete_Or_Private_Type (E)
                or else Has_Discriminants (E))
      then
         --  No components or discriminants to return
         return L;
      end if;

      loop
         Ptr := First_Component_Or_Discriminant (T);
         while Present (Ptr) loop
            if not S.Contains (Ptr) then
               S.Include (Ptr);
               L.Append (Ptr);
            end if;
            Next_Component_Or_Discriminant (Ptr);
         end loop;
         exit when Up (T) = T;
         T := Up (T);
      end loop;

      return L;
   end All_Components;

   -------------------------------------------
   -- Collect_Functions_And_Read_Locked_POs --
   -------------------------------------------

   procedure Collect_Functions_And_Read_Locked_POs
     (N                  : Node_Id;
      Functions_Called   : out Node_Sets.Set;
      Tasking            : in out Tasking_Info;
      Include_Predicates : Boolean)
   is
      Scope : constant Flow_Scope := Get_Flow_Scope (N);

      function Proc (N : Node_Id) return Traverse_Result;
      --  If the node being processed is an N_Function_Call, store a
      --  corresponding Flow_Id; for protected functions store the
      --  read-locked protected object.

      procedure Process_Type (E : Entity_Id);
      --  Merge predicate function for the given type.

      ------------------
      -- Process_Type --
      ------------------

      procedure Process_Type (E : Entity_Id)
      is
         P : Node_Id;
      begin
         if Include_Predicates and then Present (E) then
            P := Predicate_Function (E);
         else
            return;
         end if;

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
               Functions_Called.Include (Get_Called_Entity (N));

               --  Collect only external calls to protected functions; internal
               --  calls must be called from the outside anyway.
               if Convention (Get_Called_Entity (N)) = Convention_Protected
                 and then Nkind (Name (N)) = N_Selected_Component
               then
                  Tasking (Read_Locks).Include (Entity (Prefix (Name (N))));
               end if;

            when N_In | N_Not_In =>
               --  Membership tests involving type with predicates have the
               --  predicate function appear during GG, but not in phase 2.
               --  See mirroring code in Get_Variable_Set that deals with
               --  this as well.
               if Present (Right_Opnd (N)) then
                  --  x in t
                  P := Right_Opnd (N);
                  if Nkind (P) = N_Identifier
                    and then Ekind (Entity (P)) in Type_Kind
                  then
                     Process_Type (Get_Type (P, Scope));
                  end if;
               else
                  --  x in t | 1 .. y | u
                  P := First (Alternatives (N));
                  while Present (P) loop
                     if Nkind (P) = N_Identifier
                       and then Ekind (Entity (P)) in Type_Kind
                     then
                        Process_Type (Get_Type (P, Scope));
                     end if;
                     Next (P);
                  end loop;
               end if;

            when others =>
               null;
         end case;

         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);
      --  AST traversal procedure
   begin
      Functions_Called := Node_Sets.Empty_Set;
      Traverse (N);
   end Collect_Functions_And_Read_Locked_POs;

   --------------------
   -- Component_Hash --
   --------------------

   function Component_Hash (E : Entity_Id) return Ada.Containers.Hash_Type is
   begin
      return Component_Graphs.Cluster_Hash
        (Comp_Graph.Get_Cluster (Comp_Graph.Get_Vertex (E)));
   end Component_Hash;

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
      Tmp : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      Ptr : Elmt_Id;
   begin
      case F.Kind is
         when Direct_Mapping =>
            if Ekind (Get_Direct_Mapping_Id (F)) = E_Abstract_State then
               Ptr := First_Elmt (Refinement_Constituents
                                  (Get_Direct_Mapping_Id (F)));
               while Present (Ptr) loop

                  --  We simply ignore the null refinement, it is
                  --  treated as if it was not present.

                  if Nkind (Node (Ptr)) /= N_Null then
                     Tmp.Union
                       (Expand_Abstract_State (Direct_Mapping_Id (Node (Ptr),
                        F.Variant), Erase_Constants));
                  end if;
                  Ptr := Next_Elmt (Ptr);
               end loop;

               Ptr := First_Elmt (Part_Of_Constituents
                                  (Get_Direct_Mapping_Id (F)));
               while Present (Ptr) loop

                  --  Part_of cannot include a null refinement.

                  Tmp.Union
                    (Expand_Abstract_State (Direct_Mapping_Id (Node (Ptr),
                     F.Variant), Erase_Constants));
                  Ptr := Next_Elmt (Ptr);
               end loop;

               if Tmp.Is_Empty then

                  --  If we can't refine this state (maybe the body
                  --  is not in SPARK, or simply not implemented or
                  --  there is a null refinement) then we use the
                  --  abstract state itself.

                  Tmp.Insert (F);
               end if;

               --  Entities translated as constants in Why3 should not be
               --  considered as effects for proof. This includes in particular
               --  formal parameters of mode IN.

            elsif Erase_Constants
              and then not
                Gnat2Why.Util.Is_Mutable_In_Why (Get_Direct_Mapping_Id (F))
            then
               null;

               --  Otherwise the effect is significant for proof, keep it

            else
               Tmp.Insert (F);
            end if;

         when Magic_String =>
            Tmp.Insert (F);

         when Record_Field | Null_Value | Synthetic_Null_Export =>
            raise Program_Error;
      end case;
      return Tmp;
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

   --------------------------
   -- Filter_Out_Constants --
   --------------------------

   function Filter_Out_Constants
     (S : Flow_Id_Sets.Set;
      C : Node_Sets.Set)
      return Flow_Id_Sets.Set
   is
   begin
      return R : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set do
         for F of S loop
            case F.Kind is
               when Direct_Mapping | Record_Field =>
                  declare
                     E : constant Entity_Id := Get_Direct_Mapping_Id (F);
                     pragma Assert (Nkind (E) in N_Entity);
                  begin
                     if Ekind (E) /= E_Constant
                       or else C.Contains (E)
                       or else Has_Variable_Input (F)
                     then
                        R.Include (F);
                     end if;
                  end;

               when Magic_String =>
                  if not Is_Constant (F.Name) then
                     R.Include (F);
                  end if;

               when Synthetic_Null_Export =>
                  R.Include (F);

               when Null_Value =>
                  raise Program_Error;
            end case;
         end loop;
      end return;
   end Filter_Out_Constants;

   ----------------------
   -- Flatten_Variable --
   ----------------------

   function Flatten_Variable
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Flow_Id_Sets.Set
   is
      T                    : Entity_Id;
      Ids                  : Flow_Id_Sets.Set;
      Classwide            : Boolean;

      Contains_Non_Visible : Boolean       := False;
      Root_Components      : Node_Sets.Set := Node_Sets.Empty_Set;

      subtype Private_Nonrecord_Kind is Private_Kind with
        Static_Predicate =>
          Private_Nonrecord_Kind not in E_Record_Type_With_Private |
                                        E_Record_Subtype_With_Private;
      --  Kind of non-record private types

      function Get_Root_Component (N : Node_Id) return Node_Id;
      --  Returns N's equilavent component of the root type. If this
      --  is not available then N's Original_Record_Component is
      --  returned instead.
      --  @param N is the component who's equivalent we are looking for
      --  @return the equivalent component of the root type if one exists
      --    or the Original_Record_Component of N otherwise.

      ------------------------
      -- Get_Root_Component --
      ------------------------

      function Get_Root_Component (N : Node_Id) return Node_Id is
         ORC : constant Node_Id := Original_Record_Component (N);
      begin
         --  Nothing to compare against. We fall back to N's
         --  Original_Record_Component.
         if Root_Components.Is_Empty then
            return ORC;
         end if;

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

   begin
      if Debug_Trace_Flatten then
         Write_Str ("Flatten: ");
         Print_Flow_Id (F);
         Indent;
      end if;

      if F.Kind not in Direct_Mapping | Record_Field
        or else F.Facet /= Normal_Part
      then
         if Debug_Trace_Flatten then
            Outdent;
         end if;
         return Flow_Id_Sets.To_Set (F);
      end if;

      pragma Assert (Nkind (Get_Direct_Mapping_Id (F)) in N_Entity);
      T         := Get_Type (F, Scope);
      Classwide := Ekind (T) in Class_Wide_Kind;
      while Ekind (T) in Class_Wide_Kind loop
         T := Get_Type (Etype (T), Scope);
      end loop;

      if Debug_Trace_Flatten then
         Write_Str ("Branching on type: ");
         Sprint_Node_Inline (T);
         Write_Line (" (" & Ekind (T)'Img & ")");
      end if;

      --  If we are dealing with a derived type then we want to get to
      --  the root and then Populate the Root_Components set. However,
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

            for Comp of All_Components (Root) loop
               Root_Components.Include (Original_Record_Component (Comp));
            end loop;
         end;
      end if;

      case Ekind (T) is
         when Private_Nonrecord_Kind =>
            if Debug_Trace_Flatten then
               Write_Line ("processing private type");
            end if;

            if Has_Discriminants (T) then
               for Ptr of All_Components (T) loop
                  if Is_Visible (Get_Root_Component (Ptr), Scope) then
                     Ids.Include (Add_Component (F, Ptr));
                  else
                     Contains_Non_Visible := True;
                  end if;
               end loop;
               Ids.Include (F'Update (Facet => Private_Part));
            else
               Ids := Flow_Id_Sets.To_Set (F);
            end if;

         when Record_Kind | Protected_Kind | Task_Kind =>
            if Debug_Trace_Flatten then
               case Ekind (T) is
                  when Record_Kind    =>
                     Write_Line ("processing record type");
                  when Protected_Kind =>
                     Write_Line ("processing protected type");
                  when Task_Kind      =>
                     Write_Line ("processing task type");
                  when others         =>
                     raise Why.Unexpected_Node;
               end case;
            end if;

            Ids := Flow_Id_Sets.Empty_Set;

            if Ekind (T) in Concurrent_Kind then
               if Nested_Inside_Concurrent_Object (T, Scope) then
                  --  Include constituents that belong to the concurrent object
                  --  due to a Part_Of.
                  if Present (Anonymous_Object (T)) then
                     declare
                        AO  : constant Node_Id := Anonymous_Object (T);
                        Ptr : Elmt_Id :=
                          First_Elmt (Part_Of_Constituents (AO));
                     begin
                        while Present (Ptr) loop
                           Ids.Union
                             (Flatten_Variable (Direct_Mapping_Id (Node (Ptr)),
                                                Scope));
                           Ptr := Next_Elmt (Ptr);
                        end loop;
                     end;
                  end if;
               else
                  --  From outside a concurrent object, all that we see is the
                  --  object itself.
                  return Flow_Id_Sets.To_Set (F);
               end if;
            end if;

            --  Include classwide types and privates with discriminants

            for Ptr of All_Components (T) loop
               if Is_Visible (Get_Root_Component (Ptr), Scope) then
                  if Ekind (T) in Concurrent_Kind then
                     Ids.Union (Flatten_Variable (Direct_Mapping_Id (Ptr),
                                                  Scope));
                  else
                     Ids.Union (Flatten_Variable (Add_Component (F, Ptr),
                                                  Scope));
                  end if;
               else
                  Contains_Non_Visible := True;
               end if;
            end loop;

            if Ekind (T) in Private_Kind or Contains_Non_Visible then
               --  We must have some discriminant, so return X'Private_Part
               --  and the discriminants. For simple private types we don't
               --  do this split.
               pragma Assert (Contains_Non_Visible);
               if Ids.Is_Empty then
                  Ids := Flow_Id_Sets.To_Set (F);
               else
                  Ids.Include (F'Update (Facet => Private_Part));
               end if;
            end if;

            --  For concurrent types we need to make sure that we never return
            --  an empty set. Instead return a singleton set with the type
            --  itself.
            if Ekind (T) in Concurrent_Kind
              and then Ids.Is_Empty
            then
               Ids.Include (F);
            end if;

            if Classwide then
               --  Ids.Include (F'Update (Facet => The_Tag));
               Ids.Include (F'Update (Facet => Extension_Part));
            end if;

         when others =>
            if Debug_Trace_Flatten then
               Write_Line ("processing misc type");
            end if;

            Ids := Flow_Id_Sets.To_Set (F);
      end case;

      if Debug_Trace_Flatten then
         Outdent;
      end if;

      return Ids;
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

      --  First we turn the tree into a more useful sequence. We also
      --  determine the root node which should be an entire variable.

      Seq := Node_Lists.Empty_List;
      while Nkind (Root_Node) in Interesting_Nodes loop
         Seq.Prepend (Root_Node);
         case Nkind (Root_Node) is
            when N_Type_Conversion | N_Unchecked_Type_Conversion =>
               Root_Node := Expression (Root_Node);

            when others =>
               Root_Node := Prefix (Root_Node);
         end case;
      end loop;
      pragma Assert (Nkind (Root_Node) in N_Identifier | N_Expanded_Name);

      Partial_Definition := False;
      View_Conversion    := False;
      Classwide          := False;
      Map_Root           := Direct_Mapping_Id (Unique_Entity
                                                 (Entity (Root_Node)));

      --  We now work out which variable (or group of variables) is
      --  actually defined, by following the selected components. If we
      --  find an array slice or index we stop and note that we are dealing
      --  with a partial assignment (the defined variable is implicitly
      --  used).

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
      Use_Computed_Globals : Boolean := True)
   is
      pragma Unreferenced (Classwide);
      --  For now we assume classwide globals are the same as the actual
      --  globals.

      Tmp           : Dependency_Maps.Map;

      Depends_N     : constant Node_Id := Get_Contract_Node (Subprogram,
                                                             Scope,
                                                             Depends_Contract);

      All_Proof_Ins : Flow_Id_Sets.Set;
      All_Reads     : Flow_Id_Sets.Set;
      All_Writes    : Flow_Id_Sets.Set;

      F             : Flow_Id;

      function Trimming_Required return Boolean;
      --  Checks if the projected Depends constituents need to be
      --  trimmed (based on a user-provided Refined_Global aspect).

      -----------------------
      -- Trimming_Required --
      -----------------------

      function Trimming_Required return Boolean is
      begin
         if Pragma_Name (Depends_N) = Name_Refined_Depends
           or else not Mentions_State_With_Visible_Refinement (Depends_N,
                                                               Scope)
         then
            --  No trimming required if:
            --
            --    a) there is a user-provided Refined_Depends
            --
            --    b) the Depends aspect does not mention state with visible
            --       refinement
            return False;
         end if;

         return True;
      end Trimming_Required;

   begin

      ----------------------------------------------------------------------
      --  Step 1: Parse the appropriate dependency relation.
      ----------------------------------------------------------------------

      Tmp := Parse_Depends (Depends_N);

      ----------------------------------------------------------------------
      --  Step 2: Expand out any abstract state for which the refinement is
      --  visible, similar to what we do for globals. During this step we
      --  also trim the generated refined depends according to the
      --  user-provided Refined_Global contract.
      ----------------------------------------------------------------------

      --  Initializing Depends map
      Depends := Dependency_Maps.Empty_Map;

      if Trimming_Required then
         --  Use the Refined_Global to trim the down projected Depends

         --  Collecting all global Proof_Ins, Outputs and Inputs
         Get_Globals (Subprogram           => Subprogram,
                      Scope                => Scope,
                      Classwide            => False,
                      Proof_Ins            => All_Proof_Ins,
                      Reads                => All_Reads,
                      Writes               => All_Writes,
                      Use_Computed_Globals => Use_Computed_Globals);

         --  Add formal parameters so that we have the complete set of
         --  Proof_Ins, Reads and Writes.
         for Param of Get_Formals (Subprogram) loop
            case Ekind (Param) is
               when E_In_Parameter     =>
                  F := Direct_Mapping_Id (Param);
                  All_Reads.Insert (F);
                  All_Proof_Ins.Insert (F);

               when E_In_Out_Parameter =>
                  F := Direct_Mapping_Id (Param);
                  All_Proof_Ins.Insert (F);
                  All_Reads.Insert (F);
                  All_Writes.Insert (F);

               when E_Out_Parameter    =>
                  F := Direct_Mapping_Id (Param);
                  All_Writes.Insert (F);

               when others             =>
                  F := Concurrent_Object_Id (Param);
                  All_Reads.Insert (F);
                  All_Proof_Ins.Insert (F);
                  if Ekind (Subprogram) not in E_Function         |
                                               E_Generic_Function
                  then
                     All_Writes.Insert (F);
                  end if;
            end case;
         end loop;

         --  If Subprogram is a function then we need to add it to the
         --  All_Writes set so that Subprogram'Result can appear on the LHS of
         --  the Refined_Depends.
         if Ekind (Subprogram) in E_Function | E_Generic_Function then
            All_Writes.Insert (Direct_Mapping_Id (Subprogram));
         end if;

         --  Change all variants to Normal_Use
         All_Proof_Ins := Change_Variant (All_Proof_Ins, Normal_Use);
         All_Reads     := Change_Variant (All_Reads, Normal_Use);
         All_Writes    := Change_Variant (All_Writes, Normal_Use);

         for C in Tmp.Iterate loop
            declare
               D_Out : constant Flow_Id_Sets.Set :=
                 (if Present (Dependency_Maps.Key (C)) then
                     To_Flow_Id_Set (Down_Project
                                       (Node_Sets.To_Set
                                          (Get_Direct_Mapping_Id
                                             (Dependency_Maps.Key (C))),
                                        Scope))
                  else
                     Flow_Id_Sets.To_Set (Dependency_Maps.Key (C)));

               D_In  : Flow_Id_Sets.Set :=
                 To_Flow_Id_Set (Down_Project
                                   (To_Node_Set
                                      (Dependency_Maps.Element (C)),
                                    Scope));
            begin
               for O of D_Out loop
                  if All_Writes.Contains (O) then
                     if O = Null_Flow_Id then
                        D_In := D_In and All_Proof_Ins;
                     else
                        D_In := D_In and All_Reads;
                     end if;
                     Depends.Include (O, D_In);
                  end if;
               end loop;
            end;
         end loop;

      else
         --  Simply add the dependencies as they are
         for C in Tmp.Iterate loop
            declare
               D_Out : constant Flow_Id_Sets.Set :=
                 (if Present (Dependency_Maps.Key (C)) then
                     To_Flow_Id_Set (Down_Project
                                       (Node_Sets.To_Set
                                          (Get_Direct_Mapping_Id
                                             (Dependency_Maps.Key (C))),
                                        Scope))
                  else
                     Flow_Id_Sets.To_Set (Dependency_Maps.Key (C)));

               D_In  : constant Flow_Id_Sets.Set :=
                 To_Flow_Id_Set (Down_Project
                                   (To_Node_Set
                                      (Dependency_Maps.Element (C)),
                                    Scope));
            begin
               for O of D_Out loop
                  Depends.Include (O, D_In);
               end loop;
            end;
         end loop;
      end if;

      ----------------------------------------------------------------------
      --  Step 3: We add all Proof_Ins of the [Refined_]Global contract to
      --  the RHS of the "null => RHS" dependence. This is an implicit
      --  dependency.
      ----------------------------------------------------------------------

      Get_Globals (Subprogram           => Subprogram,
                   Scope                => Scope,
                   Classwide            => False,
                   Proof_Ins            => All_Proof_Ins,
                   Reads                => All_Reads,
                   Writes               => All_Writes,
                   Use_Computed_Globals => Use_Computed_Globals,
                   Ignore_Depends       => True);

      --  Change variant of All_Proof_Ins to Normal_Use
      All_Proof_Ins := Change_Variant (All_Proof_Ins, Normal_Use);

      if Depends.Contains (Null_Flow_Id) then
         --  Add All_Proof_Ins to the existing RHS of the "null => RHS"
         --  dependency.
         for P_In of All_Proof_Ins loop
            Depends (Null_Flow_Id).Include (P_In);
         end loop;
      else
         --  Create new dependency where "null => All_Proof_Ins"
         Depends.Insert (Null_Flow_Id, All_Proof_Ins);
      end if;

   end Get_Depends;

   -----------------
   -- Get_Flow_Id --
   -----------------

   function Get_Flow_Id
     (Name  : Entity_Name;
      View  : Flow_Id_Variant := Normal_Use;
      Scope : Flow_Scope      := Null_Flow_Scope)
      return Flow_Id
   is
      E : constant Entity_Id := Find_Entity (Name);
   begin
      if Present (E) then
         if Ekind (E) in Type_Kind | E_Constant
           and then Present (Full_View (E))
           and then (Scope = Null_Flow_Scope
                       or else Is_Visible (Full_View (E), Scope))
         then
            return Direct_Mapping_Id (Full_View (E), View);
         else
            return Direct_Mapping_Id (E, View);
         end if;
      end if;

      --  If none can be found, we fall back to the magic
      --  string.
      return Magic_String_Id (Name, View);
   end Get_Flow_Id;

   ----------------------
   -- Get_Function_Set --
   ----------------------

   function Get_Function_Set (N                  : Node_Id;
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
         Include_Predicates => Include_Predicates);
      return Funcs;
   end Get_Function_Set;

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
                          Use_Computed_Globals   : Boolean := True;
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
         if Debug_Trace_Get_Global then
            Indent;
            Write_Line ("using user annotation");
            Outdent;
         end if;

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
                               The_Global : Entity_Id);
            --  Add the given global to the reads, writes or proof_in
            --  list, depending on the mode.

            -------------
            -- Process --
            -------------

            procedure Process (The_Mode   : Name_Id;
                               The_Global : Entity_Id)
            is
               Non_Limited_Global : constant Entity_Id :=
                 (if Ekind (The_Global) = E_Abstract_State
                    and then Present (Non_Limited_View (The_Global))
                  then Non_Limited_View (The_Global)
                  else The_Global);
               --  If a Non_Limited_View exists, then use that. In
               --  doing so we avoid generating two Flow_Ids for a
               --  single variable.
            begin
               case The_Mode is
                  when Name_Input =>
                     G_In.Insert (Non_Limited_Global);
                  when Name_In_Out =>
                     G_In.Insert (Non_Limited_Global);
                     G_Out.Insert (Non_Limited_Global);

                  when Name_Output =>
                     if Consider_Discriminants and then
                       Contains_Discriminants
                       (Direct_Mapping_Id (Non_Limited_Global, In_View),
                        Scope)
                     then
                        G_In.Insert (Non_Limited_Global);
                     end if;
                     G_Out.Insert (Non_Limited_Global);

                  when Name_Proof_In =>
                     G_Proof.Insert (Non_Limited_Global);
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

            elsif Nkind (Expression (PAA)) in
              N_Identifier | N_Expanded_Name
            then
               --  global => foo
               --  A single input
               Process (Name_Input, Entity (Expression (PAA)));

            elsif Nkind (Expression (PAA)) = N_Aggregate and then
              Expressions (Expression (PAA)) /= No_List
            then
               --  global => (foo, bar)
               --  Inputs
               RHS := First (Expressions (Expression (PAA)));
               while Present (RHS) loop
                  case Nkind (RHS) is
                     when N_Identifier | N_Expanded_Name =>
                        Process (Name_Input, Entity (RHS));
                     when N_Numeric_Or_String_Literal =>
                        --  We should only ever get here if we are
                        --  dealing with a rewritten constant.
                        pragma Assert (Present (Original_Node (RHS)));

                        --  We process the entity of the Original_Node instead
                        Process (Name_Input, Entity (Original_Node (RHS)));

                     when others =>
                        raise Why.Unexpected_Node;
                  end case;
                  RHS := Next (RHS);
               end loop;

            elsif Nkind (Expression (PAA)) = N_Aggregate and then
              Component_Associations (Expression (PAA)) /= No_List
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
                              Process (The_Mode, Entity (RHS));
                              RHS := Next (RHS);
                           end loop;
                        when N_Identifier | N_Expanded_Name =>
                           Process (The_Mode, Entity (RHS));
                        when N_Null =>
                           null;
                        when N_Numeric_Or_String_Literal =>
                           --  We should only ever get here if we are
                           --  dealing with a rewritten constant.
                           pragma Assert (Present (Original_Node (RHS)));

                           --  We process the entity of the
                           --  Original_Node instead.
                           Process (The_Mode, Entity (Original_Node (RHS)));

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

            declare

               function Trimming_Required return Boolean;
               --  Checks if the projected Global constituents need to be
               --  trimmed (based on a user-provided Refined_Depends aspect).

               -----------------------
               -- Trimming_Required --
               -----------------------

               function Trimming_Required return Boolean is
               begin
                  if Ignore_Depends
                    or else No (Depends_Node)
                    or else Pragma_Name (Global_Node) = Name_Refined_Global
                    or else Pragma_Name (Depends_Node) /= Name_Refined_Depends
                    or else not Mentions_State_With_Visible_Refinement
                                  (Global_Node,
                                   Scope)
                  then
                     --  No trimming required if there is:
                     --
                     --    a) no user-provided Depends contract
                     --
                     --    b) a user-provided Refined_Global
                     --
                     --    c) no user-provided Refined_Depends
                     --
                     --    d) the Global aspect does not mention state with
                     --       visible refinement
                     return False;
                  end if;

                  return True;
               end Trimming_Required;

               D_Map        : Dependency_Maps.Map;
               All_Inputs_F : Flow_Id_Sets.Set     := Flow_Id_Sets.Empty_Set;
               All_Inputs_N : Node_Sets.Set        := Node_Sets.Empty_Set;

            begin
               if Trimming_Required then
                  --  Read the Refined_Depends aspect
                  Get_Depends (Subprogram           => Subprogram,
                               Scope                => Scope,
                               Classwide            => Classwide,
                               Depends              => D_Map,
                               Use_Computed_Globals => Use_Computed_Globals);

                  --  Gather all inputs
                  for C in D_Map.Iterate loop
                     All_Inputs_F := All_Inputs_F or
                                       Dependency_Maps.Element (C);
                  end loop;

                  --  Convert set of Flow_Ids to a set of Node_Ids
                  for F of All_Inputs_F loop
                     All_Inputs_N.Include (Get_Direct_Mapping_Id (F));
                  end loop;

                  --  Do the trimming
                  G_In := G_In and All_Inputs_N;
               end if;
            end;

            ---------------------------------------------------------------
            --  Step 5: Convert to a Flow_Id set.
            ---------------------------------------------------------------

            for V of G_Proof loop
               Proof_Ins.Include (Direct_Mapping_Id (V, In_View));
            end loop;
            for V of G_In loop
               Reads.Include (Direct_Mapping_Id (V, In_View));
            end loop;
            for V of G_Out loop
               Writes.Include (Direct_Mapping_Id (V, Out_View));
            end loop;

            if Debug_Trace_Get_Global then
               Indent;
               Write_Line ("proof ins");
               Indent;
               for F of Proof_Ins loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;

               Write_Line ("reads");
               Indent;
               for F of Reads loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;

               Write_Line ("writes");
               Indent;
               for F of Writes loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;
               Outdent;
            end if;
         end;

      elsif Present (Depends_Node)
        and then not Use_Generated_Globals
        and then not Ignore_Depends
      then

         --  If we have no global, but we do have a depends, we can
         --  reverse-engineer the global. This also solves the issue where
         --  the (computed) global is inconsistent with the depends. (See
         --  M807-032 for an example.)

         if Debug_Trace_Get_Global then
            Indent;
            Write_Line ("reversing depends annotation");
            Outdent;
         end if;

         declare
            D_Map  : Dependency_Maps.Map;
            Params : Node_Sets.Set;
         begin
            Get_Depends (Subprogram           => Subprogram,
                         Scope                => Scope,
                         Classwide            => Classwide,
                         Depends              => D_Map,
                         Use_Computed_Globals => Use_Computed_Globals);

            --  We need to make sure not to include our own parameters in the
            --  globals we produce here. Note that the formal parameters that
            --  we collect here will also include implicit formal parameters of
            --  subprograms that belong to concurrent types.
            Params.Union (Get_Formals (Subprogram));

            --  Always OK to call direct_mapping here since you can't refer
            --  to hidden state in user-written depends contracts.

            for C in D_Map.Iterate loop
               declare
                  E      : Entity_Id;
                  Output : constant Flow_Id := Dependency_Maps.Key (C);
                  Inputs : constant Flow_Id_Sets.Set :=
                    Dependency_Maps.Element (C);
               begin
                  E := (if Present (Output)
                        then Get_Direct_Mapping_Id (Output)
                        else Empty);

                  if Present (E)
                    and then E /= Subprogram
                    and then not Params.Contains (E)
                  then
                     --  Note we also filter out the function'result
                     --  construct here.
                     Writes.Include (Change_Variant (Output, Out_View));
                  end if;

                  for R of Inputs loop
                     E := (if Present (R)
                           then Get_Direct_Mapping_Id (R)
                           else Empty);

                     if Present (E) and then not Params.Contains (E) then
                        Reads.Include (Change_Variant (R, In_View));

                        if Has_Effective_Reads (R) then
                           --  A volatile with effective reads is always an
                           --  output as well (this should be recorded in
                           --  the depends, but the front-end does not
                           --  enforce this).
                           Writes.Include (Change_Variant (R, Out_View));
                        end if;
                     end if;
                  end loop;
               end;
            end loop;

            if Debug_Trace_Get_Global then
               Indent;
               Write_Line ("reads");
               Indent;
               for F of Reads loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;

               Write_Line ("writes");
               Indent;
               for F of Writes loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;
               Outdent;
            end if;
         end;

      elsif Use_Computed_Globals and then GG_Exist (Subprogram) then
         --  We don't have a global or a depends aspect so we look at
         --  the generated globals.

         if Debug_Trace_Get_Global then
            Indent;
            Write_Line ("using pavlos globals");
            Outdent;
         end if;

         GG_Get_Globals (Subprogram,
                         Scope,
                         Proof_Ins,
                         Reads,
                         Writes);

         if Debug_Trace_Get_Global then
            Indent;
            Write_Line ("proof ins");
            Indent;
            for PI of Proof_Ins loop
               Sprint_Flow_Id (PI);
               Write_Eol;
            end loop;
            Outdent;

            Write_Line ("reads");
            Indent;
            for R of Reads loop
               Sprint_Flow_Id (R);
               Write_Eol;
            end loop;
            Outdent;

            Write_Line ("writes");
            Indent;
            for W of Writes loop
               Sprint_Flow_Id (W);
               Write_Eol;
            end loop;
            Outdent;
            Outdent;
         end if;

      elsif Use_Computed_Globals then
         --  We don't have a global or a depends aspect and we don't
         --  have generated globals, so we should look at the computed
         --  globals...

         if Debug_Trace_Get_Global then
            Indent;
            Write_Line ("using yannick globals");
            Outdent;
         end if;

         declare
            ALI_Reads  : constant Name_Sets.Set :=
              Get_Generated_Reads (Subprogram,
                                   Include_Constants => True);
            ALI_Writes : constant Name_Sets.Set :=
              Get_Generated_Writes (Subprogram);

            F : Flow_Id;
         begin

            --  We process the reads
            if Debug_Trace_Get_Global then
               Indent;
               Write_Line ("reads");
               Indent;
            end if;

            for R of ALI_Reads loop
               F := Get_Flow_Id (R, In_View, Scope);

               if Debug_Trace_Get_Global then
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end if;

               if Is_Variable (F) then
                  Reads.Include (F);
               end if;
            end loop;

            if Debug_Trace_Get_Global then
               Outdent;
               Write_Line ("writes");
               Indent;
            end if;

            for W of ALI_Writes loop
               --  This is not a mistake, we must assume that all
               --  values written may also not change or that they are
               --  only partially updated.
               --
               --  This also takes care of discriminants as every out
               --  is really an in out.
               F := Get_Flow_Id (W, Out_View, Scope);

               if Debug_Trace_Get_Global then
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end if;

               Reads.Include (Change_Variant (F, In_View));
               Writes.Include (F);
            end loop;

            if Debug_Trace_Get_Global then
               Outdent;
               Outdent;
            end if;
         end;

      else
         --  We don't have user globals and we're not allowed to use
         --  computed globals (i.e. we're trying to compute globals).

         if Debug_Trace_Get_Global then
            Indent;
            Write_Line ("defaulting to null globals");
            Outdent;
         end if;

      end if;
   end Get_Globals;

   ---------------------
   -- Get_Loop_Writes --
   ---------------------

   function Get_Loop_Writes (E : Entity_Id) return Flow_Id_Sets.Set is
   begin
      return Loop_Info (E);
   end Get_Loop_Writes;

   ---------------------------
   -- Get_Part_Of_Variables --
   ---------------------------

   function Get_Part_Of_Variables (E : Entity_Id) return Node_Sets.Set is
      S : Node_Sets.Set := Node_Sets.Empty_Set;

      --  to get the right flow scope, we compute some node inside the
      --  protected object

      Inner : constant Node_Id :=
        First (Visible_Declarations_of_Prot_Type (E));
   begin

      --  A hack, but a correct one. Arguably, a protected object without any
      --  visible declarations might still have part_of variables. But we can
      --  ignore them in proof, because no-one can read nor write them (as this
      --  object doesn't have any subprograms).

      if No (Inner) then
         return S;
      end if;

      declare
         Parts : constant Flow_Id_Sets.Set :=
           Flatten_Variable (E, Get_Flow_Scope (Inner));
      begin
         for Fid of Parts loop
            declare
               Ent : constant Entity_Id :=
                 (if Fid.Kind in Direct_Mapping | Record_Field then Fid.Node
                  else Empty);
            begin
               if Present (Ent)
                 and then Is_Part_Of_Concurrent_Object (Ent)
               then
                  S.Include (Ent);
               end if;
            end;
         end loop;
      end;
      return S;
   end Get_Part_Of_Variables;

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
         when Subprogram_Kind | E_Entry =>
            if Refined then
               P_Expr := Find_Contracts (E, Name_Refined_Post);
            else
               P_Expr := Find_Contracts (E, Name_Postcondition);
               P_CC   := Find_Contracts (E, Name_Contract_Cases);

               --  If a Contract_Cases aspect was found then we pull out
               --  every right-hand-side.
               if not P_CC.Is_Empty then
                  declare
                     Ptr : Node_Id;
                  begin
                     Ptr := First (Component_Associations
                                     (P_CC.First_Element));
                     while Present (Ptr) loop
                        P_Expr.Append (Expression (Ptr));
                        Ptr := Next (Ptr);
                     end loop;
                  end;
               end if;
            end if;

         when E_Package =>
            if Refined then
               P_Expr := Node_Lists.Empty_List;
            else
               P_Expr := Find_Contracts (E, Name_Initial_Condition);
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
        Find_Contracts (E, Name_Precondition);
      Contract_Case            : constant Node_Lists.List :=
        Find_Contracts (E, Name_Contract_Cases);
   begin
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

   procedure Get_Proof_Globals (Subprogram           : Entity_Id;
                                Classwide            : Boolean;
                                Reads                : out Flow_Id_Sets.Set;
                                Writes               : out Flow_Id_Sets.Set;
                                Use_Computed_Globals : Boolean := True;
                                Keep_Constants       : Boolean := False)
   is
      Proof_Ins : Flow_Id_Sets.Set;
      Tmp_In    : Flow_Id_Sets.Set;
      Tmp_Out   : Flow_Id_Sets.Set;
      Body_E    : constant Entity_Id  := Get_Body_Entity (Subprogram);
      S         : constant Flow_Scope := (if Present (Body_E) and then
                                            Entity_Body_In_SPARK (Subprogram)
                                          then Get_Flow_Scope (Body_E)
                                          else Get_Flow_Scope (Subprogram));
   begin
      Get_Globals
        (Subprogram             => Subprogram,
         Scope                  => S,
         Classwide              => Classwide,
         Proof_Ins              => Proof_Ins,
         Reads                  => Tmp_In,
         Writes                 => Tmp_Out,
         Consider_Discriminants => False,
         Use_Computed_Globals   => Use_Computed_Globals);

      --  Merge the proof ins with the reads.
      Tmp_In.Union (Proof_Ins);

      --  Expand all variables.
      Reads := Flow_Id_Sets.Empty_Set;
      for F of Tmp_In loop
         Reads.Union (Expand_Abstract_State (F, not Keep_Constants));
      end loop;

      Writes := Flow_Id_Sets.Empty_Set;
      for F of Tmp_Out loop
         Writes.Union (Expand_Abstract_State (F, not Keep_Constants));
      end loop;
   end Get_Proof_Globals;

   --------------
   -- Get_Type --
   --------------

   function Get_Type
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Entity_Id
   is
      E : Entity_Id;
   begin
      case F.Kind is
         when Direct_Mapping =>
            E := Get_Direct_Mapping_Id (F);
         when Record_Field =>
            E := F.Component.Last_Element;
         when others =>
            raise Program_Error;
      end case;
      return Get_Type (E, Scope);
   end Get_Type;

   function Get_Type
     (N     : Node_Id;
      Scope : Flow_Scope)
      return Entity_Id
   is
      --  T will be assigned the type of N
      T : Entity_Id :=

        (if Nkind (N) in N_Entity
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
   begin
      --  When dealing with a state abstraction just return T
      if Nkind (N) in N_Entity and then Ekind (N) = E_Abstract_State then
         return T;
      end if;

      while Is_Type (T)
        and then Present (Full_View (T))
        and then Is_Visible (Full_View (T), Scope)
        and then Full_View (T) /= T
      loop
         T := Full_View (T);
      end loop;

      --  We do not want to return an Itype so we recurse on T's Etype
      --  if it different to T. If we cannot do any better then we
      --  will in fact return an Itype.
      if Is_Itype (T)
        and then not Is_Nouveau_Type (T)
      then
         T := Get_Type (Etype (T), Scope);
      end if;

      return T;
   end Get_Type;

   --------------------------
   -- Get_Implicit_Formals --
   --------------------------

   function Get_Implicit_Formals
     (E        : Entity_Id;
      Callsite : Node_Id := Empty;
      Entire   : Boolean := True)
      return Node_Sets.Set
   is
      F      : constant Flow_Id := Direct_Mapping_Id (E);
      Params : Node_Sets.Set    := Node_Sets.Empty_Set;
   begin
      case Ekind (E) is
         when E_Entry | Subprogram_Kind =>
            --  If E is directly enclosed in a protected object then add the
            --  protected object as an implicit formal parameter of the
            --  entry/subprogram.
            if Belongs_To_Protected_Object (F) then
               Params.Insert (Get_Enclosing_Concurrent_Object (F,
                                                               Callsite,
                                                               Entire));
            end if;

         when E_Task_Type =>
            --  A task sees itself as a formal parameter.
            Params.Include ((if Present (Anonymous_Object (E))
                             then Anonymous_Object (E)
                             else E));

         when others =>
            raise Why.Unexpected_Node;

      end case;

      return Params;
   end Get_Implicit_Formals;

   -----------------
   -- Get_Formals --
   -----------------

   function Get_Formals
     (E        : Entity_Id;
      Callsite : Node_Id := Empty;
      Entire   : Boolean := True)
      return Node_Sets.Set
   is
      Param  : Entity_Id;
      Params : Node_Sets.Set := Get_Implicit_Formals (E, Callsite, Entire);
   begin
      case Ekind (E) is
         when E_Entry | Subprogram_Kind =>
            --  Collect explicit formal parameters
            Param := First_Formal (E);
            while Present (Param) loop
               Params.Insert (Param);
               Param := Next_Formal (Param);
            end loop;

         when E_Task_Type =>
            --  Add discriminants of task as formal parameters.
            if Has_Discriminants (E)
              or else Has_Unknown_Discriminants (E)
            then
               Param :=  First_Discriminant (E);
               while Present (Param) loop
                  Params.Include (Param);
                  Param := Next_Discriminant (Param);
               end loop;
            end if;

         when others =>
            raise Why.Unexpected_Node;

      end case;

      return Params;
   end Get_Formals;

   ----------------------
   -- Get_Variable_Set --
   ----------------------

   function Get_Variable_Set
     (N                            : Node_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Allow_Statements             : Boolean := False;
      Expand_Synthesized_Constants : Boolean := False;
      Consider_Extensions          : Boolean := False)
      return Flow_Id_Sets.Set
   is
      VS         : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

      function Recurse_On (N                   : Node_Id;
                           Consider_Extensions : Boolean := False)
                           return Flow_Id_Sets.Set
      is (Get_Variable_Set
            (N,
             Scope                        => Scope,
             Local_Constants              => Local_Constants,
             Fold_Functions               => Fold_Functions,
             Use_Computed_Globals         => Use_Computed_Globals,
             Reduced                      => Reduced,
             Allow_Statements             => False,
             Expand_Synthesized_Constants => Expand_Synthesized_Constants,
             Consider_Extensions          => Consider_Extensions));
      --  Recurse on N. Please note that Allow_Statements is always false;
      --  this is intentional as we should only ever recurse on something
      --  inside expressions.

      function Process_Subprogram_Call
        (Callsite : Node_Id)
         return Flow_Id_Sets.Set
      with Pre => Nkind (Callsite) in N_Entry_Call_Statement |
                                      N_Subprogram_Call;
      --  Work out which variables (including globals) are used in the
      --  entry/function call and add them to the given set.

      function Proc (N : Node_Id) return Traverse_Result;
      --  Adds each identifier or defining_identifier found to VS, as
      --  long as we are dealing with:
      --     * a variable
      --     * a subprogram parameter
      --     * a loop parameter
      --     * a constant

      ---------------------------
      -- Process_Function_Call --
      ---------------------------

      function Process_Subprogram_Call
        (Callsite : Node_Id)
         return Flow_Id_Sets.Set
      is
         Subprogram    : constant Entity_Id := Get_Called_Entity (Callsite);

         Global_Reads  : Flow_Id_Sets.Set;
         Global_Writes : Flow_Id_Sets.Set;

         Folding       : constant Boolean :=
           Fold_Functions
           and then Ekind (Subprogram) = E_Function
           and then Has_Depends (Subprogram);

         Used_Reads    : Flow_Id_Sets.Set;

         V             : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      begin

         --  Determine the global effects of the called program

         declare
            Proof_Reads : Flow_Id_Sets.Set;
         begin
            Get_Globals (Subprogram           => Subprogram,
                         Scope                => Scope,
                         Classwide            =>
                           Is_Dispatching_Call (Callsite),
                         Proof_Ins            => Proof_Reads,
                         Reads                => Global_Reads,
                         Writes               => Global_Writes,
                         Use_Computed_Globals => Use_Computed_Globals);
            if not Fold_Functions then
               Global_Reads.Union (Proof_Reads);
            end if;
         end;

         --  If we are dealing with a subprogram that is declared inside a
         --  concurrent object then we also need to add the concurrent object.
         declare
            Subprogram_F : constant Flow_Id := Direct_Mapping_Id (Subprogram);
            The_CO       : Entity_Id;
         begin
            if Belongs_To_Concurrent_Object (Subprogram_F) then
               The_CO := Get_Enclosing_Concurrent_Object (Subprogram_F,
                                                          Callsite);
               V.Union (Flatten_Variable (The_CO, Scope));
            end if;
         end;

         --  If we fold functions we need to obtain the used inputs

         if Folding then
            declare
               Depends : Dependency_Maps.Map;
            begin
               Get_Depends (Subprogram           => Subprogram,
                            Scope                => Scope,
                            Classwide            =>
                              Is_Dispatching_Call (Callsite),
                            Depends              => Depends,
                            Use_Computed_Globals => Use_Computed_Globals);
               pragma Assert (Depends.Length in 1 .. 2);
               Used_Reads := Depends (Direct_Mapping_Id (Subprogram));
            end;
         end if;

         --  Apply sanity check for functions

         if Nkind (Callsite) = N_Function_Call and then
           Flow_Id_Sets.Length (Global_Writes) > 0
         then
            Error_Msg_NE
              (Msg => "side effects of function & are not modeled in SPARK",
               N   => Callsite,
               E   => Subprogram);
         end if;

         --  Merge globals into the variables used

         for G of Global_Reads loop
            if (if Folding
                then Used_Reads.Contains (Change_Variant (G, Normal_Use)))
            then
               V.Include (Change_Variant (G, Normal_Use));
               if Extensions_Visible (G, Scope) then
                  V.Include (Change_Variant (G, Normal_Use)'Update
                               (Facet => Extension_Part));
               end if;
            end if;
         end loop;
         for G of Global_Writes loop
            V.Include (Change_Variant (G, Normal_Use));
            if Extensions_Visible (G, Scope) then
               V.Include (Change_Variant (G, Normal_Use)'Update
                            (Facet => Extension_Part));
            end if;
         end loop;

         --  Merge the actuals into the set of variables used

         declare
            Actual : Node_Id;
            Formal : Entity_Id;
            Call   : Node_Id;
            Ptr    : Node_Id;
         begin
            Ptr := First (Parameter_Associations (Callsite));
            while Present (Ptr) loop
               case Nkind (Ptr) is
                  when N_Parameter_Association =>
                     Actual := Explicit_Actual_Parameter (Ptr);
                  when others =>
                     Actual := Ptr;
               end case;

               Find_Actual (N      => Actual,
                            Formal => Formal,
                            Call   => Call);
               pragma Assert (Call = Callsite);

               if (if Folding
                   then Used_Reads.Contains (Direct_Mapping_Id (Formal)))
               then
                  V.Union
                    (Recurse_On
                       (Actual,
                        Consider_Extensions =>
                          Has_Extensions_Visible (Subprogram) or else
                          Ekind (Get_Type (Formal, Scope))
                            in Class_Wide_Kind));
               end if;

               Next (Ptr);
            end loop;
         end;

         --  Finally, we expand the collected set (if necessary)

         return R : Flow_Id_Sets.Set do
            R := Flow_Id_Sets.Empty_Set;
            for Tmp of V loop
               if Reduced or Tmp.Kind = Record_Field then
                  R.Include (Tmp);
               else
                  R.Union (Flatten_Variable (Tmp, Scope));
               end if;
            end loop;
         end return;
      end Process_Subprogram_Call;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Procedure_Call_Statement =>
               if not Allow_Statements then
                  --  If we ever get one of these we have a problem -
                  --  Get_Variable_Set is only really meant to be
                  --  called on expressions and not statements.
                  raise Program_Error;

               else
                  VS.Union (Process_Subprogram_Call (N));
                  return Skip;
               end if;

            when N_Later_Decl_Item =>
               --  These should allow us to go through package specs
               --  and bodies.
               return Skip;

            when N_Function_Call =>
               VS.Union (Process_Subprogram_Call (N));
               return Skip;

            when N_Identifier | N_Expanded_Name =>
               if Present (Entity (N)) then
                  case Ekind (Entity (N)) is
                     when E_Constant =>
                        if Expand_Synthesized_Constants
                          and then not Comes_From_Source (Entity (N))
                        then
                           --  To expand synthesized constants, we need to find
                           --  the original expression and find the variable
                           --  set of that.
                           declare
                              Obj_Decl : constant Node_Id :=
                                Parent (Entity (N));
                              E        : constant Node_Id :=
                                Expression (Obj_Decl);
                           begin
                              pragma Assert
                                (Nkind (Obj_Decl) =
                                   N_Object_Declaration,
                                 "Bad parent of constant entity");
                              pragma Assert
                                (Present (E),
                                 "Constant has no expression");
                              VS.Union (Recurse_On (E));
                           end;

                        elsif Local_Constants.Contains (Entity (N))
                          or else Has_Variable_Input
                                    (Direct_Mapping_Id (Entity (N)))
                        then
                           --  If this constant:
                           --    * comes from source and is in Local_Constants
                           --    * or has variable input
                           --  then add it.
                           if Reduced then
                              VS.Include (Direct_Mapping_Id
                                            (Unique_Entity (Entity (N))));
                           else
                              VS.Union (Flatten_Variable (Entity (N), Scope));
                           end if;
                        end if;

                     when E_Variable         |
                          E_Component        |
                          E_Discriminant     |
                          E_Loop_Parameter   |
                          E_Out_Parameter    |
                          E_In_Parameter     |
                          E_In_Out_Parameter =>

                        declare
                           E : Entity_Id := Entity (N);
                        begin
                           if Ekind (E) = E_In_Parameter
                             and then Present (Discriminal_Link (E))
                           then
                              E := Discriminal_Link (E);
                           end if;

                           case Ekind (E) is
                              when E_Discriminant | E_Component =>
                                 if Ekind (Sinfo.Scope (E)) not in
                                   E_Protected_Type | E_Task_Type
                                 then
                                    --  We include stuff from tasks and
                                    --  POs, but otherwise we need to
                                    --  ignore discriminants and
                                    --  components.
                                    return OK;
                                 end if;
                              when others =>
                                 null;
                           end case;

                           if Reduced then
                              VS.Include (Direct_Mapping_Id
                                            (Unique_Entity (E)));
                           else
                              VS.Union (Flatten_Variable (E, Scope));
                           end if;
                           if Consider_Extensions
                             and then Extensions_Visible (E, Scope)
                           then
                              VS.Include (Direct_Mapping_Id
                                            (Unique_Entity (E),
                                             Facet => Extension_Part));
                           end if;
                        end;

                     when Discrete_Or_Fixed_Point_Kind =>
                        if Is_Constrained (Entity (N)) then
                           declare
                              E  : constant Entity_Id := Entity (N);
                              SR : constant Node_Id   := Scalar_Range (E);
                              LB : constant Node_Id   := Low_Bound (SR);
                              HB : constant Node_Id   := High_Bound (SR);
                           begin
                              VS.Union (Recurse_On (LB));
                              VS.Union (Recurse_On (HB));
                           end;
                        end if;

                     when others =>
                        null;
                  end case;
               end if;

            when N_Defining_Identifier =>
               case Ekind (N) is
                  when E_Constant         |
                       E_Variable         |
                       E_Component        |
                       E_Discriminant     |
                       E_Loop_Parameter   |
                       E_Out_Parameter    |
                       E_In_Parameter     |
                       E_In_Out_Parameter =>
                     declare
                        E : Entity_Id := N;
                     begin
                        if Ekind (E) in E_Constant | E_In_Parameter
                          and then Present (Discriminal_Link (E))
                        then
                           E := Discriminal_Link (E);
                        end if;

                        case Ekind (E) is
                           when E_Discriminant | E_Component =>
                              if Ekind (Sinfo.Scope (E)) not in
                                E_Protected_Type | E_Task_Type
                              then
                                 --  We include stuff from tasks and POs,
                                 --  but otherwise we need to ignore
                                 --  discriminants and components.
                                 return OK;
                              end if;
                           when others =>
                              null;
                        end case;

                        if Ekind (E) /= E_Constant
                          or else Local_Constants.Contains (E)
                          or else Has_Variable_Input
                          (Direct_Mapping_Id (Unique_Entity (E)))
                        then
                           if Reduced then
                              VS.Include (Direct_Mapping_Id
                                            (Unique_Entity (E)));
                           else
                              VS.Union (Flatten_Variable (E, Scope));
                           end if;
                           if Consider_Extensions
                             and then Extensions_Visible (E, Scope)
                           then
                              VS.Include (Direct_Mapping_Id
                                            (Unique_Entity (E),
                                             Facet => Extension_Part));
                           end if;
                        end if;
                     end;

                  when Discrete_Or_Fixed_Point_Kind =>
                     if Is_Constrained (N) then
                        declare
                           SR : constant Node_Id := Scalar_Range (N);
                           LB : constant Node_Id := Low_Bound (SR);
                           HB : constant Node_Id := High_Bound (SR);
                        begin
                           VS.Union (Recurse_On (LB));
                           VS.Union (Recurse_On (HB));
                        end;
                     end if;

                  when others =>
                     null;
               end case;

            when N_Aggregate =>
               VS.Union (Recurse_On (Aggregate_Bounds (N)));

            when N_Selected_Component =>
               if Ekind (Entity (Selector_Name (N))) in E_Entry    |
                                                        E_Function
               then
                  --  Here we are dealing with a call of a protected
                  --  entry/function. This appears on the tree as a selected
                  --  component of the protected object.

                  --  Sanity check that parent is an entry/subprogram call
                  pragma Assert (Nkind (Parent (N)) in N_Entry_Call_Statement |
                                                       N_Subprogram_Call);

                  VS.Union (Process_Subprogram_Call (Parent (N)));
                  return Skip;
               end if;

               if Reduced then
                  --  In reduced mode we just keep traversing the tree, but
                  --  we need to turn off consider_extensions.

                  VS.Union (Recurse_On (Prefix (N)));
                  return Skip;
               else
                  VS.Union
                    (Untangle_Record_Fields
                       (N,
                        Scope                        => Scope,
                        Local_Constants              => Local_Constants,
                        Fold_Functions               => Fold_Functions,
                        Use_Computed_Globals         => Use_Computed_Globals,
                        Expand_Synthesized_Constants =>
                          Expand_Synthesized_Constants));
                  return Skip;

               end if;

            when N_Type_Conversion =>
               if Reduced then
                  return OK;

               elsif Ekind (Get_Type (N, Scope)) in Record_Kind then
                  --  We use Untangle_Record_Assignment as this can deal
                  --  with view conversions.

                  declare
                     M : constant Flow_Id_Maps.Map :=
                       Untangle_Record_Assignment
                       (N,
                        Map_Root                     =>
                          Direct_Mapping_Id (Etype (N)),
                        Map_Type                     => Get_Type (N, Scope),
                        Scope                        => Scope,
                        Local_Constants              => Local_Constants,
                        Fold_Functions               => Fold_Functions,
                        Use_Computed_Globals         => Use_Computed_Globals,
                        Expand_Synthesized_Constants =>
                          Expand_Synthesized_Constants);
                  begin
                     for C in M.Iterate loop
                        VS.Union (Flow_Id_Maps.Element (C));
                     end loop;
                  end;

                  return Skip;

               else
                  return OK;

               end if;

            when N_Attribute_Reference =>
               case Get_Attribute_Id (Attribute_Name (N)) is
                  when Attribute_Update =>
                     if Reduced or Is_Tagged_Type (Get_Type (N, Scope)) then
                        --  !!! Precise analysis is disabled for tagged types
                        return OK;
                     else
                        VS.Union
                          (Untangle_Record_Fields
                             (N,
                              Scope                        => Scope,
                              Local_Constants              => Local_Constants,
                              Fold_Functions               => Fold_Functions,
                              Use_Computed_Globals         =>
                                Use_Computed_Globals,
                              Expand_Synthesized_Constants =>
                                Expand_Synthesized_Constants));
                        return Skip;
                     end if;

                  when Attribute_Constrained =>
                     for F of Recurse_On (Prefix (N)) loop
                        if F.Kind in Direct_Mapping | Record_Field and then
                          F.Facet = Normal_Part and then
                          Has_Bounds (F, Scope)
                        then
                           --  This is not a bound variable, but it
                           --  requires bounds tracking. We make it a
                           --  bound variable.
                           VS.Include (F'Update (Facet => The_Bounds));
                        elsif Is_Discriminant (F) then
                           VS.Include (F);
                        end if;
                     end loop;
                     return Skip;

                  when Attribute_First  |
                       Attribute_Last   |
                       Attribute_Length |
                       Attribute_Range  =>

                     declare
                        T  : constant Node_Id := Get_Type (Prefix (N), Scope);
                        LB : Node_Id;
                        HB : Node_Id;
                     begin
                        if Is_Constrained (T) then
                           if Is_Array_Type (T) then
                              LB := Type_Low_Bound (Etype (First_Index (T)));
                              HB := Type_High_Bound (Etype (First_Index (T)));
                           else
                              LB := Low_Bound (Scalar_Range (T));
                              HB := High_Bound (Scalar_Range (T));
                           end if;

                           case Get_Attribute_Id (Attribute_Name (N)) is
                              when Attribute_First =>
                                 --  Add variables from Low_Bound
                                 VS.Union (Recurse_On (LB));

                              when Attribute_Last  =>
                                 --  Add variables from High_Bound
                                 VS.Union (Recurse_On (HB));

                              when Attribute_Length | Attribute_Range =>
                                 --  Add variables from Low_Bound and
                                 --  High_Bound.
                                 VS.Union (Recurse_On (LB));
                                 VS.Union (Recurse_On (HB));

                              when others =>
                                 raise Why.Unexpected_Node;
                           end case;
                        else
                           for F of Recurse_On (Prefix (N)) loop
                              if F.Kind in Direct_Mapping | Record_Field
                                and then F.Facet = Normal_Part
                                and then Has_Bounds (F, Scope)
                              then
                                 --  This is not a bound variable, but
                                 --  it requires bounds tracking. We
                                 --  make it a bound variable.
                                 VS.Include (F'Update (Facet => The_Bounds));

                              else
                                 --  This is something else. We just
                                 --  copy it.
                                 VS.Include (F);
                              end if;
                           end loop;
                        end if;
                     end;
                     return Skip;

                  when Attribute_Loop_Entry =>
                     --  Again, we ignore loop entry references, these
                     --  are dealt with by Do_Pragma and
                     --  Do_Loop_Statement in the CFG construction.
                     return Skip;

                  when Attribute_Callable   |
                       Attribute_Caller     |
                       Attribute_Count      |
                       Attribute_Terminated =>
                     --  Add the implicit use of
                     --  Ada.Task_Identification.Tasking_State
                     VS.Include
                       (Get_Flow_Id
                          (To_Entity_Name
                             ("ada__task_identification__tasking_state"),
                           Normal_Use,
                           Scope));

                  when others =>
                     null;
               end case;  -- dealing with all the attributes

            when N_In | N_Not_In =>
               --  Membership tests involving type with predicates have the
               --  predicate flow into the variable set returned.

               declare
                  procedure Process_Type (E : Entity_Id);
                  --  Merge variables used in predicate functions for the
                  --  given type.

                  procedure Process_Type (E : Entity_Id)
                  is
                     P          : Node_Id;
                     GP, GI, GO : Flow_Id_Sets.Set;
                  begin
                     if Present (E) then
                        P := Predicate_Function (E);
                     else
                        P := Empty;
                     end if;
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
                       (Subprogram           => P,
                        Scope                => Scope,
                        Classwide            => False,
                        Proof_Ins            => GP,
                        Reads                => GI,
                        Writes               => GO,
                        Use_Computed_Globals => Use_Computed_Globals);
                     pragma Assert (GO.Length = 0);

                     declare
                        Effects : constant Flow_Id_Sets.Set := GP or GI or GO;
                     begin
                        for F of Effects loop
                           VS.Include (Change_Variant (F, Normal_Use));
                        end loop;
                     end;

                  end Process_Type;

                  P : Node_Id;
               begin
                  if Present (Right_Opnd (N)) then
                     --  x in t
                     P := Right_Opnd (N);
                     if Nkind (P) = N_Identifier
                        and then Ekind (Entity (P)) in Type_Kind
                     then
                        Process_Type (Get_Type (P, Scope));
                     end if;
                  else
                     --  x in t | 1 .. y | u
                     P := First (Alternatives (N));
                     while Present (P) loop
                        if Nkind (P) = N_Identifier
                          and then Ekind (Entity (P)) in Type_Kind
                        then
                           Process_Type (Get_Type (P, Scope));
                        end if;
                        Next (P);
                     end loop;
                  end if;
               end;
               return OK;

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);

      --  Start of processing for Get_Variable_Set

   begin
      Traverse (N);

      return S : Flow_Id_Sets.Set do
         --  We need to do some post-processing on the result here. First
         --  we check each variable to see if it is the result of an
         --  action. For flow analysis its more helpful to talk about the
         --  original variables, so we undo these actions whenever
         --  possible.
         for F of VS loop
            case F.Kind is
               when Direct_Mapping | Record_Field =>
                  declare
                     N : constant Node_Id :=
                       Parent (Get_Direct_Mapping_Id (F));
                  begin
                     if Nkind (N) = N_Object_Declaration
                       and then Is_Action (N)
                     then
                        case Nkind (Expression (N)) is
                           when N_Identifier =>
                              S.Include
                                (F'Update
                                   (Node => Unique_Entity
                                      (Entity (Expression (N)))));
                           when others =>
                              S.Union (Recurse_On (Expression (N)));
                        end case;
                     else
                        S.Include (F);
                     end if;
                  end;

               when others =>
                  S.Include (F);
            end case;
         end loop;

         --  And finally, we remove any local constants.
         S := Filter_Out_Constants (S, Local_Constants);
      end return;
   end Get_Variable_Set;

   function Get_Variable_Set
     (L                            : List_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Allow_Statements             : Boolean := False;
      Expand_Synthesized_Constants : Boolean := False)
      return Flow_Id_Sets.Set
   is
      VS : Flow_Id_Sets.Set;
      P  : Node_Id;
   begin
      P := First (L);
      while Present (P) loop
         VS.Union
           (Get_Variable_Set
              (N                            => P,
               Scope                        => Scope,
               Local_Constants              => Local_Constants,
               Fold_Functions               => Fold_Functions,
               Use_Computed_Globals         => Use_Computed_Globals,
               Reduced                      => Reduced,
               Allow_Statements             => Allow_Statements,
               Expand_Synthesized_Constants => Expand_Synthesized_Constants));

         P := Next (P);
      end loop;
      return VS;
   end Get_Variable_Set;

   -----------------
   -- Has_Depends --
   -----------------

   function Has_Depends (Subprogram : Entity_Id) return Boolean is
   begin
      return Present (Get_Pragma (Subprogram, Pragma_Depends));
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

   function Has_Variable_Input (F : Flow_Id) return Boolean is
      function Get_Declaration (E : Entity_Id) return Node_Id
      with Post => Nkind (Get_Declaration'Result) = N_Object_Declaration;
      --  Returns the N_Object_Declaration corresponding to entity E
      --  @param E is the entity whose declaration we are looking for
      --  @return the N_Object_Declaration of entity E

      ---------------------
      -- Get_Declaration --
      ---------------------

      function Get_Declaration (E : Entity_Id) return Node_Id is
         D : Node_Id;
      begin
         D := E;
         while Nkind (D) /= N_Object_Declaration
           and then Present (Parent (D))
         loop
            D := Parent (D);
         end loop;

         return D;
      end Get_Declaration;

      E    : Entity_Id;
      Decl : Node_Id;
      FS   : Flow_Id_Sets.Set;
   begin
      E := Get_Direct_Mapping_Id (F);

      if not Is_Constant_Object (E) then
         --  If we are not dealing with a constant object then we do
         --  not care whether it has variable input or not.
         return False;
      end if;

      if Nkind (E) in N_Entity
        and then Ekind (E) in Formal_Kind
      then
         --  If we are dealing with a formal parameter then we
         --  consider this to be a variable.
         return True;
      end if;

      --  If we are dealing with an imported constant, we consider this to have
      --  potentially variable input.

      if Is_Imported (E) then
         return True;
      end if;

      Decl := Get_Declaration (E);
      if No (Expression (Decl)) then
         --  We are dealing with a deferred constant so we need to get
         --  to the full view.
         E    := Full_View (E);
         Decl := Get_Declaration (E);
      end if;

      if not Entity_In_SPARK (E) then
         --  We are dealing with an entity that is not in SPARK so we
         --  assume that it does not have variable input.
         return False;
      end if;

      FS := Get_Variable_Set (Expression (Decl),
                              Scope                => Get_Flow_Scope (E),
                              Local_Constants      => Node_Sets.Empty_Set,
                              Fold_Functions       => True,
                              Use_Computed_Globals => GG_Has_Been_Generated);
      --  Note that Get_Variable_Set calls Has_Variable_Input when it
      --  finds a constant. This means that there might be some mutual
      --  recursion here (but this should be fine).

      if FS /= Flow_Id_Sets.Empty_Set then
         --  If any variable was found then return True
         return True;
      end if;

      if not GG_Has_Been_Generated
        and then Get_Function_Set (Expression (Decl),
                                   Include_Predicates => False)
          /= Node_Sets.Empty_Set
      then
         --  Globals have not yet been computed. If we find any function
         --  calls we consider the constant to have variable inputs (this
         --  is the safe thing to do).
         return True;
      end if;

      --  If we reach this point then the constant does not have
      --  variable input.
      return False;
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

      Ptr  : Entity_Id;
      Ptr2 : Entity_Id;

      S    : Node_Sets.Set;
   begin
      Comp_Graph := Component_Graphs.Create;

      S := Node_Sets.Empty_Set;
      for E of Entity_Set loop
         if Is_Record_Type (E)
           or else Ekind (E) in E_Protected_Type | E_Task_Type
         then
            Ptr := First_Component_Or_Discriminant (E);
            while Present (Ptr) loop
               if not S.Contains (Ptr) then
                  S.Include (Ptr);
                  Comp_Graph.Add_Vertex (Ptr);
               end if;
               if Present (Original_Record_Component (Ptr))
                 and then not S.Contains (Original_Record_Component (Ptr))
               then
                  S.Include (Original_Record_Component (Ptr));
                  Comp_Graph.Add_Vertex (Original_Record_Component (Ptr));
               end if;
               if Ekind (Ptr) = E_Discriminant
                 and then Present (Corresponding_Discriminant (Ptr))
                 and then not S.Contains (Corresponding_Discriminant (Ptr))
               then
                  S.Include (Corresponding_Discriminant (Ptr));
                  Comp_Graph.Add_Vertex (Corresponding_Discriminant (Ptr));
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
            Ptr := Node_Sets.Element (S.First);
            S.Exclude (Ptr);

            --  Create a new component.
            Comp_Graph.New_Cluster (C);

            --  Seed the work list.
            Work_List := Node_Sets.To_Set (Ptr);

            --  Flood current component.
            while not Work_List.Is_Empty loop
               Ptr := Node_Sets.Element (Work_List.First);
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

   -----------------------------------
   -- Is_Constant_After_Elaboration --
   -----------------------------------

   function Is_Constant_After_Elaboration (N : Node_Id) return Boolean is
      Expr : Node_Id;
   begin
      if No (N) then
         --  Trivially false
         return False;
      end if;

      Expr := (if Present (Pragma_Argument_Associations (N))
               then Expression (First (Pragma_Argument_Associations (N)))
               else Empty);

      --  The pragma has an optional Boolean expression, the related
      --  property is enabled only when the expression evaluates to True.

      if Present (Expr) then
         return Is_True (Expr_Value (Get_Pragma_Arg (Expr)));
      else
         --  Otherwise the lack of expression enables the property
         --  by default.
         return True;
      end if;
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
            return GG_Has_Been_Generated
              and then GG_Is_Initialized_At_Elaboration (F.Name);

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
            --  The fact that we have a Magic_String instead of an entity means
            --  that we this comes from another compilation unit (via an
            --  indirect call) and therefore has to have already been
            --  elaborated.
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
      --  We can't possibly up-project something that does not
      --  correspond to a direct mapping.
      if F.Kind /= Direct_Mapping then
         return False;
      end if;

      declare
         N : constant Node_Id := Get_Direct_Mapping_Id (F);
      begin
         --  There is no point in up-projecting if any of the
         --  following is True.
         if Ekind (N) not in E_Abstract_State | E_Constant | E_Variable
           or else (No (Encapsulating_State (N))
                      and then not Is_Concurrent_Comp_Or_Disc (F))
           or else Is_Visible (N, Scope)
         then
            return False;
         end if;

         return True;
      end;
   end Is_Non_Visible_Constituent;

   --------------------
   -- Is_Null_Record --
   --------------------

   function Is_Null_Record (E : Entity_Id) return Boolean is
   begin
      if Is_Type (E) then
         if Ekind (E) in Record_Kind then
            case Ekind (E) is
               when E_Class_Wide_Type | E_Class_Wide_Subtype =>
                  --  We always have the tag.
                  return False;
               when others =>
                  --  ??? there should be a cheaper way to check this
                  return All_Components (E).Is_Empty;
            end case;
         else
            return False;
         end if;
      elsif Ekind (E) = E_Abstract_State then
         return False;
      else
         return Is_Null_Record (Get_Full_Type_Without_Checking (E));
      end if;
   end Is_Null_Record;

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
      if F.Kind not in Direct_Mapping | Record_Field then
         --  Consider anything that is not a Direct_Mapping or a
         --  Record_Field to be a variable.
         return True;
      end if;

      return not Is_Constant_Object (Get_Direct_Mapping_Id (F))
        or else Has_Variable_Input (F);
   end Is_Variable;

   -----------------------
   -- Loop_Writes_Known --
   -----------------------

   function Loop_Writes_Known (E : Entity_Id) return Boolean is
   begin
      return Loop_Info_Frozen and then Loop_Info.Contains (E);
   end Loop_Writes_Known;

   --------------------------
   -- Quantified_Variables --
   --------------------------

   function Quantified_Variables (N : Node_Id) return Flow_Id_Sets.Set is
      RV : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

      function Proc (N : Node_Id) return Traverse_Result;

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Quantified_Expression =>
               if Present (Iterator_Specification (N)) then
                  RV.Include (Direct_Mapping_Id
                                (Defining_Identifier
                                   (Iterator_Specification (N))));
               elsif Present (Loop_Parameter_Specification (N)) then
                  RV.Include (Direct_Mapping_Id
                                (Defining_Identifier
                                   (Loop_Parameter_Specification (N))));
               else
                  Print_Tree_Node (N);
                  raise Why.Unexpected_Node;
               end if;

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Proc);
   begin
      Traverse (N);
      return RV;
   end Quantified_Variables;

   -------------------------------
   -- Rely_On_Generated_Depends --
   -------------------------------

   function Rely_On_Generated_Depends
     (E     : Entity_Id;
      Scope : Flow_Scope)
      return Boolean
   is
      Body_E : constant Entity_Id := Get_Body_Entity (E);
   begin
      if Rely_On_Generated_Global (E, Scope) then
         if Present (Body_E) then
            declare
               Depends_N         : constant Node_Id :=
                 Get_Pragma (E, Pragma_Depends);

               Refined_Depends_N : constant Node_Id :=
                 Get_Pragma (Body_E, Pragma_Refined_Depends);

               B_Scope           : constant Flow_Scope :=
                 Get_Flow_Scope (Body_E);
            begin
               if Present (Depends_N)
                 and then No (Refined_Depends_N)
                 and then Mentions_State_With_Visible_Refinement (Depends_N,
                                                                  B_Scope)
               then
                  return True;
               end if;
            end;
         end if;
      end if;

      --  If we reach here then we must not rely on the generated
      --  depends.
      return False;
   end Rely_On_Generated_Depends;

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
      if Present (Body_E)
        and then Entity_Body_In_SPARK (E)
        and then Entity_Body_Valid_SPARK (E)
        and then Is_Visible (Body_E, Scope)
        and then Refinement_Needed (E)
      then
         return True;
      end if;

      --  If we reach here then we must not rely on the generated
      --  globals.
      return False;
   end Rely_On_Generated_Global;

   --------------------
   -- Same_Component --
   --------------------

   function Same_Component (C1, C2 : Entity_Id) return Boolean is
      use Component_Graphs;

      A : constant Cluster_Id :=
        Comp_Graph.Get_Cluster (Comp_Graph.Get_Vertex (C1));
      B : constant Cluster_Id :=
        Comp_Graph.Get_Cluster (Comp_Graph.Get_Vertex (C2));
   begin
      return A = B;
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
      --  Searches under contract for Output and sets needle to the
      --  node, if found.

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
                        pragma Assert (Present (Original_Node (Tmp)));

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
                                      (Present (Original_Node (Tmp2)));

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
                           pragma Assert (Present (Original_Node (Tmp2)));

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
                        pragma Assert (Present (Original_Node (Tmp)));

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

   begin
      case Contract is
         when Pragma_Depends =>
            declare
               Body_E : constant Node_Id := Get_Body_Entity (Unit);
            begin
               Contract_N := (if Present (Body_E)
                              then Get_Pragma (Body_E, Pragma_Refined_Depends)
                              else Empty);
            end;
            if No (Contract_N) then
               Contract_N := Get_Pragma (Unit, Pragma_Depends);
            end if;
            if No (Contract_N) then
               return Unit;
            end if;

            Find_Export_Internal (Contract_N);
            if Present (Needle) then
               return Needle;
            else
               return Contract_N;
            end if;

         when Pragma_Initializes =>
            Contract_N := Get_Pragma (Unit, Pragma_Initializes);

            if No (Contract_N) then
               return Unit;
            end if;

            Find_Export_Internal (Contract_N);
            if Present (Needle) then
               return Needle;
            else
               return Contract_N;
            end if;

         when others =>
            raise Why.Unexpected_Node;
      end case;
   end Search_Contract;

   --------------------
   -- To_Flow_Id_Set --
   --------------------

   function To_Flow_Id_Set
     (NS    : Name_Sets.Set;
      View  : Flow_Id_Variant := Normal_Use;
      Scope : Flow_Scope        := Null_Flow_Scope)
      return Flow_Id_Sets.Set
   is
      FS : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for N of NS loop
         FS.Include (Get_Flow_Id (N, View, Scope));
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
      is (Get_Variable_Set
            (N,
             Scope                        => Scope,
             Local_Constants              => Local_Constants,
             Fold_Functions               => Fold_Functions,
             Use_Computed_Globals         => Use_Computed_Globals,
             Reduced                      => False,
             Allow_Statements             => False,
             Expand_Synthesized_Constants => Expand_Synthesized_Constants));
      --  Helpful wrapper for calling Get_Variable_Set.

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
         F      : constant Flow_Id := Add_Component (Map_Root, Component);
         Tmp    : Flow_Id_Maps.Map;
         Output : Flow_Id;
         Inputs : Flow_Id_Sets.Set;
      begin
         case Ekind (Get_Type (Component, Scope)) is
            when Record_Kind =>
               Tmp := Recurse_On (Input, F);

               for C in Tmp.Iterate loop
                  Output := Flow_Id_Maps.Key (C);
                  Inputs := Flow_Id_Maps.Element (C);

                  M.Include (Output, Inputs);
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
               for Ptr of All_Components (Map_Type) loop
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
                     M (LHS_Ext) := M (LHS_Ext).Union (To_Ext);
                     --  ??? workaround for O812-006
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

               Tmp_Set : Flow_Id_Sets.Set;

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
               Tmp_Set         := Flatten_Variable (T_To, Scope);
               --  !!! Tmp_Set is workaround for compiler bug
               for F of Tmp_Set loop
                  Valid_To_Fields.Include (Join (Map_Root, F));
               end loop;

               for C in Tmp.Iterate loop
                  declare
                     Output : constant Flow_Id := Flow_Id_Maps.Key (C);
                     Inputs : constant Flow_Id_Sets.Set :=
                       Flow_Id_Maps.Element (C);
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
                  M (The_Ext) := M (The_Ext).Union (Valid_To_Fields);
                  --  ??? workaround for O812-006
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
                  Error_Msg_N ("can't untangle attribute", N);
                  raise Why.Not_Implemented;
            end case;

         when N_Function_Call =>
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
                  for C in M.Iterate loop
                     M (C) := M (C).Union (FS);
                     --  ??? workaround for O812-006
                  end loop;
               end if;
            end;

         when others =>
            Error_Msg_N ("can't untangle node " & Nkind (N)'Img, N);
            raise Why.Unexpected_Node;
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
      is (case Nkind (N) is
             when N_Attribute_Reference =>
                Get_Attribute_Id (Attribute_Name (N)) in
                  Attribute_Old | Attribute_Loop_Entry,
             when others =>
                False);

      function Get_Vars_Wrapper (N : Node_Id) return Flow_Id_Sets.Set
      is (Get_Variable_Set
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
      --  We also note all components (bar, z), 'update nodes and the
      --  order in which they access or update fields (bar,
      --  the_update, z).

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
                        K : constant Flow_Id          := Flow_Id_Maps.Key (C);
                        V : constant Flow_Id_Sets.Set :=
                          Flow_Id_Maps.Element (C);
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
      --  Fold_Functions (a parameter for Get_Variable_Set) is specified as
      --  `false' here because Untangle should only ever be called where we
      --  assign something to something. And you can't assign to function
      --  results (yet).

      function Get_Vars_Wrapper (N    : Node_Id;
                                 Fold : Boolean)
                                 return Flow_Id_Sets.Set
      is (Get_Variable_Set
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

      Idx                      : Natural;
      Process_Type_Conversions : Boolean;

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
         Write_Str ("Seq is:");
         Write_Eol;
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

                     function In_Type (C : Entity_Id) return Boolean;

                     function In_Type (C : Entity_Id) return Boolean is
                     begin
                        for Ptr of All_Components (New_Typ) loop
                           if Same_Component (C, Ptr) then
                              return True;
                           end if;
                        end loop;
                        return False;
                     end In_Type;
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
         if Present (Encapsulating_State (Enclosing_E)) then
            Enclosing_E := Encapsulating_State (Enclosing_E);
         else
            pragma Assert (Is_Concurrent_Comp_Or_Disc (F));
            Enclosing_E := Get_Enclosing_Concurrent_Object (F);
         end if;
         Enclosing_F := Direct_Mapping_Id (Enclosing_E);
      end loop;

      return Enclosing_F;
   end Up_Project_Constituent;

end Flow_Utility;
