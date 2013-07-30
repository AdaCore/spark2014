------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              F L O W . C O N T R O L _ F L O W _ G R A P H               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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

with Nlists;   use Nlists;
with Namet;    use Namet;

with Treepr;   use Treepr;

with Why;

with Flow.Debug;        use Flow.Debug;

package body Flow.Utility is

   use type Flow_Id_Sets.Set;

   ----------------------------------------------------------------------
   --  Debug
   ----------------------------------------------------------------------

   Debug_Trace_Untangle : constant Boolean := False;
   --  Enable this to print the tree and def/use sets in each call of
   --  Untangle_Assignment_Target.

   ----------------------------------------------------------------------
   --  Local
   ----------------------------------------------------------------------

   function All_Record_Components
     (Entire_Var : Entity_Id)
      return Flow_Id_Sets.Set
      with Pre => Ekind (Get_Full_Type (Entire_Var)) in
        E_Record_Type | E_Record_Subtype;
   --  Given the record Entire_Var, return a set with all components.
   --  So, for example we might return:
   --     * p.x
   --     * p.r.a
   --     * p.r.b

   function All_Record_Components
     (The_Record_Field : Flow_Id)
      return Flow_Id_Sets.Set
      with Pre => The_Record_Field.Kind in Direct_Mapping | Record_Field
                  and then Ekind (Get_Full_Type
                                    (Get_Direct_Mapping_Id
                                       (The_Record_Field))) in
                                     E_Record_Type | E_Record_Subtype;
   --  As above but only include fields that are equal to Record_Field or are
   --  nested under it. For example if Record_Field = p.r for the above
   --  record, then we will get the following set:
   --     * p.r.a
   --     * p.r.b

   function Find_Contracts (E    : Entity_Id;
                            Name : Name_Id)
                            return Node_Lists.List
     with Pre => Ekind (E) in Subprogram_Kind;
   --  Walk the Contract node attached to E and return the pragma
   --  matching Name.

   function Filter_Out_Constants (S : Flow_Id_Sets.Set)
                                  return Flow_Id_Sets.Set;
   --  Remove all flow_ids referencing constants from the set.

   ---------------------------
   -- All_Record_Components --
   ---------------------------

   function All_Record_Components
     (Entire_Var : Entity_Id)
      return Flow_Id_Sets.Set
   is
   begin
      return All_Record_Components (Direct_Mapping_Id (Entire_Var));
   end All_Record_Components;

   function All_Record_Components
     (The_Record_Field : Flow_Id)
      return Flow_Id_Sets.Set
   is
      Entire_Var : constant Entity_Id :=
        Get_Direct_Mapping_Id (The_Record_Field);

      All_Comp   : Flow_Id_Sets.Set   := Flow_Id_Sets.Empty_Set;

      procedure Possibly_Include (F : Flow_Id);
      --  Include F in All_Comp if it is The_Record_Field or a
      --  subcomponent of it.

      procedure Process_Record (R_Type : Entity_Id;
                                Comp   : Entity_Lists.Vector)
      with Pre => Ekind (R_Type) in E_Record_Type | E_Record_Subtype;
      --  Recursively go through the record's components, adding
      --  everything to All_Comp.

      procedure Possibly_Include (F : Flow_Id)
      is
      begin
         --  ??? Direct access into flow_id, should be removed somehow.
         if F.Component.Length < The_Record_Field.Component.Length then
            return;
         end if;

         for I in Natural
           range 1 .. Natural (The_Record_Field.Component.Length)
         loop
            if The_Record_Field.Component (I) /= F.Component (I) then
               return;
            end if;
         end loop;

         All_Comp.Include (F);
      end Possibly_Include;

      procedure Process_Record (R_Type : Entity_Id;
                                Comp   : Entity_Lists.Vector)
      is
         C : Entity_Id;
         F : Flow_Id;
      begin
         --  Make a vertex for each subcomponent, unless its a
         --  record. If we have a record we recurse instead.
         C := First_Component_Or_Discriminant (R_Type);
         while Present (C) loop
            declare
               Tmp : Entity_Lists.Vector := Comp;
            begin
               Tmp.Append (C);

               case Ekind (Get_Full_Type (C)) is
                  when E_Record_Type =>
                     Process_Record (Get_Full_Type (C), Tmp);

                  when others =>
                     F := Flow_Id'(Kind      => Record_Field,
                                   Variant   => Normal_Use,
                                   Node      => Entire_Var,
                                   Name      => Null_Entity_Name,
                                   Component => Tmp);
                     Possibly_Include (F);
               end case;
            end;

            C := Next_Component_Or_Discriminant (C);
         end loop;
      end Process_Record;

   begin
      Process_Record (Get_Full_Type (Entire_Var),
                      Entity_Lists.Empty_Vector);
      return All_Comp;
   end All_Record_Components;

   --------------------
   -- Find_Contracts --
   --------------------

   function Find_Contracts (E    : Entity_Id;
                            Name : Name_Id)
                            return Node_Lists.List
   is
      C          : constant Node_Id := Contract (E);
      P          : Node_Id;
      Contracts  : Node_Lists.List := Node_Lists.Empty_List;
      Other_Name : Name_Id;
   begin
      case Name is
         when Name_Precondition | Name_Postcondition =>
            if Name = Name_Precondition then
               Other_Name := Name_Pre;
            else
               Other_Name := Name_Post;
            end if;

            P := Pre_Post_Conditions (C);
            while Present (P) loop
               if Chars (Pragma_Identifier (P)) in Name | Other_Name then
                  Contracts.Append
                    (Expression (First (Pragma_Argument_Associations (P))));
               end if;

               P := Next_Pragma (P);
            end loop;

            return Contracts;

         when Name_Global | Name_Depends =>
            raise Why.Not_Implemented;

         when Name_Contract_Cases =>
            raise Why.Not_Implemented;

         when others =>
            raise Program_Error;
      end case;
   end Find_Contracts;

   --------------------------
   -- Filter_Out_Constants --
   --------------------------

   function Filter_Out_Constants (S : Flow_Id_Sets.Set)
                                  return Flow_Id_Sets.Set
   is
      R : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for F of S loop
         case F.Kind is
            when Direct_Mapping | Record_Field =>
               pragma Assert (Nkind (Get_Direct_Mapping_Id (F)) in N_Entity);
               if not (Ekind (Get_Direct_Mapping_Id (F)) = E_Constant) then
                  R.Include (F);
               end if;

            when Magic_String | Null_Value =>
               R.Include (F);
         end case;
      end loop;
      return R;
   end Filter_Out_Constants;

   ----------------------------------------------------------------------
   --  Package
   ----------------------------------------------------------------------

   ------------------------
   --  Get_Variable_Set  --
   ------------------------

   function Get_Variable_Set (Scope : Scope_Ptr;
                              N     : Node_Id)
                              return Flow_Id_Sets.Set
   is
      VS : Flow_Id_Sets.Set;

      procedure Process_Function_Call
        (Callsite       : Node_Id;
         Used_Variables : in out Flow_Id_Sets.Set)
         with Pre => Nkind (Callsite) = N_Function_Call;
      --  Work out which variables (including globals) are used in the
      --  function call and add them to the given set.

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

      procedure Process_Function_Call
        (Callsite       : Node_Id;
         Used_Variables : in out Flow_Id_Sets.Set) is

         Subprogram : constant Entity_Id := Entity (Name (Callsite));

         Global_Reads  : Flow_Id_Sets.Set;
         Global_Writes : Flow_Id_Sets.Set;

      begin
         Get_Globals (Subprogram   => Subprogram,
                      Reads        => Global_Reads,
                      Writes       => Global_Writes,
                      Refined_View => Should_Use_Refined_View (Scope,
                                                               Callsite));
         pragma Assert (Flow_Id_Sets.Length (Global_Writes) = 0);

         Used_Variables :=
           Used_Variables or
           Get_Variable_Set (Scope,
                             Parameter_Associations (Callsite));

         for G of Global_Reads loop
            Used_Variables.Include (Change_Variant (G, Normal_Use));
         end loop;
      end Process_Function_Call;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Procedure_Call_Statement =>
               --  If we ever get one of these we have a problem -
               --  Get_Variable_Set is only really meant to be called
               --  on expressions and not statements.
               raise Program_Error;

            when N_Later_Decl_Item =>
               --  These should allow us to go through package specs
               --  and bodies.
               return Skip;

            when N_Function_Call =>
               Process_Function_Call (Callsite       => N,
                                      Used_Variables => VS);
               return Skip;

            when N_Identifier | N_Expanded_Name =>
               if Present (Entity (N)) then
                  case Ekind (Entity (N)) is
                     when E_Variable |
                       E_Loop_Parameter |
                       E_Out_Parameter |
                       E_In_Parameter |
                       E_In_Out_Parameter =>
                        VS.Union (Flatten_Variable (Entity (N)));
                     when others =>
                        null;
                  end case;
               end if;

            when N_Defining_Identifier =>
               case Ekind (N) is
                  when E_Variable |
                    E_Loop_Parameter |
                    E_Out_Parameter |
                    E_In_Parameter |
                    E_In_Out_Parameter =>
                     VS.Union (Flatten_Variable (N));
                  when others =>
                     null;
               end case;

            when N_Selected_Component | N_Indexed_Component =>
               --  We strip out loop entry references as they are
               --  dealt with by Do_Pragma and Do_Loop_Statement in
               --  the CFG construction.
               if not Contains_Loop_Entry_Reference (N) then
                  declare
                     D, U : Flow_Id_Sets.Set;
                  begin
                     Untangle_Assignment_Target (Scope        => Scope,
                                                 N            => N,
                                                 Vars_Defined => D,
                                                 Vars_Used    => U);
                     VS.Union (D);
                     VS.Union (U);
                  end;
               end if;
               return Skip;

            when N_Attribute_Reference =>
               case Get_Attribute_Id (Attribute_Name (N)) is
                  when Attribute_First |
                    Attribute_Last |
                    Attribute_Length |
                    Attribute_Range =>
                     --  Ignore anything to do with ranges.
                     return Skip;

                  when Attribute_Loop_Entry =>
                     --  Again, we ignore loop entry references, these
                     --  are dealt with by Do_Pragma and
                     --  Do_Loop_Statement in the CFG construction.
                     return Skip;

                  when others =>
                     null;
               end case;

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);
   begin
      Traverse (N);
      return Filter_Out_Constants (VS);
   end Get_Variable_Set;

   function Get_Variable_Set (Scope : Scope_Ptr;
                              L     : List_Id)
                              return Flow_Id_Sets.Set
   is
      VS : Flow_Id_Sets.Set;
      P  : Node_Id;
   begin
      P := First (L);
      while Present (P) loop
         VS.Union (Get_Variable_Set (Scope, P));

         P := Next (P);
      end loop;
      return VS;
   end Get_Variable_Set;

   ----------------------
   -- Flatten_Variable --
   ----------------------

   function Flatten_Variable (E : Entity_Id) return Flow_Id_Sets.Set is
      U : constant Entity_Id := Unique_Entity (E);
   begin
      case Ekind (Get_Full_Type (U)) is
         when Elementary_Kind | Array_Kind =>
            return Flow_Id_Sets.To_Set (Direct_Mapping_Id (U));

         when E_Record_Type | E_Record_Subtype =>
            return All_Record_Components (Entire_Var => U);

         when E_Void =>
            pragma Assert (Ekind (E) = E_Abstract_State);
            return Flow_Id_Sets.To_Set (Direct_Mapping_Id (U));

         when others =>
            Print_Tree_Node (U);
            Print_Tree_Node (Etype (U));
            raise Why.Unexpected_Node;
      end case;
   end Flatten_Variable;

   function Flatten_Variable (F : Flow_Id) return Flow_Id_Sets.Set is
   begin
      case F.Kind is
         when Direct_Mapping =>
            return Flatten_Variable (Get_Direct_Mapping_Id (F));
         when Magic_String =>
            return Flow_Id_Sets.To_Set (F);
         when others =>
            raise Program_Error;
      end case;
   end Flatten_Variable;

   -------------------
   -- Get_Full_Type --
   -------------------

   function Get_Full_Type (E : Entity_Id) return Entity_Id
   is
      T : constant Entity_Id := Etype (E);
   begin
      if Ekind (E) = E_Abstract_State then
         return T;
      else
         pragma Assert (Is_Type (T));
         if Present (Full_View (T)) then
            return Full_View (T);
         else
            return T;
         end if;
      end if;
   end Get_Full_Type;

   --------------------------------
   -- Untangle_Assignment_Target --
   --------------------------------

   procedure Untangle_Assignment_Target
     (Scope        : Scope_Ptr;
      N            : Node_Id;
      Vars_Defined : out Flow_Id_Sets.Set;
      Vars_Used    : out Flow_Id_Sets.Set)
   is
      procedure Find_Bottom_Node (N             : Node_Id;
                                  Bottom_Node   : out Node_Id;
                                  End_Of_Record : out Node_Id;
                                  Partial_Use   : out Boolean);
      --  This procedure returns the bottom node of the subtree and
      --  finds the end of the outermost record node. We also detect
      --  if the end of record node is a partial use (array indexing)
      --  or entire use.
      --
      --  Let's consider the parse tree for P.R.A (I).A (J).X
      --  In the following parse tree 'i' represents an indexed
      --  component and s represents a selected component.
      --
      --                               Parse Tree
      --                                    s
      --                                   / \
      --                                  i   X
      --                                 / \
      --                                s   J
      --                               / \
      --                              i   A
      --                             / \
      --        End_Of_Record --->  s   I
      --                           / \
      --                          s   A
      --                         / \
      --      Bottom_Node --->  P   R
      --
      --  In this example Partial_Use would be True. If we had been
      --  given only P.R.A Partial_Use would be False.

      function Proc (N : Node_Id) return Traverse_Result;
      --  Traverses a subtree and adds each variable found inside
      --  the expression part of an N_Indexed_Component to the
      --  Vars_Used set.

      -------------------
      -- Find_Top_Node --
      -------------------

      procedure Find_Bottom_Node
        (N             : Node_Id;
         Bottom_Node   : out Node_Id;
         End_Of_Record : out Node_Id;
         Partial_Use   : out Boolean) is
      begin
         Bottom_Node   := N;
         End_Of_Record := N;
         Partial_Use   := False;

         while Nkind (Bottom_Node) in
           N_Indexed_Component | N_Selected_Component |
           N_Slice | N_Type_Conversion
         loop
            if Nkind (Bottom_Node) in N_Indexed_Component | N_Slice then
               End_Of_Record := Prefix (Bottom_Node);
               Partial_Use   := True;
            end if;
            Bottom_Node := Prefix (Bottom_Node);
         end loop;
      end Find_Bottom_Node;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Indexed_Component =>
               Vars_Used.Union (Get_Variable_Set (Scope, Expressions (N)));
               return OK;
            when N_Slice =>
               Vars_Used.Union (Get_Variable_Set (Scope, Discrete_Range (N)));
               return OK;
            when others =>
               return OK;
         end case;
      end Proc;

      procedure Merge_Array_Expressions is new Traverse_Proc (Proc);

      Bottom_Node   : Node_Id;
      End_Of_Record : Node_Id;
      Partial_Use   : Boolean;

   begin
      Vars_Used    := Flow_Id_Sets.Empty_Set;
      Vars_Defined := Flow_Id_Sets.Empty_Set;

      if Debug_Trace_Untangle then
         Print_Node_Subtree (N);
      end if;

      case Nkind (N) is
         when N_Type_Conversion =>
            Untangle_Assignment_Target
              (Scope        => Scope,
               N            => Expression (N),
               Vars_Defined => Vars_Defined,
               Vars_Used    => Vars_Used);

         when N_Identifier | N_Expanded_Name =>
            --  X :=
            Vars_Defined := Get_Variable_Set (Scope, N);

         when N_Selected_Component | N_Indexed_Component | N_Slice =>
            --  R.A :=
            --  A (...) :=

            --  First we collect all variables used in any index
            --  expression or a slice range, as they are always used.
            --
            --  So out of A (X + B (Y)).B (I) we call Get_Variable_Set
            --  on X + B (Y) and I and add this to Vars_Used.

            Merge_Array_Expressions (N);

            --  We now need to work out what we're ultimately dealing
            --  with. Bottom_Node is the entire variable and
            --  End_Of_Record points to either the entire variable or
            --  the last N_Selected_Component flow analysis will care
            --  about.

            Find_Bottom_Node (N, Bottom_Node, End_Of_Record, Partial_Use);

            --  We may be dealing with some record field. For example:
            --
            --     R.A
            --     R.A (12)
            --     R.A (12).Specific_Field
            --
            --  In all of these End_Of_Record will point to R.A.
            --
            --  There is the possibility that we are still dealing
            --  with more than one variable, for example if R.X.A and
            --  R.X.B exist then R.X will deal with both of the above.
            --
            --  We are interested it what comes next. For example with
            --  R.A we just define R.A, but with R.A (12) we define
            --  and use it. The Partial_Use flag keeps track of this.

            case Nkind (End_Of_Record) is
               when N_Selected_Component =>
                  case Nkind (Prefix (End_Of_Record)) is
                     when N_Function_Call =>
                        Vars_Defined.Union
                          (Get_Variable_Set (Scope, Prefix (End_Of_Record)));

                     when others =>
                        Vars_Defined.Union
                          (All_Record_Components
                             (Record_Field_Id (End_Of_Record)));
                        if Partial_Use then
                           Vars_Used.Union
                             (All_Record_Components
                                (Record_Field_Id (End_Of_Record)));
                        end if;
                  end case;

               when N_Indexed_Component | N_Slice =>
                  raise Program_Error;

               when N_Function_Call =>
                  --  Not strictly right, but this will satisfy the
                  --  postcondition.
                  Vars_Defined.Union (Get_Variable_Set (Scope, End_Of_Record));

               when others =>
                  Vars_Defined.Include
                    (Direct_Mapping_Id (Entity (End_Of_Record)));
                  if Partial_Use then
                     Vars_Used.Include
                       (Direct_Mapping_Id (Entity (End_Of_Record)));
                  end if;
            end case;

         when others =>
            raise Why.Unexpected_Node;
      end case;

      if Debug_Trace_Untangle then
         Print_Node_Set (Vars_Used);
         Print_Node_Set (Vars_Defined);
      end if;
   end Untangle_Assignment_Target;

   -----------------------
   -- Get_Preconditions --
   -----------------------

   function Get_Preconditions (E : Entity_Id)
                               return Node_Lists.List
   is
   begin
      return Find_Contracts (E, Name_Precondition);
   end Get_Preconditions;

   ---------------------------
   -- Is_Precondition_Check --
   ---------------------------

   function Is_Precondition_Check (N : Node_Id) return Boolean
   is
      A : constant Node_Id := First (Pragma_Argument_Associations (N));
   begin
      pragma Assert (Nkind (Expression (A)) = N_Identifier);
      return Chars (Expression (A)) in Name_Pre | Name_Precondition;
   end Is_Precondition_Check;

   ---------------------
   -- Is_Discriminant --
   ---------------------

   function Is_Discriminant (F : Flow_Id) return Boolean
   is
   begin
      case F.Kind is
         when Record_Field =>
            return Ekind (F.Component.Last_Element) = E_Discriminant;
         when Direct_Mapping | Magic_String =>
            return False;
         when Null_Value =>
            raise Why.Unexpected_Node;
      end case;
   end Is_Discriminant;

end Flow.Utility;
