------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2013-2014, Altran UK Limited                 --
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
with Ada.Containers.Hashed_Sets;

with Elists;                     use Elists;
with Errout;                     use Errout;
with Namet;                      use Namet;
with Nlists;                     use Nlists;
with Output;                     use Output;
with Sprint;                     use Sprint;
with Treepr;                     use Treepr;

with Why;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Util;                 use SPARK_Util;

with Flow_Debug;                 use Flow_Debug;
with Flow_Computed_Globals;      use Flow_Computed_Globals;
with Flow_Classwide;             use Flow_Classwide;

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

   Loop_Info_Frozen : Boolean       := False;
   Loop_Info        : Loop_Maps.Map := Loop_Maps.Empty_Map;

   ----------------------------------------------------------------------
   --  Local
   ----------------------------------------------------------------------

   package Component_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Entity_Id,
      Hash                => Component_Hash,
      Equivalent_Elements => Same_Component);

   function Filter_Out_Non_Local_Constants (S : Flow_Id_Sets.Set;
                                            C : Node_Sets.Set)
                                            return Flow_Id_Sets.Set;
   --  Remove all flow_ids referencing constants from the set.

   -----------------
   -- Get_Flow_Id --
   -----------------

   function Get_Flow_Id
     (Name : Entity_Name;
      View : Parameter_Variant)
      return Flow_Id
   is
      E : constant Entity_Id := Find_Entity (Name);
   begin
      if Present (E) then
         return Direct_Mapping_Id (E, View);
      end if;

      --  If none can be found, we fall back to the magic
      --  string.
      return Magic_String_Id (Name, View);
   end Get_Flow_Id;

   ------------------------------------
   -- Filter_Out_Non_Local_Constants --
   ------------------------------------

   function Filter_Out_Non_Local_Constants (S : Flow_Id_Sets.Set;
                                            C : Node_Sets.Set)
                                            return Flow_Id_Sets.Set
   is
      R : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for F of S loop
         case F.Kind is
            when Direct_Mapping | Record_Field =>
               declare
                  E : constant Entity_Id := Get_Direct_Mapping_Id (F);
                  pragma Assert (Nkind (E) in N_Entity);
               begin
                  if Ekind (E) /= E_Constant or else C.Contains (E) then
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
      return R;
   end Filter_Out_Non_Local_Constants;

   --------------
   -- Get_Type --
   --------------

   function Get_Type (F     : Flow_Id;
                      Scope : Flow_Scope)
                      return Entity_Id
   is
      E : Entity_Id;
   begin
      case F.Kind is
         when Direct_Mapping =>
            E := F.Node;
         when Record_Field =>
            E := F.Component.Last_Element;
         when others =>
            raise Program_Error;
      end case;
      if Ekind (E) in Private_Kind then
         if Is_Visible (Full_View (E), Scope) and then
           not Is_Itype (Full_View (E))
         then
            return Full_View (E);
         else
            return E;
         end if;
      elsif Ekind (E) in Type_Kind then
         return E;
      else
         return Get_Full_Type (E, Scope);
      end if;
   end Get_Type;

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
                                              else Get_Full_Type (N, Scope)),
             Scope                        => Scope,
             Local_Constants              => Local_Constants,
             Fold_Functions               => Fold_Functions,
             Use_Computed_Globals         => Use_Computed_Globals,
             Expand_Synthesized_Constants => Expand_Synthesized_Constants,
             Extensions_Irrelevant        => Ext_Irrelevant))
      with Pre => (if not Extensions_Irrelevant
                   then not Ext_Irrelevant);
      --  Helpful wrapper for recursing. Note that once extensions are not
      --  irrlevant its not right to start ignoring them again.

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
         case Ekind (Get_Full_Type (Component, Scope)) is
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
               Write_Str ("processing selected component");
               Write_Eol;
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
                 and then ((Ekind (Map_Type) in Class_Wide_Kind and then
                              Ekind (Etype (N)) not in Class_Wide_Kind)
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
                  if not To_Ext.Is_Empty then
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
               T_From : constant Entity_Id :=
                 Get_Full_Type (Expression (N), Scope);
               T_To   : constant Entity_Id :=
                 Get_Full_Type (N, Scope);

               --  To_Class_Wide : constant Boolean :=
               --    Ekind (T_To) in Class_Wide_Kind;

               Class_Wide_Conversion : constant Boolean :=
                 Ekind (T_From) not in Class_Wide_Kind and then
                 Ekind (T_To) in Class_Wide_Kind;

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
                       (Ekind (Get_Full_Type (N, Scope)) not in Class_Wide_Kind
                          and then Ekind (Map_Type) in Class_Wide_Kind);
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

                           if Ekind (Get_Full_Type (Entity (Output), Scope))
                             in Record_Kind
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

      Component     : Entity_Lists.Vector       := Entity_Lists.Empty_Vector;

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
        (Is_Tick_Update (Root_Node) and then
           Ekind (Get_Full_Type_Without_Checking (Root_Node))
             in Record_Kind) or else
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
        Ekind (Get_Full_Type_Without_Checking (Root_Node)) not in Record_Kind
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

                        if Ekind (Get_Full_Type (E, Scope)) in Record_Kind
                        then
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

   ----------------------------------------------------------------------
   --  Package
   ----------------------------------------------------------------------

   -------------------------------
   -- Has_User_Supplied_Globals --
   -------------------------------

   function Has_User_Supplied_Globals (Subprogram : Entity_Id)
                                       return Boolean
   is
   begin
      return Present (Get_Pragma (Subprogram, Pragma_Global)) or else
        Has_Depends (Subprogram);
   end Has_User_Supplied_Globals;

   -----------------
   -- Has_Depends --
   -----------------

   function Has_Depends (Subprogram : Entity_Id) return Boolean is
   begin
      return Present (Get_Pragma (Subprogram, Pragma_Depends));
   end Has_Depends;

   -----------------
   -- Get_Depends --
   -----------------

   procedure Get_Depends (Subprogram : Entity_Id;
                          Scope      : Flow_Scope;
                          Classwide  : Boolean;
                          Depends    : out Dependency_Maps.Map)
   is
      pragma Unreferenced (Classwide);
      --  For now we assume classwide globals are the same as the actual
      --  globals.

      Tmp : Dependency_Maps.Map;
   begin

      ----------------------------------------------------------------------
      --  Step 1: parse the appropriate dependency relation.
      ----------------------------------------------------------------------

      Tmp := Parse_Depends (Get_Contract_Node (Subprogram,
                                               Scope,
                                               Depends_Contract));

      ----------------------------------------------------------------------
      --  Step 2: expand out any abstract state for which the refinement is
      --  visible, similar to what we do for globals.
      ----------------------------------------------------------------------

      Depends := Dependency_Maps.Empty_Map;
      for C in Tmp.Iterate loop
         declare
            D_In  : constant Flow_Id_Sets.Set :=
              (if Present (Dependency_Maps.Key (C))
               then To_Flow_Id_Set (Down_Project
                                      (Node_Sets.To_Set
                                         (Get_Direct_Mapping_Id
                                            (Dependency_Maps.Key (C))),
                                       Scope))
               else Flow_Id_Sets.To_Set (Dependency_Maps.Key (C)));

            D_Out : constant Flow_Id_Sets.Set :=
              To_Flow_Id_Set (Down_Project
                                (To_Node_Set (Dependency_Maps.Element (C)),
                                 Scope));
         begin
            for I of D_In loop
               Depends.Include (I, D_Out);
            end loop;
         end;
      end loop;

   end Get_Depends;

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
                          Globals_For_Proof      : Boolean := False;
                          Use_Computed_Globals   : Boolean := True)
   is
      Global_Node  : constant Node_Id := Get_Contract_Node (Subprogram,
                                                            Scope,
                                                            Global_Contract);
      Depends_Node : constant Node_Id := Get_Contract_Node (Subprogram,
                                                            Scope,
                                                            Depends_Contract);
   begin
      Proof_Ins := Flow_Id_Sets.Empty_Set;
      Reads     := Flow_Id_Sets.Empty_Set;
      Writes    := Flow_Id_Sets.Empty_Set;

      if Debug_Trace_Get_Global then
         Write_Str ("Get_Global (");
         Sprint_Node (Subprogram);
         Write_Str (", ");
         Print_Flow_Scope (Scope);
         Write_Str (")");
         Write_Eol;
      end if;

      if Present (Global_Node) then
         if Debug_Trace_Get_Global then
            Indent;
            Write_Str ("using user annotation");
            Write_Eol;
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
                     if not Globals_For_Proof or else
                       Ekind (Non_Limited_Global) /= E_In_Parameter
                     then
                        --  Proof does not count in parameters as
                        --  globals (as they are constants).
                        G_In.Insert (Non_Limited_Global);
                     end if;

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
                     if not Globals_For_Proof or else
                       Ekind (Non_Limited_Global) /= E_In_Parameter
                     then
                        --  See above.
                        G_Proof.Insert (Non_Limited_Global);
                     end if;

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
            --  Step 4: Convert to a Flow_Id set.
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
               Write_Str ("proof ins");
               Write_Eol;
               Indent;
               for F of Proof_Ins loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;

               Write_Str ("reads");
               Write_Eol;
               Indent;
               for F of Reads loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;

               Write_Str ("writes");
               Write_Eol;
               Indent;
               for F of Writes loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;
               Outdent;
            end if;

         end;

      elsif Present (Depends_Node) then

         --  If we have no global, but we do have a depends, we can
         --  reverse-engineer the global. This also solves the issue where
         --  the (computed) global is inconsistent with the depends. (See
         --  M807-032 for an example.)

         if Debug_Trace_Get_Global then
            Indent;
            Write_Str ("reversing depends annotation");
            Write_Eol;
            Outdent;
         end if;

         declare
            D_Map  : Dependency_Maps.Map;
            Params : Node_Sets.Set;
            E      : Entity_Id;
         begin
            Get_Depends (Subprogram => Subprogram,
                         Scope      => Scope,
                         Classwide  => Classwide,
                         Depends    => D_Map);

            --  We need to make sure not to include our own parameters in
            --  the globals we produce here.

            E := First_Formal (Subprogram);
            while Present (E) loop
               Params.Include (E);
               E := Next_Formal (E);
            end loop;

            --  Always OK to call direct_mapping here since you can't refer
            --  to hidden state in user-written depends contracts.

            for C in D_Map.Iterate loop
               declare
                  Output : constant Flow_Id := Dependency_Maps.Key (C);
                  Inputs : constant Flow_Id_Sets.Set :=
                    Dependency_Maps.Element (C);
               begin
                  E := (if Present (Output)
                        then Get_Direct_Mapping_Id (Output)
                        else Empty);
                  if Present (E) and then E /= Subprogram
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
               Write_Str ("reads");
               Write_Eol;
               Indent;
               for F of Reads loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;

               Write_Str ("writes");
               Write_Eol;
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
            Write_Str ("using pavlos globals");
            Write_Eol;
            Outdent;
         end if;

         GG_Get_Globals (Subprogram,
                         Scope,
                         Proof_Ins,
                         Reads,
                         Writes);

         if Debug_Trace_Get_Global then
            Indent;
            Write_Str ("proof ins");
            Write_Eol;
            Indent;
            for PI of Proof_Ins loop
               Sprint_Flow_Id (PI);
               Write_Eol;
            end loop;
            Outdent;

            Write_Str ("reads");
            Write_Eol;
            Indent;
            for R of Reads loop
               Sprint_Flow_Id (R);
               Write_Eol;
            end loop;
            Outdent;

            Write_Str ("writes");
            Write_Eol;
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
            Write_Str ("using yannick globals");
            Write_Eol;
            Outdent;
         end if;

         declare
            --  We exclude constants here, since any *analyzed* spark
            --  program (as opposed to called programs) will have the new
            --  generated globals. To be revisited in M314-013.
            ALI_Reads  : constant Name_Set.Set :=
              Get_Generated_Reads (Subprogram,
                                   Include_Constants => False);
            ALI_Writes : constant Name_Set.Set :=
              Get_Generated_Writes (Subprogram);

            F : Flow_Id;
         begin

            --  We process the reads
            if Debug_Trace_Get_Global then
               Indent;
               Write_Str ("reads");
               Write_Eol;
               Indent;
            end if;

            for R of ALI_Reads loop
               F := Get_Flow_Id (R, In_View);

               if Debug_Trace_Get_Global then
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end if;

               case F.Kind is
                  when Direct_Mapping =>
                     if Ekind (Get_Direct_Mapping_Id (F)) /= E_Constant then
                        --  We completely ignore all non-local constants
                        --  for now.
                        Reads.Include (F);
                     end if;

                  when Magic_String =>
                     Reads.Include (F);

                  when Null_Value | Record_Field | Synthetic_Null_Export  =>
                     raise Program_Error;
               end case;
            end loop;

            if Debug_Trace_Get_Global then
               Outdent;
               Write_Str ("writes");
               Write_Eol;
               Indent;
            end if;

            for W of ALI_Writes loop
               --  This is not a mistake, we must assume that all
               --  values written may also not change or that they are
               --  only partially updated.
               --
               --  This also takes care of discriminants as every out
               --  is really an in out.
               F := Get_Flow_Id (W, Out_View);

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
            Write_Str ("defaulting to null globals");
            Write_Eol;
            Outdent;
         end if;

      end if;
   end Get_Globals;

   -----------------------
   -- Get_Proof_Globals --
   -----------------------

   procedure Get_Proof_Globals (Subprogram : Entity_Id;
                                Classwide  : Boolean;
                                Reads      : out Flow_Id_Sets.Set;
                                Writes     : out Flow_Id_Sets.Set)
   is
      Proof_Ins : Flow_Id_Sets.Set;
      Tmp_In    : Flow_Id_Sets.Set;
      Tmp_Out   : Flow_Id_Sets.Set;
      Body_E    : constant Entity_Id := Get_Body (Subprogram);

      function Expand (F : Flow_Id) return Flow_Id_Sets.Set;
      --  If F represents abstract state, return the set of all its
      --  components. Otherwise return F. Additionally, remove formal
      --  in parameters from the set since proof is not interested in
      --  them.

      ------------
      -- Expand --
      ------------

      function Expand (F : Flow_Id) return Flow_Id_Sets.Set is
         Tmp : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
         Ptr : Elmt_Id;
      begin
         case F.Kind is
            when Direct_Mapping =>
               case Ekind (Get_Direct_Mapping_Id (F)) is
                  when E_Abstract_State =>
                     Ptr := First_Elmt (Refinement_Constituents
                                          (Get_Direct_Mapping_Id (F)));
                     while Present (Ptr) loop
                        --  We simply ignore the null refinement, it is
                        --  treated as if it was not present.
                        if Nkind (Node (Ptr)) /= N_Null then
                           Tmp.Union (Expand (Direct_Mapping_Id (Node (Ptr),
                                                                 F.Variant)));
                        end if;
                        Ptr := Next_Elmt (Ptr);
                     end loop;

                     Ptr := First_Elmt (Part_Of_Constituents
                                          (Get_Direct_Mapping_Id (F)));
                     while Present (Ptr) loop
                        --  Part_of cannot include a null refinement.
                        Tmp.Union (Expand (Direct_Mapping_Id (Node (Ptr),
                                                              F.Variant)));
                        Ptr := Next_Elmt (Ptr);
                     end loop;

                     if Tmp.Is_Empty then
                        --  If we can't refine this state (maybe the body
                        --  is not in SPARK, or simply not implemented or
                        --  there is a null refinement) then we use the
                        --  abstract state itself.
                        Tmp.Insert (F);
                     end if;

                  when E_In_Parameter =>
                     --  For proof we exclude formal parameters of
                     --  mode "In" from the set of globals.
                     null;

                  when others =>
                     Tmp.Insert (F);
               end case;

            when Magic_String =>
               Tmp.Insert (F);

            when Record_Field | Null_Value | Synthetic_Null_Export =>
               raise Program_Error;
         end case;
         return Tmp;
      end Expand;

   begin
      Get_Globals
        (Subprogram             => Subprogram,
         Scope                  => (if Present (Body_E) and then
                                      Entity_Body_In_SPARK (Subprogram)
                                    then Get_Flow_Scope (Body_E)
                                    else Get_Flow_Scope (Subprogram)),
         Classwide              => Classwide,
         Proof_Ins              => Proof_Ins,
         Reads                  => Tmp_In,
         Writes                 => Tmp_Out,
         Consider_Discriminants => False,
         Globals_For_Proof      => True);

      --  Merge the proof ins with the reads.
      Tmp_In.Union (Proof_Ins);

      --  Expand all variables.
      Reads := Flow_Id_Sets.Empty_Set;
      for F of Tmp_In loop
         Reads.Union (Expand (F));
      end loop;

      Writes := Flow_Id_Sets.Empty_Set;
      for F of Tmp_Out loop
         Writes.Union (Expand (F));
      end loop;
   end Get_Proof_Globals;

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

   ----------------------
   -- Get_Function_Set --
   ----------------------

   function Get_Function_Set (N : Node_Id) return Node_Sets.Set is
      NS : Node_Sets.Set := Node_Sets.Empty_Set;

      function Proc (N : Node_Id) return Traverse_Result;
      --  If the node being processed is an N_Function call, it adds
      --  the corresponding Flow_Id to FS.

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) = N_Function_Call then
            NS.Include (Entity (Name (N)));
         end if;

         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);

   begin
      Traverse (N);
      return NS;
   end Get_Function_Set;

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
      VS : Flow_Id_Sets.Set;

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
        with Pre => Nkind (Callsite) in N_Subprogram_Call;
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

      function Process_Subprogram_Call
        (Callsite : Node_Id)
         return Flow_Id_Sets.Set
      is
         Subprogram    : constant Entity_Id := Entity (Name (Callsite));

         Global_Reads  : Flow_Id_Sets.Set;
         Global_Writes : Flow_Id_Sets.Set;

         Folding       : constant Boolean :=
           Fold_Functions
           and then Ekind (Subprogram) = E_Function
           and then Has_Depends (Subprogram);

         Used_Reads    : Flow_Id_Sets.Set;

         V             : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      begin

         --  Determine the global effects of the called program.

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

         --  If we fold functions we need to obtain the used inputs.

         if Folding then
            declare
               Depends : Dependency_Maps.Map;
            begin
               Get_Depends (Subprogram => Subprogram,
                            Scope      => Scope,
                            Classwide  => Is_Dispatching_Call (Callsite),
                            Depends    => Depends);
               pragma Assert (Depends.Length in 1 .. 2);
               Used_Reads := Depends (Direct_Mapping_Id (Subprogram));
            end;
         end if;

         --  Apply sanity check for functions.

         if Nkind (Callsite) = N_Function_Call and then
           Flow_Id_Sets.Length (Global_Writes) > 0
         then
            Error_Msg_NE
              (Msg =>
                 "side-effects of function & are not modelled in SPARK",
               N   => Callsite,
               E   => Subprogram);
         end if;

         --  Merge globals into the variables used.

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

         --  Merge the actuals into the set of variables used.

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
                          Has_Extensions_Visible_Aspect (Subprogram) or else
                          Ekind (Get_Full_Type (Formal, Scope))
                            in Class_Wide_Kind));
               end if;

               Next (Ptr);
            end loop;
         end;

         --  Finally, we expand the collected set (if necessary).

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
                        if Expand_Synthesized_Constants and then
                          not Comes_From_Source (Entity (N))
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

                        else
                           --  If this constant comes from source, and
                           --  it's in Local_Constants, then add it.
                           if Local_Constants.Contains (Entity (N)) then
                              if Reduced then
                                 VS.Include (Direct_Mapping_Id
                                             (Unique_Entity (Entity (N))));
                              else
                                 VS.Union (Flatten_Variable (Entity (N),
                                                             Scope));
                              end if;
                           end if;

                        end if;

                     when E_Variable |
                       E_Loop_Parameter |
                       E_Out_Parameter |
                       E_In_Parameter |
                       E_In_Out_Parameter =>

                        if Reduced then
                           VS.Include (Direct_Mapping_Id
                                       (Unique_Entity (Entity (N))));
                        else
                           VS.Union (Flatten_Variable (Entity (N), Scope));
                        end if;
                        if Consider_Extensions and then
                          Extensions_Visible (Entity (N), Scope)
                        then
                           VS.Include (Direct_Mapping_Id
                                         (Unique_Entity (Entity (N)),
                                          Facet => Extension_Part));
                        end if;

                     when others =>
                        null;
                  end case;
               end if;

            when N_Defining_Identifier =>
               case Ekind (N) is
                  when E_Constant |
                    E_Variable |
                    E_Loop_Parameter |
                    E_Out_Parameter |
                    E_In_Parameter |
                    E_In_Out_Parameter =>
                     if Ekind (N) /= E_Constant or else
                       Local_Constants.Contains (N)
                     then
                        if Reduced then
                           VS.Include (Direct_Mapping_Id (Unique_Entity (N)));
                        else
                           VS.Union (Flatten_Variable (N, Scope));
                        end if;
                        if Consider_Extensions and then
                          Extensions_Visible (N, Scope)
                        then
                           VS.Include (Direct_Mapping_Id
                                         (Unique_Entity (N),
                                          Facet => Extension_Part));
                        end if;
                     end if;
                  when others =>
                     null;
               end case;

            when N_Aggregate =>
               VS.Union (Recurse_On (Aggregate_Bounds (N)));

            when N_Selected_Component =>

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

               elsif Ekind (Get_Full_Type (N, Scope)) in Record_Kind then

                  --  We use Untangle_Record_Assignment as this can deal
                  --  with view conversions.

                  declare
                     M : constant Flow_Id_Maps.Map :=
                       Untangle_Record_Assignment
                       (N,
                        Map_Root                     =>
                          Direct_Mapping_Id (Etype (N)),
                        Map_Type                     =>
                          Get_Full_Type (N, Scope),
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
                     if Reduced or Is_Tagged_Type (Get_Full_Type (N, Scope))
                     then
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
                     for F of Recurse_On (Prefix (N)) loop
                        if F.Kind in Direct_Mapping | Record_Field and then
                          F.Facet = Normal_Part and then
                          Has_Bounds (F, Scope)
                        then
                           --  This is not a bound variable, but it
                           --  requires bounds tracking. We make it a
                           --  bound variable.
                           VS.Include (F'Update (Facet => The_Bounds));

                        else
                           --  This is something else. We just copy it.
                           VS.Include (F);
                        end if;
                     end loop;
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

   begin --  Get_Variable_Set
      Traverse (N);
      return Filter_Out_Non_Local_Constants (VS, Local_Constants);
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

   --------------------
   -- Is_Null_Record --
   --------------------

   function Is_Null_Record (E : Entity_Id) return Boolean
   is
   begin
      if Is_Type (E) then
         if Ekind (E) in Record_Kind then
            case Ekind (E) is
               when E_Class_Wide_Type | E_Class_Wide_Subtype =>
                  --  We always have the tag.
                  return False;
               when others =>
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

      Contains_Non_Visible : Boolean := False;
   begin
      if Debug_Trace_Flatten then
         Write_Str ("Flatten: ");
         Print_Flow_Id (F);
         Indent;
      end if;

      if not (F.Kind in Direct_Mapping | Record_Field and then
                F.Facet = Normal_Part)
      then
         if Debug_Trace_Flatten then
            Outdent;
         end if;
         return Flow_Id_Sets.To_Set (F);
      end if;

      pragma Assert (Nkind (F.Node) in N_Entity);
      T         := Get_Type (F, Scope);
      Classwide := Ekind (T) in Class_Wide_Kind;
      if Classwide then
         T := Get_Full_Type (T, Scope);
         pragma Assert (Ekind (T) not in Class_Wide_Kind);
      end if;

      if Debug_Trace_Flatten then
         Write_Str ("Branching on type: ");
         Sprint_Node_Inline (T);
         Write_Str (" (" & Ekind (T)'Img & ")");
         Write_Eol;
      end if;

      case Ekind (T) is
         when E_Private_Type .. Private_Kind'Last =>
            if Debug_Trace_Flatten then
               Write_Str ("processing private type");
               Write_Eol;
            end if;

            if Has_Discriminants (T) then
               for Ptr of All_Components (T) loop
                  if Is_Visible (Original_Record_Component (Ptr), Scope) then
                     Ids.Include (Add_Component (F, Ptr));
                  end if;
               end loop;
               Ids.Include (F'Update (Facet => Private_Part));
            else
               Ids := Flow_Id_Sets.To_Set (F);
            end if;

         when Record_Kind =>
            if Debug_Trace_Flatten then
               Write_Str ("processing record type");
               Write_Eol;
            end if;

            --  this includes classwide types and privates with
            --  discriminants

            Ids := Flow_Id_Sets.Empty_Set;

            for Ptr of All_Components (T) loop
               if Is_Visible (Original_Record_Component (Ptr), Scope) then
                  Ids.Union (Flatten_Variable (Add_Component (F, Ptr),
                                               Scope));
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

            if Classwide then
               --  Ids.Include (F'Update (Facet => The_Tag));
               Ids.Include (F'Update (Facet => Extension_Part));
            end if;

         when others =>
            if Debug_Trace_Flatten then
               Write_Str ("processing misc type");
               Write_Eol;
            end if;

            Ids := Flow_Id_Sets.To_Set (F);
      end case;

      if Debug_Trace_Flatten then
         Outdent;
      end if;

      return Ids;
   end Flatten_Variable;

   -------------------
   -- Get_Full_Type --
   -------------------

   function Get_Full_Type
     (N     : Node_Id;
      Scope : Flow_Scope)
      return Entity_Id
   is
      T : Entity_Id := Etype (N);
   begin
      if Nkind (N) in N_Entity and then Ekind (N) = E_Abstract_State then
         return T;
      end if;

      while Present (Full_View (T))
        and then Is_Visible (Full_View (T), Scope)
        and then not Is_Itype (Full_View (T))
        and then Full_View (T) /= T
      loop
         T := Full_View (T);
      end loop;

      return T;
   end Get_Full_Type;

   --------------------------------
   -- Is_Valid_Assignment_Target --
   --------------------------------

   function Is_Valid_Assignment_Target (N : Node_Id) return Boolean
   is
      Ptr : Node_Id := N;
   begin
      while Nkind (Ptr) in Valid_Assignment_Kinds loop
         case Valid_Assignment_Kinds (Nkind (Ptr)) is
            when N_Identifier | N_Expanded_Name =>
               return True;
            when N_Type_Conversion =>
               Ptr := Expression (Ptr);
            when N_Unchecked_Type_Conversion =>
               --  We only allow `unchecked' conversions of scalars in
               --  assignment targets.
               if Ekind (Get_Full_Type_Without_Checking (Ptr)) not in
                 Scalar_Kind
               then
                  return False;
               end if;
               Ptr := Expression (Ptr);
               if Ekind (Get_Full_Type_Without_Checking (Ptr)) not in
                 Scalar_Kind
               then
                  return False;
               end if;
            when N_Indexed_Component | N_Slice | N_Selected_Component =>
               Ptr := Prefix (Ptr);
         end case;
      end loop;
      return False;
   end Is_Valid_Assignment_Target;

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

      --  First we turn the tree into a more helpful sequence. We also
      --  determine the root node which should be an entire variable.

      Seq := Node_Lists.Empty_List;
      while Nkind (Root_Node) in Interesting_Nodes loop
         Seq.Prepend (Root_Node);
         Root_Node := Prefix (Root_Node);
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
               --  We have only limited support for unchecked conversions
               --  here - we support conversions from scalars to scalars
               --  only. The assert here makes sure this assumption stays
               --  valid.
               declare
                  Typ_From : constant Entity_Id := Etype (Expression (N));
                  Typ_To   : constant Entity_Id := Etype (N);
               begin
                  pragma Assert (Ekind (Typ_From) in Scalar_Kind);
                  pragma Assert (Ekind (Typ_To)   in Scalar_Kind);
               end;

            when others =>
               Partial_Definition := True;
               Classwide          := False;
               exit;
         end case;
      end loop;
   end Get_Assignment_Target_Properties;

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
      --      which level of components (in the flow_id) we are looking at.
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
                              Vars_Defined.Include (F);
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
         when Subprogram_Kind =>
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

         when Magic_String | Synthetic_Null_Export =>
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
      pragma Assert (F.Kind in Direct_Mapping | Record_Field);
      E : constant Entity_Id := Get_Direct_Mapping_Id (F);
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return False;

         when others =>
            pragma Assert (Nkind (Parent (E)) = N_Object_Declaration);
            return Present (Expression (Parent (E)));

      end case;
   end Is_Initialized_In_Specification;

   --------------
   -- Add_Loop --
   --------------

   procedure Add_Loop (E : Entity_Id)
   is
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

   ----------------------
   -- Freeze_Loop_Info --
   ----------------------

   procedure Freeze_Loop_Info
   is
   begin
      pragma Assert (not Loop_Info_Frozen);
      Loop_Info_Frozen := True;
   end Freeze_Loop_Info;

   -----------------------
   -- Loop_Writes_Known --
   -----------------------

   function Loop_Writes_Known (E : Entity_Id) return Boolean
   is
   begin
      return Loop_Info_Frozen and then Loop_Info.Contains (E);
   end Loop_Writes_Known;

   ---------------------
   -- Get_Loop_Writes --
   ---------------------

   function Get_Loop_Writes (E : Entity_Id) return Flow_Id_Sets.Set
   is
   begin
      return Loop_Info (E);
   end Get_Loop_Writes;

   ------------------------
   -- Extensions_Visible --
   ------------------------

   function Extensions_Visible (E     : Entity_Id;
                                Scope : Flow_Scope)
                                return Boolean
   is
      T : constant Entity_Id := Get_Full_Type (E, Scope);
   begin
      return Ekind (E) in Formal_Kind
        and then Is_Tagged_Type (T)
        and then Ekind (T) not in Class_Wide_Kind
        and then Has_Extensions_Visible_Aspect (Sinfo.Scope (E));
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

   --------------------
   -- Search_Depends --
   --------------------

   function Search_Depends (Subprogram : Entity_Id;
                            Output     : Entity_Id;
                            Input      : Entity_Id := Empty)
                            return Node_Id
   is

      Depends_Contract : Node_Id;
      Needle           : Node_Id := Empty;

      function Proc (N : Node_Id) return Traverse_Result;
      --  Searches dependency aspect for export E and sets needle
      --  to the node, if found.

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
                                 when others =>
                                    raise Program_Error;
                              end case;
                              if I = Input then
                                 Needle := Tmp2;
                                 return Abandon;
                              end if;
                              Tmp2 := Next (Tmp2);
                           end loop;
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
            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Find_Export_Internal is new Traverse_Proc (Proc);

   begin
      declare
         Body_N : constant Node_Id :=
           (if Acts_As_Spec (SPARK_Util.Get_Subprogram_Body (Subprogram))
            then Subprogram
            else Get_Body (Subprogram));
      begin
         Depends_Contract := Get_Pragma (Body_N, Pragma_Refined_Depends);
      end;
      if No (Depends_Contract) then
         Depends_Contract := Get_Pragma (Subprogram, Pragma_Depends);
      end if;
      if No (Depends_Contract) then
         return Subprogram;
      end if;

      Find_Export_Internal (Depends_Contract);
      if Present (Needle) then
         return Needle;
      else
         return Subprogram;
      end if;
   end Search_Depends;

   --------------------
   -- All_Components --
   --------------------

   function All_Components (E : Entity_Id) return Node_Lists.List
   is
      Ptr : Entity_Id;
      T   : Entity_Id          := E;
      L   : Node_Lists.List    := Node_Lists.Empty_List;
      S   : Component_Sets.Set := Component_Sets.Empty_Set;

      function Up (E : Entity_Id) return Entity_Id;
      --  Get parent type, but don't consider record subtypes' ancestors.

      function Up (E : Entity_Id) return Entity_Id
      is
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

end Flow_Utility;
