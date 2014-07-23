------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012-2014, AdaCore                  --
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

with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Sem_Eval;               use Sem_Eval;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Uintp;                  use Uintp;

with SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util;             use SPARK_Util;

with Flow_Types;
with Flow_Utility;

with Why.Atree.Accessors;    use Why.Atree.Accessors;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Atree.Modules;      use Why.Atree.Modules;
with Why.Conversions;        use Why.Conversions;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Inter;              use Why.Inter;
with Why.Types;              use Why.Types;

with Gnat2Why.Expr;          use Gnat2Why.Expr;
with Gnat2Why.Nodes;         use Gnat2Why.Nodes;

package body Gnat2Why.Util is

   --------------------
   -- Ada_Ent_To_Why --
   --------------------

   package body Ada_Ent_To_Why is

      -------------
      -- Element --
      -------------

      function Element (M : Map; E : Entity_Id) return Item_Type is
      begin
         return M.Entity_Ids.Element (E);
      end Element;

      function Element (C : Cursor) return Item_Type is
      begin
         case C.Kind is
            when CK_Ent =>
               return Ent_To_Why.Element (C.Ent_Cursor);
            when CK_Str =>
               return Name_To_Why_Map.Element (C.Name_Cursor);
         end case;
      end Element;

      ----------
      -- Find --
      ----------

      function Find (M : Map; E : Entity_Id) return Cursor is
         C : constant Ent_To_Why.Cursor := M.Entity_Ids.Find (E);
      begin
         if Ent_To_Why.Has_Element (C) then
            return Cursor'(CK_Ent,
                           C,
                           Name_To_Why_Map.No_Element);
         else
            return Cursor'(CK_Ent, Ent_To_Why.No_Element,
                           Name_To_Why_Map.No_Element);
         end if;
      end Find;

      function Find (M : Map; E : Entity_Name) return Cursor is
         C : constant Name_To_Why_Map.Cursor := M.Entity_Names.Find (E);
      begin
         if Name_To_Why_Map.Has_Element (C) then
            return Cursor'(CK_Str, Ent_To_Why.No_Element,
                           C);
         else
            declare
               Ent : constant Entity_Id := Find_Entity (E);
            begin
               if Present (Ent) then
                  return Find (M, Ent);
               else
                  return Cursor'(CK_Ent, Ent_To_Why.No_Element,
                                 Name_To_Why_Map.No_Element);
               end if;
            end;
         end if;
      end Find;

      -----------------
      -- Has_Element --
      -----------------

      function Has_Element (M : Map; E : Entity_Id) return Boolean
      is
      begin
         return M.Entity_Ids.Contains (E);
      end Has_Element;

      function Has_Element (C : Cursor) return Boolean
      is
      begin
         case C.Kind is
            when CK_Ent =>
               return Ent_To_Why.Has_Element (C.Ent_Cursor);
            when CK_Str =>
               return Name_To_Why_Map.Has_Element (C.Name_Cursor);
         end case;
      end Has_Element;

      ------------
      -- Insert --
      ------------

      procedure Insert (M : in out Map;
                        E : Entity_Id;
                        W : Item_Type)
      is
         C : Ent_To_Why.Cursor;
         Inserted : Boolean;
      begin
         M.Entity_Ids.Insert (E, W, C, Inserted);
         if Undo_Stacks.Is_Empty (M.Undo_Stack) then

            --  At the global level (no undo stack) we expect that there are no
            --  clashes in symbols

            pragma Assert (Inserted);
         else
            if Inserted then
               M.Undo_Stack.Append (Action'(Remove_Ent, E));
            else

               --  If there was already an entry for the entity, we need to
               --  store in the undo stack the fact that this info must be
               --  reinserted

               M.Undo_Stack.Append
                 (Action'(Kind       => Insert_Ent,
                          Ins_Entity => Ent_To_Why.Key (C),
                          Ins_Binder => Ent_To_Why.Element (C)));
               M.Entity_Ids.Replace (E, W);
               M.Undo_Stack.Append (Action'(Remove_Ent, E));
            end if;
         end if;
      end Insert;

      procedure Insert (M : in out Map;
                        E : Entity_Name;
                        W : Item_Type) is
         C : Name_To_Why_Map.Cursor;
         Inserted : Boolean;
      begin
         M.Entity_Names.Insert (E, W, C, Inserted);
         if Undo_Stacks.Is_Empty (M.Undo_Stack) then

            --  At the global level (no undo stack) we expect that there are no
            --  clashes in symbols

            pragma Assert (Inserted);
         else
            if Inserted then
               M.Undo_Stack.Append (Action'(Remove_Name, E));
            else

               --  If there was already an entry for the name, we need to
               --  store in the undo stack the fact that this info must be
               --  reinserted

               M.Undo_Stack.Append
                 (Action'(Kind => Insert_Name,
                          Ins_Name => Name_To_Why_Map.Key (C),
                          Ins_Binder => Name_To_Why_Map.Element (C)));
               M.Entity_Names.Replace (E, W);
               M.Undo_Stack.Append (Action'(Remove_Name, E));
            end if;
         end if;
      end Insert;

      ---------------
      -- Pop_Scope --
      ---------------

      procedure Pop_Scope (M : in out Map) is

         procedure Apply_Action (C : Undo_Stacks.Cursor);
         --  apply a single action

         ------------------
         -- Apply_Action --
         ------------------

         procedure Apply_Action (C : Undo_Stacks.Cursor) is
            A : constant Action := Undo_Stacks.Element (C);
         begin
            case A.Kind is
               when Insert_Ent =>
                  M.Entity_Ids.Include (A.Ins_Entity, A.Ins_Binder);
               when Insert_Name =>
                  M.Entity_Names.Include (A.Ins_Name, A.Ins_Binder);
               when Remove_Ent =>
                  M.Entity_Ids.Delete (A.Rem_Entity);
               when Remove_Name =>
                  M.Entity_Names.Delete (A.Rem_Name);
               when Boundary =>
                  raise Program_Error;
            end case;
         end Apply_Action;

         C : Undo_Stacks.Cursor := M.Undo_Stack.Last;
         Tmp : Undo_Stacks.Cursor;

      begin
         while Undo_Stacks.Has_Element (C) and then
           Undo_Stacks.Element (C).Kind /= Boundary loop
            Apply_Action (C);
            Tmp := C;
            Undo_Stacks.Previous (C);
            M.Undo_Stack.Delete (Tmp);
         end loop;

         --  we still need to delete the boundary marker, if it exists

         if Undo_Stacks.Has_Element (C) then
            M.Undo_Stack.Delete (C);
         end if;
      end Pop_Scope;

      ----------------
      -- Push_Scope --
      ----------------

      procedure Push_Scope (M : in out Map) is
      begin
         M.Undo_Stack.Append (Action'(Kind => Boundary));
      end Push_Scope;

   end Ada_Ent_To_Why;

   -------------------------------------
   -- Expression_Depends_On_Variables --
   -------------------------------------

   function Expression_Depends_On_Variables (N : Node_Id) return Boolean is

      Variable_Reference_Seen : Boolean := False;

      function Is_Variable_Reference (N : Node_Id) return Traverse_Result;
      --  Attempt to find a variable reference in N

      procedure Search_Variable_Reference is
        new Traverse_Proc (Is_Variable_Reference);

      ---------------------------
      -- Is_Variable_Reference --
      ---------------------------

      function Is_Variable_Reference (N : Node_Id) return Traverse_Result is
      begin
         if Nkind_In (N, N_Identifier, N_Expanded_Name)
           and then Present (Entity (N))
           and then
             (case Ekind (Entity (N)) is
                 when Object_Kind     => Is_Mutable_In_Why (Entity (N)),
                 when Subprogram_Kind =>
                    Flow_Utility.Has_Proof_Global_Reads (Entity (N)),
                 when others          => False)
         then
            Variable_Reference_Seen := True;
            return Abandon;

         --  Continue the traversal

         else
            return OK;
         end if;
      end Is_Variable_Reference;

   begin
      Search_Variable_Reference (N);
      return Variable_Reference_Seen;
   end Expression_Depends_On_Variables;

   ------------------
   -- Compute_Spec --
   ------------------

   function Compute_Spec
     (Params : Transformation_Params;
      Nodes  : Node_Lists.List;
      Domain : EW_Domain) return W_Expr_Id
   is
      Cur_Spec : W_Expr_Id := Why_Empty;
   begin
      if Nodes.Is_Empty then
         return New_Literal (Value => EW_True, Domain => Domain);
      end if;

      for Node of Nodes loop
         declare
            Why_Expr : constant W_Expr_Id :=
              Transform_Expr (Node, EW_Bool_Type, Domain, Params);
         begin
            if Cur_Spec /= Why_Empty then
               Cur_Spec :=
                 New_And_Then_Expr
                   (Left   => Why_Expr,
                    Right  => Cur_Spec,
                    Domain => Domain);
            else
               Cur_Spec := Why_Expr;
            end if;
         end;
      end loop;

      return Cur_Spec;
   end Compute_Spec;

   function Compute_Spec
     (Params    : Transformation_Params;
      E         : Entity_Id;
      Kind      : Name_Id;
      Domain    : EW_Domain;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return W_Expr_Id
   is
      Nodes : constant Node_Lists.List :=
        Find_Contracts (E, Kind, Classwide, Inherited);
   begin
      return Compute_Spec (Params, Nodes, Domain);
   end Compute_Spec;

   -------------------------
   -- Create_Zero_Binding --
   -------------------------

   function Create_Zero_Binding
     (Vars : Why_Node_Lists.List;
      Prog : W_Prog_Id) return W_Prog_Id
   is
      Result   : W_Prog_Id;
   begin
      Result := Prog;
      for V of Vars loop
         Result :=
           New_Binding_Ref (Name     => W_Identifier_Id (V),
                            Def      => New_Integer_Constant (Value => Uint_0),
                            Context  => Result);
      end loop;
      return Result;
   end Create_Zero_Binding;

   ------------------------------
   -- Get_Dispatching_Contract --
   ------------------------------

   function Get_Dispatching_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Name_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Conjuncts_List : Node_Lists.List :=
        Find_Contracts (E, Kind, Classwide => True);
   begin
      if Conjuncts_List.Is_Empty then
         Conjuncts_List := Find_Contracts
           (E, Kind, Classwide => True, Inherited => True);
      end if;

      return +Compute_Spec (Params, Conjuncts_List, Domain);
   end Get_Dispatching_Contract;

   function Get_Dispatching_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Name_Id) return W_Pred_Id is
   begin
      return +Get_Dispatching_Contract (Params, E, Kind, EW_Pred);
   end Get_Dispatching_Contract;

   ------------------------------
   -- Get_Static_Call_Contract --
   ------------------------------

   function Get_Static_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Name_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Conjuncts_List : constant Node_Lists.List := Find_Contracts (E, Kind);
   begin
      if Conjuncts_List.Is_Empty then
         return Get_Dispatching_Contract (Params, E, Kind, Domain);
      end if;

      return +Compute_Spec (Params, Conjuncts_List, Domain);
   end Get_Static_Call_Contract;

   function Get_Static_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Name_Id) return W_Pred_Id is
   begin
      return +Get_Static_Call_Contract (Params, E, Kind, EW_Pred);
   end Get_Static_Call_Contract;

   --------------------
   -- Init_Why_Files --
   --------------------

   procedure Init_Why_Sections is
      Body_Prefix : constant String := Unit_Name;
   begin
      Why_File_Name := new String'(Body_Prefix & Why_File_Suffix);
      for Kind in Why_Section_Enum'First ..
                  Why_Section_Enum'Pred (Why_Section_Enum'Last)
      loop
         Why_Sections (Kind) :=
           Make_Empty_Why_Section (Kind => Kind);
      end loop;
      Why_Sections (WF_Main) := Make_Empty_Why_Section (Kind => WF_Main);
   end Init_Why_Sections;

   -------------------
   -- Insert_Entity --
   -------------------

   procedure Insert_Entity (E       : Entity_Id;
                            Name    : W_Identifier_Id;
                            Mutable : Boolean := False) is
   begin
      Ada_Ent_To_Why.Insert (Symbol_Table,
                             E,
                             Item_Type'(Regular,
                               Binder_Type'(
                                 B_Name   => Name,
                                 B_Ent    => null,
                                 Ada_Node => E,
                                 Mutable  => Mutable)));
   end Insert_Entity;

   -----------------
   -- Insert_Item --
   -----------------

   procedure Insert_Item (E : Entity_Id; I : Item_Type) is
   begin
      Ada_Ent_To_Why.Insert (Symbol_Table, E, I);
   end Insert_Item;

   -------------------------
   -- Make_Empty_Why_File --
   -------------------------

   function Make_Empty_Why_Section (Kind : Why_Section_Enum)
                                    return Why_Section is
   begin
      return Why_Section'(File       => New_File,
                          Kind       => Kind,
                          Cur_Theory => Why.Types.Why_Empty);
   end Make_Empty_Why_Section;

   --------------------------------
   -- Is_Locally_Defined_In_Loop --
   --------------------------------

   function Is_Locally_Defined_In_Loop (N : Node_Id) return Boolean is
      Stmt : Node_Id := Parent (N);
   begin
      while Present (Stmt) loop
         if Nkind (Stmt) = N_Loop_Statement then
            return True;

         elsif Is_Body_Or_Package_Declaration (Stmt) then
            return False;
         end if;

         Stmt := Parent (Stmt);
      end loop;

      return False;
   end Is_Locally_Defined_In_Loop;

   -----------------------
   -- Is_Mutable_In_Why --
   -----------------------

   function Is_Mutable_In_Why (N : Node_Id) return Boolean is
   begin
      --  A variable is translated as mutable in Why if it is not constant on
      --  the Ada side, or if it is a loop parameter (of an actual loop, not a
      --  quantified expression).

      if Ekind (N) = E_Loop_Parameter then
         return not (Is_Quantified_Loop_Param (N));

      --  A component or discriminant is not separately considered as mutable,
      --  only the enclosing object is. This ensures that components used in
      --  the named notation of aggregates are not considered as references
      --  to mutable variables (e.g. in Expression_Depends_On_Variables).

      elsif Ekind (N) in E_Enumeration_Literal |
                         E_Component           |
                         E_Discriminant        |
                         Named_Kind            |
                         Subprogram_Kind
      then
         return False;

      --  Constants defined locally to a loop inside a subprogram (or any
      --  other dynamic scope) may end up having different values, so should
      --  be mutable in Why, except when they are defined inside "actions" (in
      --  which case they are defined as local "let" bound variables in Why).

      elsif Ekind (N) = E_Constant
        and then SPARK_Definition.Loop_Entity_Set.Contains (N)
        and then not SPARK_Definition.Actions_Entity_Set.Contains (N)
      then
         return True;

      --  We special case any volatile with async writers: they are always
      --  mutable (even if they are, for example, in parameters).

      elsif Flow_Types.Has_Async_Writers
        (Flow_Types.Direct_Mapping_Id (N))
      then

         return True;

      elsif Is_Constant_Object (N) then
         return False;

      else
         return True;
      end if;
   end Is_Mutable_In_Why;

   ------------------------------------
   -- Type_Is_Modeled_As_Int_Or_Real --
   ------------------------------------

   function Type_Is_Modeled_As_Int_Or_Real (T : Entity_Id) return Boolean is
   begin
      return SPARK_Definition.Loop_Entity_Set.Contains (T)
        and then not Is_Static_Subtype (T);
   end Type_Is_Modeled_As_Int_Or_Real;

   ------------------------
   -- Why_Type_Of_Entity --
   ------------------------

   function Why_Type_Of_Entity (E : Entity_Id) return W_Type_Id is
      Binder : constant Item_Type := Ada_Ent_To_Why.Element (Symbol_Table, E);
   begin
      case Binder.Kind is
      when Regular =>
         return Get_Typ (Binder.Main.B_Name);
      when UCArray =>
         return Get_Typ (Binder.Content.B_Name);
      when Func =>
         return Get_Typ (Binder.For_Logic.B_Name);
      when DRecord =>
         return EW_Abstract (Binder.Typ);
      end case;
   end Why_Type_Of_Entity;

end Gnat2Why.Util;
