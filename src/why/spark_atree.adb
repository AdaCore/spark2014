------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          S P A R K _ A T R E E                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2025, AdaCore                     --
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

with Einfo.Utils;
with Nlists;  use Nlists;
with Sem_Disp;
with SPARK_Util.Types;
with Stringt; use Stringt;

package body SPARK_Atree is

   -------------
   -- Actions --
   -------------

   function Actions (N : Node_Id) return List_Id renames Sinfo.Nodes.Actions;

   ----------------------
   -- Aggregate_Bounds --
   ----------------------

   function Aggregate_Bounds (N : Node_Id) return Node_Id
   is (Sinfo.Utils.Aggregate_Bounds (N));

   -----------------
   -- All_Present --
   -----------------

   function All_Present (N : Node_Id) return Boolean
   renames Sinfo.Nodes.All_Present;

   ------------------
   -- Alternatives --
   ------------------

   function Alternatives (N : Node_Id) return List_Id
   renames Sinfo.Nodes.Alternatives;

   -------------------
   -- Ancestor_Part --
   -------------------

   function Ancestor_Part (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Ancestor_Part (N));

   ----------------------------------------
   -- Attribute_Constrained_Static_Value --
   ----------------------------------------

   function Attribute_Constrained_Static_Value (N : Node_Id) return Boolean
   renames Exp_Util.Attribute_Constrained_Static_Value;

   --------------------
   -- Attribute_Name --
   --------------------

   function Attribute_Name (N : Node_Id) return Name_Id
   is (Sinfo.Nodes.Attribute_Name (N));

   -----------------
   -- Box_Present --
   -----------------

   function Box_Present (N : Node_Id) return Boolean
   renames Sinfo.Nodes.Box_Present;

   ------------------------
   -- Char_Literal_Value --
   ------------------------

   function Char_Literal_Value (N : Node_Id) return Uint
   is (Sinfo.Nodes.Char_Literal_Value (N));

   -----------
   -- Chars --
   -----------

   function Chars (N : Node_Id) return Name_Id
   is (Sinfo.Nodes.Chars (N));

   -----------------
   -- Choice_List --
   -----------------

   function Choice_List (N : Node_Id) return List_Id
   renames Sem_Util.Choice_List;

   ----------------------------
   -- Component_Associations --
   ----------------------------

   function Component_Associations (N : Node_Id) return List_Id
   renames Sinfo.Nodes.Component_Associations;

   --------------------------
   -- Component_Definition --
   --------------------------

   function Component_Definition (N : Node_Id) return Node_Id
   renames Sinfo.Nodes.Component_Definition;

   ----------------------------------
   -- Component_Subtype_Indication --
   ----------------------------------

   function Component_Subtype_Indication (N : Node_Id) return Node_Id
   is (if Nkind (N) = N_Full_Type_Declaration
         and then Nkind (Type_Definition (N))
                  in N_Constrained_Array_Definition
                   | N_Unconstrained_Array_Definition
       then
         Sinfo.Nodes.Subtype_Indication
           (Sinfo.Nodes.Component_Definition (Sinfo.Nodes.Type_Definition (N)))
       else Empty);

   ---------------
   -- Condition --
   ---------------

   function Condition (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Condition (N));

   -----------------------
   -- Condition_Actions --
   -----------------------

   function Condition_Actions (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Condition_Actions (N));

   -------------------
   -- Context_Items --
   -------------------

   function Context_Items (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Context_Items (N));

   --------------------------
   -- Controlling_Argument --
   --------------------------

   function Controlling_Argument (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Controlling_Argument (N));

   ---------------------------------
   -- Corresponding_Integer_Value --
   ---------------------------------

   function Corresponding_Integer_Value (N : Node_Id) return Uint
   is (Sinfo.Nodes.Corresponding_Integer_Value (N));

   ------------------
   -- Declarations --
   ------------------

   function Declarations (N : Node_Id) return List_Id
   renames Sinfo.Nodes.Declarations;

   -----------------------------
   -- Depends_On_Discriminant --
   -----------------------------

   function Depends_On_Discriminant (N : Node_Id) return Boolean
   renames Sem_Util.Depends_On_Discriminant;

   ----------------------
   -- Discrete_Choices --
   ----------------------

   function Discrete_Choices (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Discrete_Choices (N));

   --------------------
   -- Discrete_Range --
   --------------------

   function Discrete_Range (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Discrete_Range (N));

   ---------------------------------
   -- Discrete_Subtype_Definition --
   ---------------------------------

   function Discrete_Subtype_Definition (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Discrete_Subtype_Definition (N));

   -----------------------------------
   -- Do_Check_On_Scalar_Conversion --
   -----------------------------------

   function Do_Check_On_Scalar_Conversion (N : Node_Id) return Boolean is
   begin
      return
        Sinfo.Nodes.Do_Range_Check (N)
        or else (Sinfo.Nodes.Nkind (Atree.Parent (N)) = N_Type_Conversion
                 and then Sinfo.Nodes.Do_Overflow_Check (Atree.Parent (N)))
        or else (Sinfo.Nodes.Nkind (N) = N_Type_Conversion
                 and then Sinfo.Nodes.Do_Range_Check
                            (Sinfo.Nodes.Expression (N))
                 and then Sinfo.Nodes.Nkind (Atree.Parent (N))
                          in N_Parameter_Association
                           | N_Procedure_Call_Statement
                           | N_Entry_Call_Statement
                 and then Einfo.Entities.Ekind
                            (SPARK_Util.Get_Formal_From_Actual (N))
                          in Einfo.Entities.E_In_Out_Parameter
                           | Einfo.Entities.E_Out_Parameter)
        or else (Sinfo.Nodes.Nkind (Atree.Parent (N)) = N_Range
                 and then Sinfo.Nodes.Do_Range_Check (Atree.Parent (N)))

        --  Do_Range_Check flag is not set on allocators. Do the check if the
        --  designated subtype and the provided subtype do not match.
        --  For uninitialized allocators, N is the allocator node itself.

        or else (Sinfo.Nodes.Nkind (N) = N_Allocator
                 and then Einfo.Entities.Directly_Designated_Type
                            (if Present (Einfo.Entities.Full_View (Etype (N)))
                             then Einfo.Entities.Full_View (Etype (N))
                             else Etype (N))
                          /= Entity (Expression (N)))

        --  On initialized allocators, it is the allocated expression, so the
        --  allocator is its parent.

        or else (Sinfo.Nodes.Nkind (Atree.Parent (N)) = N_Allocator
                 and then Einfo.Entities.Directly_Designated_Type
                            (if Present
                                  (Einfo.Entities.Full_View
                                     (Etype (Atree.Parent (N))))
                             then
                               Einfo.Entities.Full_View
                                 (Etype (Atree.Parent (N)))
                             else Etype (Atree.Parent (N)))
                          /= Etype (N));
   end Do_Check_On_Scalar_Conversion;

   -----------------------
   -- Do_Division_Check --
   -----------------------

   function Do_Division_Check (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Do_Division_Check (N));

   -----------------------
   -- Do_Overflow_Check --
   -----------------------

   function Do_Overflow_Check (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Do_Overflow_Check (N));

   --------------------
   -- Do_Range_Check --
   --------------------

   function Do_Range_Check (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Do_Range_Check (N));

   ------------------
   -- Else_Actions --
   ------------------

   function Else_Actions (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Else_Actions (N));

   ---------------------
   -- Else_Statements --
   ---------------------

   function Else_Statements (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Else_Statements (N));

   -----------------
   -- Elsif_Parts --
   -----------------

   function Elsif_Parts (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Elsif_Parts (N));

   ------------------------------
   -- Enclosing_Comp_Unit_Node --
   ------------------------------

   function Enclosing_Comp_Unit_Node (N : Node_Id) return Node_Id
   renames Sem_Util.Enclosing_Comp_Unit_Node;

   -------------------------
   -- Enclosing_Statement --
   -------------------------

   function Enclosing_Statement (N : Node_Id) return Node_Id
   renames Atree.Parent;

   ------------
   -- Entity --
   ------------

   function Entity (N : Node_Id) return Node_Id
   is (Sinfo.Utils.Entity (N));

   ------------------------
   -- Entry_Body_Barrier --
   ------------------------

   function Entry_Body_Barrier (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Condition (Sinfo.Nodes.Entry_Body_Formal_Part (N)));

   -----------
   -- Etype --
   -----------

   function Etype (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Etype (N));

   ----------------
   -- Expr_Value --
   ----------------

   function Expr_Value (N : Node_Id) return Uint renames Sem_Eval.Expr_Value;

   ------------------
   -- Expr_Value_R --
   ------------------

   function Expr_Value_R (N : Node_Id) return Ureal
   renames Sem_Eval.Expr_Value_R;

   ----------------
   -- Expression --
   ----------------

   function Expression (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Expression (N));

   -------------------------------------------
   -- Expression_Contains_Old_Or_Loop_Entry --
   -------------------------------------------

   function Expression_Contains_Old_Or_Loop_Entry
     (Expr : Node_Id) return Boolean
   is
      use type Atree.Traverse_Result;

      function Search_Old_Or_Loop_Entry
        (N : Node_Id) return Atree.Traverse_Result;
      --  Search for attribute old or loop_entry

      ------------------------------
      -- Search_Old_Or_Loop_Entry --
      ------------------------------

      function Search_Old_Or_Loop_Entry
        (N : Node_Id) return Atree.Traverse_Result is
      begin
         if Nkind (N) = N_Attribute_Reference
           and then Attribute_Name (N) in Name_Loop_Entry | Name_Old
         then
            --  There is no need to continue the traversal, as one such
            --  attribute suffices.

            return Atree.Abandon;
         end if;

         return Atree.OK;
      end Search_Old_Or_Loop_Entry;

      function Search_Attrs is new
        Sem_Util.Traverse_More_Func (Search_Old_Or_Loop_Entry);

      --  Start of processing for Expression_Contains_Old_Or_Loop_Entry

   begin
      return Search_Attrs (Expr) = Atree.Abandon;
   end Expression_Contains_Old_Or_Loop_Entry;

   -----------------
   -- Expressions --
   -----------------

   function Expressions (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Expressions (N));

   -------------------------------
   -- From_Aspect_Specification --
   -------------------------------

   function From_Aspect_Specification (N : Node_Id) return Boolean
   is (Sinfo.Nodes.From_Aspect_Specification (N));

   ----------------------
   -- Get_Address_Expr --
   ----------------------

   function Get_Address_Expr (N : Node_Id) return Node_Id is
      Address : constant Node_Id :=
        Einfo.Utils.Address_Clause (Sem_Util.Defining_Entity (N));
   begin
      if Present (Address) then
         return Sinfo.Nodes.Expression (Address);
      else
         return Empty;
      end if;
   end Get_Address_Expr;

   -----------------------
   -- Get_Called_Entity --
   -----------------------

   function Get_Called_Entity (N : Node_Id) return Entity_Id
   is (if Nkind (N) in N_Op
       then Entity (N)
       else Sem_Aux.Get_Called_Entity (N));

   -----------------------
   -- Get_Entire_Object --
   -----------------------

   function Get_Entire_Object (N : Node_Id) return Entity_Id is
   begin
      if Einfo.Utils.Is_Entity_Name (N) then
         return Entity (N);
      else
         case Nkind (N) is
            when N_Explicit_Dereference
               | N_Indexed_Component
               | N_Selected_Component
               | N_Slice
            =>
               return Get_Entire_Object (Prefix (N));

            when N_Type_Conversion | N_Unchecked_Type_Conversion =>
               return Get_Entire_Object (Expression (N));

            when others =>
               return Empty;
         end case;
      end if;
   end Get_Entire_Object;

   -------------------
   -- Get_Pragma_Id --
   -------------------

   function Get_Pragma_Id (N : Node_Id) return Pragma_Id
   renames Sem_Util.Get_Pragma_Id;

   --------------------------
   -- Get_Range_Check_Info --
   --------------------------

   function Get_Range_Check_Info
     (N : Node_Id) return SPARK_Util.Scalar_Check_Kind
   is
      Typ : constant Entity_Id := SPARK_Util.Types.Retysp (Etype (N));
      Par : Node_Id := Atree.Parent (N);

   begin
      --  For uninitialized allocators, N is not a scalar expression but
      --  the allocator itself.

      if Nkind (N) = N_Allocator then
         Par := N;
      end if;

      --  Access to components in arrays are index checks

      if Nkind (Par) = N_Indexed_Component then
         return SPARK_Util.RCK_Index;

      --  If the target type is a constrained array, we have a length check

      elsif Einfo.Utils.Is_Array_Type (Typ)
        and then Einfo.Entities.Is_Constrained (Typ)
      then
         return SPARK_Util.RCK_Length;

      --  Otherwise, this is a range check

      else
         return SPARK_Util.RCK_Range;
      end if;
   end Get_Range_Check_Info;

   -----------------------
   -- Get_Return_Object --
   -----------------------

   function Get_Return_Object (N : Node_Id) return Entity_Id
   renames Sem_Util.Get_Return_Object;

   --------------------------------
   -- Handled_Statement_Sequence --
   --------------------------------

   function Handled_Statement_Sequence (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Handled_Statement_Sequence (N));

   ----------------------
   -- Has_Target_Names --
   ----------------------

   function Has_Target_Names (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Has_Target_Names (N));

   ---------------------------------
   -- Has_Inferable_Discriminants --
   ---------------------------------

   function Has_Inferable_Discriminants (N : Node_Id) return Boolean
   renames Sem_Util.Has_Inferable_Discriminants;

   ------------------------
   -- Has_Wide_Character --
   ------------------------

   --  We cannot use directly Sinfo.Has_Wide_Character which is not set for
   --  string literals not from source, say created as a result of inlining.

   function Has_Wide_Character (N : Node_Id) return Boolean is
      S : constant String_Id := Strval (N);
   begin
      for J in 1 .. String_Length (S) loop
         declare
            Code : constant Char_Code := Get_String_Char (S, J);
         begin
            if not In_Character_Range (Code)
              and then In_Wide_Character_Range (Code)
            then
               return True;
            end if;
         end;
      end loop;
      return False;
   end Has_Wide_Character;

   -----------------------------
   -- Has_Wide_Wide_Character --
   -----------------------------

   --  We cannot use directly Sinfo.Has_Wide_Wide_Character which is not
   --  set for string literals not from source, say created as a result
   --  of inlining.

   function Has_Wide_Wide_Character (N : Node_Id) return Boolean is
      S : constant String_Id := Strval (N);
   begin
      for J in 1 .. String_Length (S) loop
         declare
            Code : constant Char_Code := Get_String_Char (S, J);
         begin
            if not In_Wide_Character_Range (Code) then
               return True;
            end if;
         end;
      end loop;
      return False;
   end Has_Wide_Wide_Character;

   ----------------
   -- High_Bound --
   ----------------

   function High_Bound (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.High_Bound (N));

   ----------------
   -- Identifier --
   ----------------

   function Identifier (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Identifier (N));

   ----------------------------
   -- Inherited_Discriminant --
   ----------------------------

   function Inherited_Discriminant (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Inherited_Discriminant (N));

   ------------
   -- Intval --
   ------------

   function Intval (N : Node_Id) return Uint
   is (Sinfo.Nodes.Intval (N));

   ---------------------------------------------
   -- Is_Choice_Of_Unconstrained_Array_Update --
   ---------------------------------------------

   function Is_Choice_Of_Unconstrained_Array_Update
     (N : Node_Id) return Boolean
   is
      Possibly_Choice_Node, Prefix_Node : Node_Id;
   begin
      if Nkind (Atree.Parent (N)) = N_Component_Association then
         Possibly_Choice_Node := N;
      elsif Nkind (Atree.Parent (N)) = N_Range
        and then Nkind (Atree.Parent (Atree.Parent (N)))
                 = N_Component_Association
      then
         Possibly_Choice_Node := Atree.Parent (N);
      else
         return False;
      end if;

      if Nkind (Atree.Parent (Atree.Parent (Possibly_Choice_Node)))
        = N_Aggregate
      then
         declare
            Attribute_Node : constant Node_Id :=
              Atree.Parent
                (Atree.Parent (Atree.Parent (Possibly_Choice_Node)));
         begin
            if Sem_Util.Is_Attribute_Update (Attribute_Node) then
               Prefix_Node := Prefix (Attribute_Node);
            else
               return False;
            end if;
         end;
      elsif Nkind (Atree.Parent (Atree.Parent (Possibly_Choice_Node)))
        = N_Delta_Aggregate
      then
         Prefix_Node :=
           Expression (Atree.Parent (Atree.Parent (Possibly_Choice_Node)));
      else
         return False;
      end if;

      if Einfo.Utils.Is_Array_Type (Etype (Prefix_Node))
        and then not Einfo.Entities.Is_Constrained (Etype (Prefix_Node))
        and then Is_List_Member (Possibly_Choice_Node)
        and then Present (Choice_List (Atree.Parent (Possibly_Choice_Node)))
        and then List_Containing (Possibly_Choice_Node)
                 = Choice_List (Atree.Parent (Possibly_Choice_Node))
      then
         return True;
      else
         return False;
      end if;
   end Is_Choice_Of_Unconstrained_Array_Update;

   ----------------------------
   -- Is_Component_Left_Opnd --
   ----------------------------

   function Is_Component_Left_Opnd (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Is_Component_Left_Opnd (N));

   -----------------------------
   -- Is_Component_Right_Opnd --
   -----------------------------

   function Is_Component_Right_Opnd (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Is_Component_Right_Opnd (N));

   ---------------------------
   -- Is_Controlling_Actual --
   ---------------------------

   function Is_Controlling_Actual (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Is_Controlling_Actual (N));

   -----------------
   -- Is_In_Range --
   -----------------

   function Is_In_Range (N : Node_Id; Typ : Entity_Id) return Boolean
   is (Sem_Eval.Is_In_Range (N, Typ, Assume_Valid => True));

   ----------------------------
   -- Is_Iterator_Over_Array --
   ----------------------------

   function Is_Iterator_Over_Array (N : Node_Id) return Boolean
   renames Sem_Util.Is_Iterator_Over_Array;

   -----------------------
   -- Is_Null_Aggregate --
   -----------------------

   function Is_Null_Aggregate (N : Node_Id) return Boolean
   renames Sem_Aggr.Is_Null_Aggregate;

   -----------------------------
   -- Is_OK_Static_Expression --
   -----------------------------

   function Is_OK_Static_Expression (N : Node_Id) return Boolean
   renames Sem_Eval.Is_OK_Static_Expression;

   ------------------------
   -- Is_OK_Static_Range --
   ------------------------

   function Is_OK_Static_Range (N : Node_Id) return Boolean
   renames Sem_Eval.Is_OK_Static_Range;

   ------------------------
   -- Is_Rewritten_Op_Eq --
   ------------------------

   function Is_Rewritten_Op_Eq (N : Node_Id) return Boolean
   is (Nkind (N) = N_Function_Call
       and then Nkind (Original_Node (N)) in N_Op_Eq | N_Op_Ne);

   --------------------------
   -- Is_Static_Expression --
   --------------------------

   function Is_Static_Expression (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Is_Static_Expression (N));

   --------------------------
   -- Is_Tag_Indeterminate --
   --------------------------

   function Is_Tag_Indeterminate (N : Node_Id) return Boolean
   renames Sem_Disp.Is_Tag_Indeterminate;

   ----------------------
   -- Is_Type_Renaming --
   ----------------------

   function Is_Type_Renaming (Decl : Node_Id) return Boolean is

      function Cstr_Subtype_Indication (N : Node_Id) return Boolean;
      --  Returns whether the subtype indication for node N (which may
      --  be a subtype declaration or a derived type definition) has a
      --  constraint.

      -----------------------------
      -- Cstr_Subtype_Indication --
      -----------------------------

      function Cstr_Subtype_Indication (N : Node_Id) return Boolean
      is (Nkind (Subtype_Indication (N)) = N_Subtype_Indication);

   begin
      case Nkind (Decl) is
         when N_Subtype_Declaration =>
            return not Cstr_Subtype_Indication (Decl);

         when N_Full_Type_Declaration =>
            if Nkind (Type_Definition (Decl)) = N_Derived_Type_Definition then
               declare
                  Def : constant Node_Id := Type_Definition (Decl);
               begin
                  return
                    No (Sinfo.Nodes.Record_Extension_Part (Def))
                    and then not Cstr_Subtype_Indication (Def);
               end;
            else
               return False;
            end if;

         when others =>
            raise Program_Error;
      end case;
   end Is_Type_Renaming;

   -----------------
   -- Is_Variable --
   -----------------

   function Is_Variable (N : Node_Id) return Boolean
   is (Sem_Util.Is_Variable (N));

   ----------------------
   -- Iteration_Scheme --
   ----------------------

   function Iteration_Scheme (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Iteration_Scheme (N));

   ---------------------
   -- Iterator_Filter --
   ---------------------

   function Iterator_Filter (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Iterator_Filter (N));

   ----------------------------
   -- Iterator_Specification --
   ----------------------------

   function Iterator_Specification (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Iterator_Specification (N));

   -----------
   -- Itype --
   -----------

   function Itype (N : Node_Id) return Entity_Id
   is (Sinfo.Nodes.Itype (N));

   ---------------
   -- Left_Opnd --
   ---------------

   function Left_Opnd (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Left_Opnd (N));

   ------------------
   -- Library_Unit --
   ------------------

   function Library_Unit (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Library_Unit (N));

   ---------------------
   -- Limited_Present --
   ---------------------

   function Limited_Present (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Limited_Present (N));

   ------------------
   -- Loop_Actions --
   ------------------

   function Loop_Actions (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Loop_Actions (N));

   ----------------------------------
   -- Loop_Parameter_Specification --
   ----------------------------------

   function Loop_Parameter_Specification (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Loop_Parameter_Specification (N));

   ---------------
   -- Low_Bound --
   ---------------

   function Low_Bound (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Low_Bound (N));

   ----------
   -- Name --
   ----------

   function Name (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Name (N));

   ----------------
   -- Of_Present --
   ----------------

   function Of_Present (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Of_Present (N));

   ----------------------------------
   -- Pragma_Argument_Associations --
   ----------------------------------

   function Pragma_Argument_Associations (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Pragma_Argument_Associations (N));

   -----------------------
   -- Pragma_Identifier --
   -----------------------

   function Pragma_Identifier (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Pragma_Identifier (N));

   ------------
   -- Prefix --
   ------------

   function Prefix (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Prefix (N));

   -------------
   -- Realval --
   -------------

   function Realval (N : Node_Id) return Ureal
   is (Sinfo.Nodes.Realval (N));

   ------------
   -- Reason --
   ------------

   function Reason (N : Node_Id) return Uint
   is (Sinfo.Nodes.Reason (N));

   --------------------------------
   -- Return_Object_Declarations --
   --------------------------------

   function Return_Object_Declarations (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Return_Object_Declarations (N));

   -----------------------------
   -- Return_Statement_Entity --
   -----------------------------

   function Return_Statement_Entity (N : Node_Id) return Entity_Id
   is (Sinfo.Nodes.Return_Statement_Entity (N));

   ---------------------
   -- Reverse_Present --
   ---------------------

   function Reverse_Present (N : Node_Id) return Boolean
   is (Sinfo.Nodes.Reverse_Present (N));

   ----------------
   -- Right_Opnd --
   ----------------

   function Right_Opnd (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Right_Opnd (N));

   -------------------
   -- Selector_Name --
   -------------------

   function Selector_Name (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Selector_Name (N));

   ----------------
   -- Statements --
   ----------------

   function Statements (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Statements (N));

   ------------
   -- Strval --
   ------------

   function Strval (N : Node_Id) return String_Id
   is (Sinfo.Nodes.Strval (N));

   ------------------------
   -- Subtype_Indication --
   ------------------------

   function Subtype_Indication (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Subtype_Indication (N));

   ------------------
   -- Subtype_Mark --
   ------------------

   function Subtype_Mark (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Subtype_Mark (N));

   ------------------
   -- Then_Actions --
   ------------------

   function Then_Actions (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Then_Actions (N));

   ---------------------
   -- Then_Statements --
   ---------------------

   function Then_Statements (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Then_Statements (N));

   ------------------------
   -- Traverse_More_Proc --
   ------------------------

   procedure Traverse_More_Proc (Node : Node_Id) is
      procedure Traverse_Proc is new
        Sem_Util.Traverse_More_Proc (Process, Process_Itypes => True);
   begin
      Traverse_Proc (Node);
   end Traverse_More_Proc;

   ---------------------
   -- Type_Definition --
   ---------------------

   function Type_Definition (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Type_Definition (N));

   -----------------
   -- Unqual_Conv --
   -----------------

   function Unqual_Conv (N : Node_Id) return Node_Id
   renames Sem_Util.Unqual_Conv;

   ----------
   -- Unit --
   ----------

   function Unit (N : Node_Id) return Node_Id
   is (Sinfo.Nodes.Unit (N));

   --------------
   -- Variants --
   --------------

   function Variants (N : Node_Id) return List_Id
   is (Sinfo.Nodes.Variants (N));

end SPARK_Atree;
