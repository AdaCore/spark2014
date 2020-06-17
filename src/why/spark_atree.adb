------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          S P A R K _ A T R E E                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2020, AdaCore                     --
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

with Ada.Text_IO; -- debugging purpose
with Aspects;
with Nlists;             use Nlists;
with Sem_Ch12;
with Sem_Disp;
with SPARK_Util.Types;
with Stand;              use Stand;

package body SPARK_Atree is

   -------------
   -- Actions --
   -------------

   function Actions (N : Node_Id) return List_Id renames Sinfo.Actions;

   ----------------------
   -- Aggregate_Bounds --
   ----------------------

   function Aggregate_Bounds (N : Node_Id) return Node_Id renames
     Sinfo.Aggregate_Bounds;

   -----------------
   -- All_Present --
   -----------------

   function All_Present (N : Node_Id) return Boolean renames
     Sinfo.All_Present;

   ------------------
   -- Alternatives --
   ------------------

   function Alternatives (N : Node_Id) return List_Id renames
     Sinfo.Alternatives;

   -------------------
   -- Ancestor_Part --
   -------------------

   function Ancestor_Part (N : Node_Id) return Node_Id renames
     Sinfo.Ancestor_Part;

   ----------------------------------------
   -- Attribute_Constrained_Static_Value --
   ----------------------------------------

   function Attribute_Constrained_Static_Value
     (N : Node_Id) return Boolean
   renames Exp_Util.Attribute_Constrained_Static_Value;

   --------------------
   -- Attribute_Name --
   --------------------

   function Attribute_Name (N : Node_Id) return Name_Id renames
     Sinfo.Attribute_Name;

   -----------------
   -- Box_Present --
   -----------------

   function Box_Present (N : Node_Id) return Boolean renames Sinfo.Box_Present;

   ------------------------
   -- Char_Literal_Value --
   ------------------------

   function Char_Literal_Value (N : Node_Id) return Uint renames
     Sinfo.Char_Literal_Value;

   -----------
   -- Chars --
   -----------

   function Chars (N : Node_Id) return Name_Id renames Sinfo.Chars;

   -------------
   -- Choices --
   -------------

   function Choices (N : Node_Id) return List_Id renames Sinfo.Choices;

   ----------------------------
   -- Component_Associations --
   ----------------------------

   function Component_Associations (N : Node_Id) return List_Id renames
     Sinfo.Component_Associations;

   --------------------------
   -- Component_Definition --
   --------------------------

   function Component_Definition (N : Node_Id) return Node_Id renames
     Sinfo.Component_Definition;

   ----------------------------------
   -- Component_Subtype_Indication --
   ----------------------------------

   function Component_Subtype_Indication (N : Node_Id) return Node_Id is
     (if Nkind (N) = N_Full_Type_Declaration
      and then Nkind (Type_Definition (N)) in
            N_Constrained_Array_Definition
          | N_Unconstrained_Array_Definition
      then Sinfo.Subtype_Indication
        (Sinfo.Component_Definition (Sinfo.Type_Definition (N)))
      else Empty);

   ---------------
   -- Condition --
   ---------------

   function Condition (N : Node_Id) return Node_Id renames
     Sinfo.Condition;

   -----------------------
   -- Condition_Actions --
   -----------------------

   function Condition_Actions (N : Node_Id) return List_Id renames
     Sinfo.Condition_Actions;

   ----------------------
   -- Constant_Present --
   ----------------------

   function Constant_Present (N : Node_Id) return Boolean renames
     Sinfo.Constant_Present;

   -------------------
   -- Context_Items --
   -------------------

   function Context_Items (N : Node_Id) return List_Id renames
     Sinfo.Context_Items;

   --------------------------
   -- Controlling_Argument --
   --------------------------

   function Controlling_Argument (N : Node_Id) return Node_Id renames
      Sinfo.Controlling_Argument;

   ---------------------------------
   -- Corresponding_Integer_Value --
   ---------------------------------

   function Corresponding_Integer_Value (N : Node_Id) return Uint renames
      Sinfo.Corresponding_Integer_Value;

   ------------------
   -- Declarations --
   ------------------

   function Declarations (N : Node_Id) return List_Id renames
     Sinfo.Declarations;

   -----------------------------
   -- Depends_On_Discriminant --
   -----------------------------

   function Depends_On_Discriminant (N : Node_Id) return Boolean renames
     Sem_Util.Depends_On_Discriminant;

   ----------------------
   -- Discrete_Choices --
   ----------------------

   function Discrete_Choices (N : Node_Id) return List_Id renames
    Sinfo.Discrete_Choices;

   --------------------
   -- Discrete_Range --
   --------------------

   function Discrete_Range (N : Node_Id) return Node_Id renames
    Sinfo.Discrete_Range;

   ---------------------------------
   -- Discrete_Subtype_Definition --
   ---------------------------------

   function Discrete_Subtype_Definition (N : Node_Id) return Node_Id renames
    Sinfo.Discrete_Subtype_Definition;

   -----------------------------------
   -- Do_Check_On_Scalar_Conversion --
   -----------------------------------

   function Do_Check_On_Scalar_Conversion (N : Node_Id) return Boolean is
      use type Einfo.Entity_Kind;
   begin
      return
      Sinfo.Do_Range_Check (N)
      or else
        (Atree.Nkind (Atree.Parent (N)) = N_Type_Conversion
         and then Sinfo.Do_Overflow_Check (Atree.Parent (N)))
      or else
        (Atree.Nkind (N) = N_Type_Conversion
         and then Sinfo.Do_Range_Check (Sinfo.Expression (N))
         and then Atree.Nkind (Atree.Parent (N)) in
           N_Parameter_Association | N_Procedure_Call_Statement
             | N_Entry_Call_Statement
         and then Atree.Ekind (SPARK_Util.Get_Formal_From_Actual (N)) in
           Einfo.E_In_Out_Parameter | Einfo.E_Out_Parameter)
      or else
        (Atree.Nkind (Atree.Parent (N)) = N_Range
         and then Sinfo.Do_Range_Check (Atree.Parent (N)))

      --  Do_Range_Check flag is not set on allocators. Do the check if the
      --  designated subtype and the provided subtype do not match.
      --  For uninitialized allocators, N is the allocator node itself.

      or else
        (Atree.Nkind (N) = N_Allocator
         and then Einfo.Directly_Designated_Type
           (if Present (Einfo.Full_View (Etype (N)))
            then Einfo.Full_View (Etype (N))
            else Etype (N)) /= Entity (Expression (N)))

      --  On initialized allocators, it is the allocated expression, so the
      --  allocator is its parent.

      or else
        (Atree.Nkind (Atree.Parent (N)) = N_Allocator
         and then Einfo.Directly_Designated_Type
           (if Present (Einfo.Full_View (Etype (Atree.Parent (N))))
            then Einfo.Full_View (Etype (Atree.Parent (N)))
            else Etype (Atree.Parent (N)))
         /= Etype (N));
   end Do_Check_On_Scalar_Conversion;

   -----------------------
   -- Do_Division_Check --
   -----------------------

   function Do_Division_Check (N : Node_Id) return Boolean renames
      Sinfo.Do_Division_Check;

   -----------------------
   -- Do_Overflow_Check --
   -----------------------

   function Do_Overflow_Check (N : Node_Id) return Boolean renames
      Sinfo.Do_Overflow_Check;

   --------------------
   -- Do_Range_Check --
   --------------------

   function Do_Range_Check (N : Node_Id) return Boolean renames
      Sinfo.Do_Range_Check;

   ------------------
   -- Else_Actions --
   ------------------

   function Else_Actions (N : Node_Id) return List_Id renames
      Sinfo.Else_Actions;

   ---------------------
   -- Else_Statements --
   ---------------------

   function Else_Statements (N : Node_Id) return List_Id renames
     Sinfo.Else_Statements;

   -----------------
   -- Elsif_Parts --
   -----------------

   function Elsif_Parts (N : Node_Id) return List_Id renames Sinfo.Elsif_Parts;

   ------------------------------
   -- Enclosing_Comp_Unit_Node --
   ------------------------------

   function Enclosing_Comp_Unit_Node (N : Node_Id) return Node_Id renames
     Sem_Util.Enclosing_Comp_Unit_Node;

   -------------------------
   -- Enclosing_Statement --
   -------------------------

   function Enclosing_Statement (N : Node_Id) return Node_Id renames
     Atree.Parent;

   ------------
   -- Entity --
   ------------

   function Entity (N : Node_Id) return Node_Id renames Sinfo.Entity;

   ------------------------
   -- Entry_Body_Barrier --
   ------------------------

   function Entry_Body_Barrier (N : Node_Id) return Node_Id is
     (Sinfo.Condition (Sinfo.Entry_Body_Formal_Part (N)));

   -----------
   -- Etype --
   -----------

   function Etype (N : Node_Id) return Node_Id renames Sinfo.Etype;

   ----------------
   -- Expr_Value --
   ----------------

   function Expr_Value (N : Node_Id) return Uint renames Sem_Eval.Expr_Value;

   ------------------
   -- Expr_Value_R --
   ------------------

   function Expr_Value_R (N : Node_Id) return Ureal renames
     Sem_Eval.Expr_Value_R;

   ----------------
   -- Expression --
   ----------------

   function Expression (N : Node_Id) return Node_Id renames Sinfo.Expression;

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
           and then Get_Attribute_Id (Attribute_Name (N))
             in Attribute_Old | Attribute_Loop_Entry
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

   ------------------------------------------------
   -- Expression_Contains_Valid_Or_Valid_Scalars --
   ------------------------------------------------

   function Expression_Contains_Valid_Or_Valid_Scalars
     (Expr : Node_Id) return Boolean
   is
      use type Atree.Traverse_Result;

      function Search_Valid_Or_Valid_Scalars
        (N : Node_Id) return Atree.Traverse_Result;
      --  Search for attribute Valid or Valid_Scalars

      -----------------------------------
      -- Search_Valid_Or_Valid_Scalars --
      -----------------------------------

      function Search_Valid_Or_Valid_Scalars
        (N : Node_Id) return Atree.Traverse_Result is
      begin
         if Nkind (N) = N_Attribute_Reference
           and then Get_Attribute_Id (Attribute_Name (N))
             in Attribute_Valid | Attribute_Valid_Scalars
         then
            --  There is no need to continue the traversal, as one such
            --  attribute suffices.

            return Atree.Abandon;
         end if;

         return Atree.OK;
      end Search_Valid_Or_Valid_Scalars;

      function Search_Attrs is new
        Sem_Util.Traverse_More_Func (Search_Valid_Or_Valid_Scalars);

   --  Start of processing for Expression_Contains_Valid_Or_Valid_Scalars

   begin
      return Search_Attrs (Expr) = Atree.Abandon;
   end Expression_Contains_Valid_Or_Valid_Scalars;

   -----------------
   -- Expressions --
   -----------------

   function Expressions (N : Node_Id) return List_Id renames Sinfo.Expressions;

   ---------------
   -- First_Bit --
   ---------------

   function First_Bit (N : Node_Id) return Node_Id renames Sinfo.First_Bit;

   -------------------------------
   -- From_Aspect_Specification --
   -------------------------------

   function From_Aspect_Specification (N : Node_Id) return Boolean renames
     Sinfo.From_Aspect_Specification;

   -----------------------------------
   -- From_Real_Range_Specification --
   -----------------------------------

   function From_Real_Range_Specification (N : Node_Id) return Boolean is
     (Nkind (Atree.Parent (N)) = Sinfo.N_Real_Range_Specification);

   --------------------------
   -- Get_Address_Rep_Item --
   --------------------------

   function Get_Address_Rep_Item (N : Node_Id) return Node_Id is
      Address : constant Node_Id :=
        Sem_Aux.Get_Rep_Item (Sem_Util.Defining_Entity (N), Name_Address);
   begin
      if Present (Address) then
         return Sinfo.Expression (Address);
      else
         return Empty;
      end if;
   end Get_Address_Rep_Item;

   -----------------------
   -- Get_Called_Entity --
   -----------------------

   function Get_Called_Entity (N : Node_Id) return Entity_Id is
     (if Nkind (N) in N_Op
      then Entity (N)
      else Sem_Aux.Get_Called_Entity (N));

   --------------------------
   -- Get_Enclosing_Object --
   --------------------------

   function Get_Enclosing_Object (N : Node_Id) return Entity_Id is
   begin
      if Einfo.Is_Entity_Name (N) then
         return Entity (N);
      else
         case Nkind (N) is
            when N_Explicit_Dereference
               | N_Indexed_Component
               | N_Selected_Component
               | N_Slice
            =>
               return Get_Enclosing_Object (Prefix (N));

            when N_Type_Conversion =>
               return Get_Enclosing_Object (Expression (N));

            when others =>
               return Empty;
         end case;
      end if;
   end Get_Enclosing_Object;

   -------------------
   -- Get_Pragma_Id --
   -------------------

   function Get_Pragma_Id (N : Node_Id) return Pragma_Id renames
     Sem_Util.Get_Pragma_Id;

   --------------------------
   -- Get_Range_Check_Info --
   --------------------------

   procedure Get_Range_Check_Info
     (N                 : Node_Id;
      In_Left_Hand_Side : Boolean := False;
      Check_Type        : out Entity_Id;
      Check_Kind        : out SPARK_Util.Scalar_Check_Kind)
   is
      Par : Node_Id := Atree.Parent (N);

   begin
      --  For uninitialized allocators, N is not a scalar expression but
      --  the allocator itself.

      if Nkind (N) = N_Allocator then
         Par := N;
      end if;

      --  In proof, we use the original node for unchecked conversions
      --  coming from source.

      if Nkind (Par) = N_Unchecked_Type_Conversion
        and then Comes_From_Source (Par)
      then
         Par := Original_Node (Par);
      end if;

      --  Set the appropriate entity in Check_Type giving the bounds for the
      --  check, depending on the parent node Par.

      case Nkind (Par) is

         when N_Assignment_Statement =>
            Check_Type := Etype (Name (Par));

            --  For an array access, an index check has already been introduced
            --  if needed. There is no other check to do.

         when N_Indexed_Component =>
            Check_Type := Empty;
            Check_Kind := SPARK_Util.RCK_Index;
            return;

            --  Frontend may have introduced unchecked type conversions on
            --  expressions or variables assigned to, which require range
            --  checking. When applied to a left-hand side of an assignment,
            --  the target type for the range check is the type of the object
            --  being converted. Otherwise, the target type is the type of the
            --  conversion.

         when N_Type_Conversion
            | N_Unchecked_Type_Conversion
            =>
            Check_Type :=
              (if In_Left_Hand_Side then Etype (N) else Etype (Par));

         when N_Qualified_Expression =>
            Check_Type := Etype (Par);

         when N_Simple_Return_Statement =>
            Check_Type :=
              Etype (Einfo.Return_Applies_To (Return_Statement_Entity (Par)));

            --  For a call, retrieve the type for the corresponding argument

         when N_Function_Call
            | N_Procedure_Call_Statement
            | N_Entry_Call_Statement
            | N_Parameter_Association
            =>
            --  If In_Left_Hand_Side is True, we are checking actual parameters
            --  on stores. In this case, the Check_Type is the type of the
            --  expression. Otherwise, the Check_Type is the expected formal
            --  type.

            if In_Left_Hand_Side then
               Check_Type := Etype (N);
            else
               Check_Type := Etype (SPARK_Util.Get_Formal_From_Actual (N));
            end if;

         when N_Attribute_Reference =>
            Attribute : declare
               Aname   : constant Name_Id := Attribute_Name (Par);
               Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
            begin
               case Attr_Id is
                  when Attribute_Pred |
                       Attribute_Succ |
                       Attribute_Val  =>
                     Check_Type := Einfo.Base_Type (Entity (Prefix (Par)));

                  when others =>
                     Ada.Text_IO.Put_Line ("[Get_Range_Check_Info] attr ="
                                           & Attribute_Id'Image (Attr_Id));
                     raise Program_Error;
               end case;
            end Attribute;

         when N_Op_Expon =>

            --  A range check on exponentiation is only possible on the right
            --  operand, and in this case the check range is "Natural"

            Check_Type := Standard_Natural;

         when N_Component_Association =>

            declare
               Pref        : Node_Id;
               Prefix_Type : Entity_Id;

            begin
               --  Expr is either
               --  1) a choice of a 'Update aggregate, and needs a
               --  range check towards the corresponding index type of the
               --  prefix to the 'Update aggregate, or
               --  2) a component expression of a 'Update aggregate for arrays,
               --  and needs a range check towards the component type.
               --  3) a component expression of a 'Update aggregate for
               --  records, and needs a range check towards the type of
               --  the component
               --  3) an expression of a regular record aggregate, and
               --  needs a range check towards the expected type.

               if Nkind (Atree.Parent (Par)) = N_Aggregate
                 and then
                   Nkind (Atree.Parent (Atree.Parent (Par))) =
                     N_Attribute_Reference
                 and then
                   Sem_Util.Is_Attribute_Update
                     (Atree.Parent (Atree.Parent (Par)))
               then

                  Pref := Prefix (Atree.Parent (Atree.Parent (Par)));

                  --  When present, the Actual_Subtype of the entity should be
                  --  used instead of the Etype of the prefix.

                  if Einfo.Is_Entity_Name (Pref)
                    and then Present (Einfo.Actual_Subtype (Entity (Pref)))
                  then
                     Prefix_Type := Einfo.Actual_Subtype (Entity (Pref));
                  else
                     Prefix_Type := Etype (Pref);
                  end if;

                  if SPARK_Util.Types.Has_Record_Type (Prefix_Type) then

                     Check_Type := Etype (Nlists.First (Choices (Par)));

                     --  it's an array type, determine whether the check is for
                     --  the component or the index

                  elsif Expression (Par) = N then
                     Check_Type :=
                       Einfo.Component_Type
                         (Sem_Util.Unique_Entity (Prefix_Type));
                  else
                     Check_Type :=
                       Etype (Einfo.First_Index
                              (Sem_Util.Unique_Entity (Prefix_Type)));
                  end if;

                  --  must be a regular record aggregate

               else
                  pragma Assert (Expression (Par) = N);

                  Check_Type := Etype (N);
               end if;
            end;

         when N_Range =>
            if Is_Choice_Of_Unconstrained_Array_Update (Par) then
               declare
                  Pref        : Node_Id;
                  Prefix_Type : Entity_Id;

               begin
                  pragma Assert
                    (Nkind (Atree.Parent (Atree.Parent (Par))) = N_Aggregate);
                  Pref :=
                    Prefix (Atree.Parent (Atree.Parent (Atree.Parent (Par))));

                  if Einfo.Is_Entity_Name (Pref)
                    and then Present (Einfo.Actual_Subtype (Entity (Pref)))
                  then
                     Prefix_Type := Einfo.Actual_Subtype (Entity (Pref));
                  else
                     Prefix_Type := Etype (Pref);
                  end if;

                  Check_Type :=
                    Etype (Einfo.First_Index
                           (Sem_Util.Unique_Entity (Prefix_Type)));
               end;
            else
               Check_Type := Etype (Par);
            end if;

         when N_Aggregate =>

            --  This parent is a special choice, the LHS of an association
            --  of a 'Update of a multi-dimensional array, for example:
            --  (I, J, K) of 'Update((I, J, K) => New_Val)

            pragma Assert
              (Nkind (Atree.Parent (Par)) = N_Component_Association);

            Aggregate : declare

               Aggr : constant Node_Id := Atree.Parent (Atree.Parent (Par));

               pragma Assert
                 (Nkind (Aggr) = N_Aggregate
                  and then Nkind (Atree.Parent (Aggr)) = N_Attribute_Reference
                  and then Sem_Util.Is_Attribute_Update (Atree.Parent (Aggr)));

               Pref        : constant Node_Id := Prefix (Atree.Parent (Aggr));
               Num_Dim     : constant Pos :=
                 Einfo.Number_Dimensions
                   (SPARK_Util.Types.Retysp (Etype (Pref)));
               Multi_Exprs : constant List_Id := Expressions (Par);

               Dim_Expr      : Node_Id;
               Array_Type    : Entity_Id;
               Current_Index : Node_Id;
               Found         : Boolean;

               pragma Assert (1 < Num_Dim
                              and then No (Component_Associations (Par))
                              and then List_Length (Multi_Exprs) = Num_Dim);

            begin

               --  When present, the Actual_Subtype of the entity should be
               --  used instead of the Etype of the prefix.

               if Einfo.Is_Entity_Name (Pref)
                 and then Present (Einfo.Actual_Subtype (Entity (Pref)))
               then
                  Array_Type := Einfo.Actual_Subtype (Entity (Pref));
               else
                  Array_Type := Etype (Pref);
               end if;

               --  Find the index type for this expression's dimension.

               Dim_Expr      := Nlists.First (Multi_Exprs);
               Current_Index :=
                 Einfo.First_Index (Sem_Util.Unique_Entity (Array_Type));
               Found         := False;

               while Present (Dim_Expr) loop
                  if N = Dim_Expr then
                     Check_Type := Etype (Current_Index);
                     Found := True;
                     exit;
                  end if;
                  Next (Dim_Expr);
                  Einfo.Next_Index (Current_Index);
               end loop;

               pragma Assert (Found);

            end Aggregate;

         when N_Aspect_Specification =>

            --  We only expect range checks on aspects for default values.

            case Aspects.Get_Aspect_Id (Par) is
            when Aspects.Aspect_Default_Component_Value =>
               pragma Assert
                 (Einfo.Is_Array_Type
                    (SPARK_Util.Types.Retysp (Entity (Par))));
               Check_Type :=
                 Einfo.Component_Type
                   (SPARK_Util.Types.Retysp (Entity (Par)));
            when Aspects.Aspect_Default_Value =>
               pragma Assert
                 (Einfo.Is_Scalar_Type
                    (SPARK_Util.Types.Retysp (Entity (Par))));
               Check_Type := SPARK_Util.Types.Retysp (Entity (Par));
            when others =>
               Ada.Text_IO.Put_Line ("[Get_Range_Check_Info] aspect ="
                                     &  Aspects.Aspect_Id'Image
                                       (Aspects.Get_Aspect_Id (Par)));
               raise Program_Error;
            end case;

         when N_Object_Declaration
            | N_Component_Declaration
            | N_Discriminant_Specification
         =>
            --  We expect range checks on defaults of record fields and
            --  discriminants.

            Check_Type := Etype (Defining_Identifier (Par));

         when N_If_Expression =>
            Check_Type := Etype (Par);

         when N_Case_Expression_Alternative =>
            Check_Type := Etype (Atree.Parent (Par));

         when N_Allocator =>
            Check_Type := Einfo.Directly_Designated_Type
              (if Present (Einfo.Full_View (Etype (Par)))
               then Einfo.Full_View (Etype (Par))
               else Etype (Par));

         when others =>
            Ada.Text_IO.Put_Line ("[Get_Range_Check_Info] kind ="
                                  & Node_Kind'Image (Nkind (Par)));
            raise Program_Error;
      end case;

      --  Reach through a non-private type in order to query its kind

      Check_Type := SPARK_Util.Types.Retysp (Check_Type);

      --  If the target type is a constrained array, we have a length check.

      if Einfo.Is_Array_Type (Check_Type) and then
        Einfo.Is_Constrained (Check_Type)
      then
         Check_Kind := SPARK_Util.RCK_Length;

         --  For attributes Pred and Succ, the check is a range check for
         --  enumeration types, and an overflow check otherwise. We use special
         --  values of Check_Kind to account for the different range checked in
         --  these cases.

      elsif Nkind (Par) = N_Attribute_Reference and then
        Get_Attribute_Id (Attribute_Name (Par)) = Attribute_Pred
      then
         if Einfo.Is_Enumeration_Type (Check_Type) then
            Check_Kind := SPARK_Util.RCK_Range_Not_First;
         else
            Check_Kind := SPARK_Util.RCK_Overflow_Not_First;
         end if;

      elsif Nkind (Par) = N_Attribute_Reference and then
        Get_Attribute_Id (Attribute_Name (Par)) = Attribute_Succ
      then
         if Einfo.Is_Enumeration_Type (Check_Type) then
            Check_Kind := SPARK_Util.RCK_Range_Not_Last;
         else
            Check_Kind := SPARK_Util.RCK_Overflow_Not_Last;
         end if;

         --  Otherwise, this is a range check

      else
         Check_Kind := SPARK_Util.RCK_Range;
      end if;
   end Get_Range_Check_Info;

   -----------------------
   -- Get_Return_Object --
   -----------------------

   function Get_Return_Object (N : Node_Id) return Entity_Id renames
     Sem_Util.Get_Return_Object;

   -----------------------------------
   -- Get_Unchecked_Conversion_Args --
   -----------------------------------

   procedure Get_Unchecked_Conversion_Args (E              : Entity_Id;
                                            Source, Target : out Node_Id)
   is
      Wrapper_Pkg : constant Node_Id :=
        Sinfo.Defining_Unit_Name (Atree.Parent (Sem_Aux.Subprogram_Spec (E)));
      pragma Assert (Einfo.Is_Wrapper_Package (Wrapper_Pkg));
      First_Assoc : constant Node_Id :=
        First (Sinfo.Generic_Associations (Sem_Ch12.Get_Unit_Instantiation_Node
               (Wrapper_Pkg)));
   begin
      Source := Sinfo.Explicit_Generic_Actual_Parameter (First_Assoc);
      Target := Sinfo.Explicit_Generic_Actual_Parameter (Next (First_Assoc));
   end Get_Unchecked_Conversion_Args;

   --------------------------------
   -- Handled_Statement_Sequence --
   --------------------------------

   function Handled_Statement_Sequence (N : Node_Id) return Node_Id renames
     Sinfo.Handled_Statement_Sequence;

   ----------------
   -- High_Bound --
   ----------------

   function High_Bound (N : Node_Id) return Node_Id renames Sinfo.High_Bound;

   ----------------
   -- Identifier --
   ----------------

   function Identifier (N : Node_Id) return Node_Id renames Sinfo.Identifier;

   ----------------------------
   -- Inherited_Discriminant --
   ----------------------------

   function Inherited_Discriminant (N : Node_Id) return Boolean renames
     Sinfo.Inherited_Discriminant;

   ------------
   -- Intval --
   ------------

   function Intval (N : Node_Id) return Uint renames Sinfo.Intval;

   ---------------------------------------------
   -- Is_Choice_Of_Unconstrained_Array_Update --
   ---------------------------------------------

   function Is_Choice_Of_Unconstrained_Array_Update
     (N : Node_Id) return Boolean
   is
      Possibly_Choice_Node, Attribute_Node : Node_Id;
   begin
      if Nkind (Atree.Parent (N)) = N_Component_Association then
         Possibly_Choice_Node := N;
      elsif Nkind (Atree.Parent (N)) = N_Range
        and then Nkind (Atree.Parent (Atree.Parent (N))) =
        N_Component_Association
      then
         Possibly_Choice_Node := Atree.Parent (N);
      else
         return False;
      end if;

      if Nkind
        (Atree.Parent (Atree.Parent (Possibly_Choice_Node))) = N_Aggregate
      then
         Attribute_Node :=
           Atree.Parent
             (Atree.Parent (Atree.Parent (Possibly_Choice_Node)));
      else
         return False;
      end if;

      if Nkind (Attribute_Node) = N_Attribute_Reference
        and then Sem_Util.Is_Attribute_Update (Attribute_Node)
        and then Einfo.Is_Array_Type (Etype (Prefix (Attribute_Node)))
        and then not Einfo.Is_Constrained (Etype (Prefix (Attribute_Node)))
        and then Is_List_Member (Possibly_Choice_Node)
        and then Present (Choices (Atree.Parent (Possibly_Choice_Node)))
        and then List_Containing (Possibly_Choice_Node)
        = Choices (Atree.Parent (Possibly_Choice_Node))
      then
         return True;
      else
         return False;
      end if;
   end Is_Choice_Of_Unconstrained_Array_Update;

   ----------------------------
   -- Is_Component_Left_Opnd --
   ----------------------------

   function Is_Component_Left_Opnd (N : Node_Id) return Boolean renames
     Sinfo.Is_Component_Left_Opnd;

   -----------------------------
   -- Is_Component_Right_Opnd --
   -----------------------------

   function Is_Component_Right_Opnd (N : Node_Id) return Boolean renames
     Sinfo.Is_Component_Right_Opnd;

   ---------------------------
   -- Is_Controlling_Actual --
   ---------------------------

   function Is_Controlling_Actual (N : Node_Id) return Boolean renames
      Sinfo.Is_Controlling_Actual;

   -----------------
   -- Is_In_Range --
   -----------------

   function Is_In_Range (N : Node_Id; Typ : Entity_Id) return Boolean is
      (Sem_Eval.Is_In_Range (N, Typ, Assume_Valid => True));

   ----------------------------
   -- Is_Iterator_Over_Array --
   ----------------------------

   function Is_Iterator_Over_Array (N : Node_Id) return Boolean renames
     Sem_Util.Is_Iterator_Over_Array;

   --------------------------------
   -- Is_Locally_Defined_In_Loop --
   --------------------------------

   function Is_Locally_Defined_In_Loop (N : Node_Id) return Boolean is
      Stmt : Node_Id := Atree.Parent (N);
   begin
      while Present (Stmt) loop
         if Nkind (Stmt) = N_Loop_Statement then
            return True;

         elsif Sem_Util.Is_Body_Or_Package_Declaration (Stmt) then
            return False;
         end if;

         Stmt := Atree.Parent (Stmt);
      end loop;

      return False;
   end Is_Locally_Defined_In_Loop;

   -----------------------------
   -- Is_OK_Static_Expression --
   -----------------------------

   function Is_OK_Static_Expression (N : Node_Id) return Boolean renames
     Sem_Eval.Is_OK_Static_Expression;

   ------------------------
   -- Is_OK_Static_Range --
   ------------------------

   function Is_OK_Static_Range (N : Node_Id) return Boolean renames
     Sem_Eval.Is_OK_Static_Range;

   ------------------------
   -- Is_Rewritten_Op_Eq --
   ------------------------

   function Is_Rewritten_Op_Eq (N : Node_Id) return Boolean is
     (Nkind (N) = N_Function_Call
      and then Nkind (Original_Node (N)) in N_Op_Eq | N_Op_Ne);

   --------------------------
   -- Is_Static_Expression --
   --------------------------

   function Is_Static_Expression (N : Node_Id) return Boolean renames
     Sinfo.Is_Static_Expression;

   --------------------------
   -- Is_Tag_Indeterminate --
   --------------------------

   function Is_Tag_Indeterminate (N : Node_Id) return Boolean renames
     Sem_Disp.Is_Tag_Indeterminate;

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

      function Cstr_Subtype_Indication (N : Node_Id) return Boolean is
        (Nkind (Subtype_Indication (N)) = N_Subtype_Indication);

   begin
      case Nkind (Decl) is
         when N_Subtype_Declaration =>
            return not Cstr_Subtype_Indication (Decl);

         when N_Full_Type_Declaration =>
            if Nkind (Type_Definition (Decl)) = N_Derived_Type_Definition then
               declare
                  Def : constant Node_Id := Type_Definition (Decl);
               begin
                  return No (Sinfo.Record_Extension_Part (Def))
                    and then not Cstr_Subtype_Indication (Def);
               end;
            else
               return False;
            end if;

         when others =>
            return False;
      end case;
   end Is_Type_Renaming;

   -----------------
   -- Is_Variable --
   -----------------

   function Is_Variable (N : Node_Id) return Boolean is
     (Sem_Util.Is_Variable (N));

   ----------------------
   -- Iteration_Scheme --
   ----------------------

   function Iteration_Scheme (N : Node_Id) return Node_Id renames
     Sinfo.Iteration_Scheme;

   ----------------------------
   -- Iterator_Specification --
   ----------------------------

   function Iterator_Specification (N : Node_Id) return Node_Id renames
     Sinfo.Iterator_Specification;

   --------------
   -- Last_Bit --
   --------------

   function Last_Bit (N : Node_Id) return Node_Id renames Sinfo.Last_Bit;

   ---------------
   -- Left_Opnd --
   ---------------

   function Left_Opnd (N : Node_Id) return Node_Id renames Sinfo.Left_Opnd;

   ------------------
   -- Library_Unit --
   ------------------

   function Library_Unit (N : Node_Id) return Node_Id renames
     Sinfo.Library_Unit;

   ---------------------
   -- Limited_Present --
   ---------------------

   function Limited_Present (N : Node_Id) return Boolean renames
     Sinfo.Limited_Present;

   ----------------------------------
   -- Loop_Parameter_Specification --
   ----------------------------------

   function Loop_Parameter_Specification (N : Node_Id) return Node_Id renames
     Sinfo.Loop_Parameter_Specification;

   ---------------
   -- Low_Bound --
   ---------------

   function Low_Bound (N : Node_Id) return Node_Id renames Sinfo.Low_Bound;

   ----------
   -- Name --
   ----------

   function Name (N : Node_Id) return Node_Id renames Sinfo.Name;

   ----------------
   -- Of_Present --
   ----------------

   function Of_Present (N : Node_Id) return Boolean renames Sinfo.Of_Present;

   ------------------------------
   -- Parameter_Specifications --
   ------------------------------

   function Parameter_Specifications (N : Node_Id) return List_Id renames
     Sinfo.Parameter_Specifications;

   ----------------------------------
   -- Pragma_Argument_Associations --
   ----------------------------------

   function Pragma_Argument_Associations (N : Node_Id) return List_Id renames
      Sinfo.Pragma_Argument_Associations;

   ------------
   -- Prefix --
   ------------

   function Prefix (N : Node_Id) return Node_Id renames Sinfo.Prefix;

   -------------
   -- Realval --
   -------------

   function Realval (N : Node_Id) return Ureal renames Sinfo.Realval;

   ------------
   -- Reason --
   ------------

   function Reason (N : Node_Id) return Uint renames Sinfo.Reason;

   --------------------------------
   -- Return_Object_Declarations --
   --------------------------------

   function Return_Object_Declarations (N : Node_Id) return List_Id renames
     Sinfo.Return_Object_Declarations;

   -----------------------------
   -- Return_Statement_Entity --
   -----------------------------

   function Return_Statement_Entity (N : Node_Id) return Entity_Id renames
     Sinfo.Return_Statement_Entity;

   ---------------------
   -- Reverse_Present --
   ---------------------

   function Reverse_Present (N : Node_Id) return Boolean renames
     Sinfo.Reverse_Present;

   ----------------
   -- Right_Opnd --
   ----------------

   function Right_Opnd (N : Node_Id) return Node_Id renames Sinfo.Right_Opnd;

   -------------------
   -- Selector_Name --
   -------------------

   function Selector_Name (N : Node_Id) return Node_Id renames
     Sinfo.Selector_Name;

   ----------------
   -- Statements --
   ----------------

   function Statements (N : Node_Id) return List_Id renames Sinfo.Statements;

   ------------
   -- Strval --
   ------------

   function Strval (N : Node_Id) return String_Id renames Sinfo.Strval;

   ------------------------
   -- Subtype_Indication --
   ------------------------

   function Subtype_Indication (N : Node_Id) return Node_Id renames
     Sinfo.Subtype_Indication;

   ------------------
   -- Subtype_Mark --
   ------------------

   function Subtype_Mark (N : Node_Id) return Node_Id renames
     Sinfo.Subtype_Mark;

   ------------------
   -- Then_Actions --
   ------------------

   function Then_Actions (N : Node_Id) return List_Id renames
      Sinfo.Then_Actions;

   ---------------------
   -- Then_Statements --
   ---------------------

   function Then_Statements (N : Node_Id) return List_Id renames
     Sinfo.Then_Statements;

   ------------------------
   -- Traverse_More_Proc --
   ------------------------

   procedure Traverse_More_Proc (Node : Node_Id) is
      procedure Traverse_Proc is new Sem_Util.Traverse_More_Proc (Process);
   begin
      Traverse_Proc (Node);
   end Traverse_More_Proc;

   ---------------------
   -- Type_Definition --
   ---------------------

   function Type_Definition (N : Node_Id) return Node_Id renames
     Sinfo.Type_Definition;

   ----------
   -- Unit --
   ----------

   function Unit (N : Node_Id) return Node_Id renames Sinfo.Unit;

   --------------
   -- Variants --
   --------------

   function Variants (N : Node_Id) return List_Id renames Sinfo.Variants;

end SPARK_Atree;
