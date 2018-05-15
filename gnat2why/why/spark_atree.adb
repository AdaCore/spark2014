------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          S P A R K _ A T R E E                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2018, AdaCore                        --
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

with Sem_Aux;
with Sem_Disp;

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

   function Condition  (N : Node_Id) return Node_Id renames
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
     (Sem_Aux.Ultimate_Alias
        (if Nkind (N) in N_Op then Entity (N)
         else Sem_Aux.Get_Called_Entity (N)));

   --------------------------
   -- Get_Enclosing_Object --
   --------------------------

   function Get_Enclosing_Object (N : Node_Id) return Entity_Id renames
     Sem_Util.Get_Enclosing_Object;

   -------------------
   -- Get_Pragma_Id --
   -------------------

   function Get_Pragma_Id (N : Node_Id) return Pragma_Id renames
     Sem_Util.Get_Pragma_Id;

   -----------------------
   -- Get_Return_Object --
   -----------------------

   function Get_Return_Object (N : Node_Id) return Entity_Id renames
     Sem_Util.Get_Return_Object;

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

   function Inherited_Discriminant  (N : Node_Id) return Boolean renames
     Sinfo.Inherited_Discriminant;

   ------------
   -- Intval --
   ------------

   function Intval (N : Node_Id) return Uint renames Sinfo.Intval;

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
            if Nkind (Type_Definition (Decl)) =
              N_Derived_Type_Definition
            then
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

   -----------------------------
   -- Paramenter_Associations --
   -----------------------------

   function Parameter_Associations (N : Node_Id) return List_Id renames
     Sinfo.Parameter_Associations;

   ------------------------------
   -- Paramenter_Specificatons --
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

   function Return_Object_Declarations  (N : Node_Id) return List_Id renames
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
