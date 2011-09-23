------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Atree;                use Atree;
with Namet;                use Namet;
with Sinput;               use Sinput;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Tables;     use Why.Atree.Tables;
with Why.Conversions;      use Why.Conversions;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Progs;        use Why.Gen.Progs;
with Why.Gen.Terms;        use Why.Gen.Terms;

package body Why.Gen.Expr is

   function Is_False_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "false"

   function Is_True_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "true"

   ----------------------
   -- Is_False_Boolean --
   ----------------------

   function Is_False_Boolean (P : W_Expr_Id) return Boolean
   is
   begin
      return
         (Get_Kind (+P) = W_Literal and then
          Get_Value (+P) = EW_False);
   end Is_False_Boolean;

   ---------------------
   -- Is_True_Boolean --
   ---------------------

   function Is_True_Boolean (P : W_Expr_Id) return Boolean
   is
   begin
      return
         (Get_Kind (+P) = W_Literal and then
          Get_Value (+P) = EW_True);
   end Is_True_Boolean;

   ------------------
   -- New_And_Expr --
   ------------------

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id is
   begin
      if Is_True_Boolean (+Left) then
         return Right;

      elsif Is_True_Boolean (+Right) then
         return Left;

      else
         if Domain = EW_Pred then
            return New_Connection
              (Domain => Domain,
               Op     => EW_And,
               Left   => +Left,
               Right  => +Right);
         else
            return
              New_Call
                (Domain => Domain,
                 Name   => New_Identifier ("bool_and"),
                 Args   => (1 => +Left, 2 => +Right));
         end if;
      end if;
   end New_And_Expr;

   -----------------------
   -- New_And_Then_Expr --
   -----------------------

   function New_And_Then_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id is
   begin
      if Is_True_Boolean (+Left) then
         return Right;
      elsif Is_True_Boolean (+Right) then
         return Left;
      else
         if Domain = EW_Prog then
            return
               New_Connection
                 (Op     => EW_And_Then,
                  Left   => Left,
                  Right  => Right,
                  Domain => Domain);
         else
            return New_And_Expr (Left, Right, Domain);
         end if;
      end if;
   end New_And_Then_Expr;

   --------------------
   -- New_Comparison --
   --------------------

   function New_Comparison
     (Cmp         : EW_Relation;
      Left, Right : W_Expr_Id;
      Arg_Types   : W_Base_Type_Id;
      Domain      : EW_Domain)
     return W_Expr_Id is
   begin
      if Domain in EW_Pred | EW_Prog then
         return
            New_Relation
              (Domain  => Domain,
               Op_Type => Get_Base_Type (Arg_Types),
               Left    => +Left,
               Right   => +Right,
               Op      => Cmp);
      else
         return
           New_Call
             (Name   => New_Bool_Cmp (Cmp, Arg_Types),
              Args   => (1 => +Left, 2 => +Right),
              Domain => Domain);
      end if;
   end New_Comparison;

   ----------------------
   -- New_Located_Call --
   ----------------------

   function New_Located_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Expr_Array;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id
   is
   begin
      return
        +New_Located_Expr
          (Ada_Node => Ada_Node,
           Reason   => Reason,
           Expr     =>
             New_Call
               (Ada_Node => Ada_Node,
                Name     => Name,
                Args     => Progs,
                Domain   => Domain),
           Domain  => Domain);
   end New_Located_Call;

   ----------------------
   -- New_Located_Expr --
   ----------------------

   function New_Located_Expr
      (Ada_Node : Node_Id;
       Expr     : W_Expr_Id;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id
   is
   begin
      if Domain /= EW_Term
        and then Present (Ada_Node)
        and then
           not (Get_Kind (+Expr) = W_Literal
                and then Get_Value (+Expr) = EW_True)
      then
         return
            New_Label
              (Ada_Node => Ada_Node,
               Name     => New_Located_Label (Ada_Node, Reason),
               Def      => Expr,
               Domain   => Domain);
      else
         return Expr;
      end if;
   end New_Located_Expr;

   -----------------------
   -- New_Located_Label --
   -----------------------

   function New_Located_Label (N : Node_Id; Reason : VC_Kind)
      return W_Identifier_Id
   is

      --  A gnatprove label in Why3 has the following form
      --
      --  #"<filename>" linenumber columnnumber 0# "gnatprove:<VC_Kind>"
      --
      --  The first part, between the #, is a location label, indicating an
      --  Ada source location. The trailing 0 is needed because Why requires
      --  an end column, but we don't need one.
      --  The second part is a text label, which is used here to indicate the
      --  reason for a VC. with prefix the text with "gnatprove:" so that Why3
      --  can easily recognize the label as coming from gnatprove.

      Loc    : constant Source_Ptr := Sloc (N);
      File   : constant String :=
         Get_Name_String (File_Name (Get_Source_File_Index (Loc)));
      Line   : constant Physical_Line_Number := Get_Physical_Line_Number (Loc);
      Column : constant Column_Number := Get_Column_Number (Loc);
      Label : constant String :=
         "#""" & File & """" & Physical_Line_Number'Image (Line) &
         Column_Number'Image (Column) & " 0# " &
         """gnatprove:" & VC_Kind'Image (Reason) & """";
   begin
      return New_Identifier (Label);
   end New_Located_Label;

   -----------------
   -- New_Or_Expr --
   -----------------

   function New_Or_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id is
   begin
      if Is_False_Boolean (Left) then
         return Right;
      elsif Is_False_Boolean (Right) then
         return Left;
      else
         if Domain = EW_Pred then
            return New_Connection
              (Op     => EW_Or,
               Left   => +Left,
               Right  => +Right,
               Domain => Domain);
         else
            return New_Call
              (Domain => Domain,
               Name => New_Identifier ("bool_or"),
               Args => (1 => +Left, 2 => +Right));
         end if;
      end if;
   end New_Or_Expr;

   ----------------------
   -- New_Or_Else_Expr --
   ----------------------

   function New_Or_Else_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain) return W_Expr_Id
   is
   begin
      if Is_False_Boolean (Left) then
         return Right;
      elsif Is_False_Boolean (Right) then
         return Left;
      else
         if Domain = EW_Prog then
            return
              New_Connection
                (Domain => Domain,
                 Op     => EW_Or_Else,
                 Left   => Left,
                 Right  => Right);
         else
            return New_Or_Expr (Left, Right, Domain);
         end if;
      end if;
   end New_Or_Else_Expr;

   ------------------------
   -- New_Simpl_Any_Expr --
   ------------------------

   function New_Simpl_Any_Expr
     (Domain   : EW_Domain;
      Arg_Type : W_Primitive_Type_Id) return W_Expr_Id is
   begin
      case Domain is
         when EW_Term => return +New_Simpl_Epsilon_Term (Arg_Type);
         when EW_Prog => return +New_Simpl_Any_Prog (Arg_Type);
         when others => raise Program_Error;
      end case;
   end New_Simpl_Any_Expr;

   ---------------------------
   -- New_Simpl_Conditional --
   ---------------------------

   function New_Simpl_Conditional
      (Condition : W_Expr_Id;
       Then_Part : W_Expr_Id;
       Else_Part : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id
   is
   begin
      if Is_True_Boolean (Condition) then
         return Then_Part;
      elsif Is_False_Boolean (Condition) then
         return Else_Part;
      else
         return
           New_Conditional
             (Condition => +Condition,
              Then_Part => Then_Part,
              Else_Part => Else_Part,
              Domain    => Domain);
      end if;
   end New_Simpl_Conditional;

end Why.Gen.Expr;
