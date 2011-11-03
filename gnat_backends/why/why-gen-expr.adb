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
with Why.Inter;            use Why.Inter;

package body Why.Gen.Expr is

   package Conversion_Reason is
      --  This package provide a rudimentary way to deleguate
      --  vc kinds to other checks. This allow to optimize out
      --  some checks without losing their reason.
      --
      --  The typical case for such a deleguation would be:
      --
      --  A : Integer := 10;
      --  B : Integer := A + 1;
      --
      --  The second line would translated as something like:
      --
      --  B := integer_from_int_ (overflow_check (integer_to_int (A) + 1))
      --
      --  Two identical checks would then be to prove: a range check by
      --  integer_from_int_, and overflow check by overflow_check. The thing
      --  is, there is little point in having two checks here, as they are
      --  strictly identical (both check that A + 1 is in range of Integer).
      --  The range check is the one to eliminate here, as it corresponds to
      --  nothing in the Ada code. But integer_from_int_ cannot be removed,
      --  So the idea is to remove overflow_check and to deleguate its
      --  reason (VC_Overflow_Check) to integer_from_int_. e.g.
      --
      --  B := #sloc# "gnatprove:VC_OVERFLOW_CHECK"
      --         integer_from_int_ (integer_to_int (A) + 1)
      --
      --  This feature can only record one reason at a time, backing up for
      --  a default if none has been pushed; we could make it a real stack;
      --  but one slot is enough for now, and what we would really need in
      --  the future is still a bit unclear, so keep it simple.

      procedure Set_Next (Reason : VC_Kind);
      --  Specify the reason for the next check that will be inserted

      function Pop return VC_Kind;
      --  Extract the reason to be included in a conversion
      --  and reset next reasons to default.

   private
      Default_Reason : constant VC_Kind := VC_Range_Check;
      Next_Reason    : VC_Kind := Default_Reason;
   end Conversion_Reason;

   -----------------------
   -- Conversion_Reason --
   -----------------------

   package body Conversion_Reason is

      ---------
      -- Pop --
      ---------

      function Pop return VC_Kind is
         Result : constant VC_Kind := Next_Reason;
      begin
         Next_Reason := Default_Reason;
         return Result;
      end Pop;

      --------------
      -- Set_Next --
      --------------

      procedure Set_Next (Reason : VC_Kind) is
      begin
         Next_Reason := Reason;
      end Set_Next;

   end Conversion_Reason;

   -----------------------
   -- Insert_Conversion --
   -----------------------

   function Insert_Conversion
      (Domain   : EW_Domain;
       Ada_Node : Node_Id := Empty;
       Expr     : W_Expr_Id;
       To       : W_Base_Type_Id;
       From     : W_Base_Type_Id;
       By       : W_Base_Type_OId := Why_Empty) return W_Expr_Id
   is
      Base   : constant W_Base_Type_Id := LCA (To, From);

      function Insert_Single_Conversion
        (To   : W_Base_Type_Id;
         From : W_Base_Type_Id;
         Expr : W_Expr_Id) return W_Expr_Id;
      --  Assuming that there is at most one step between To and From in the
      --  type hierarchy (i.e. that it exists a conversion from From
      --  to To; a counterexample would be two abstract types whose base
      --  types differ), insert the corresponding conversion.

      function Insert_Overflow_Check (Expr : W_Expr_Id) return W_Expr_Id;
      --  If it makes sense in the context, insert an overflow check
      --  on the top of Expr

      ---------------------------
      -- Insert_Overflow_Check --
      ---------------------------

      function Insert_Overflow_Check (Expr : W_Expr_Id) return W_Expr_Id is
      begin
         if Domain /= EW_Prog
           or else Get_Base_Type (By) /= EW_Abstract
         then
            return Expr;
         end if;

         --  If To and From are equal, the conversion from the base type to
         --  To will introduce a range check that is identical to the overflow
         --  check. So do not generate the duplicated overflow check, just
         --  change the label of the next conversion.

         if Eq (To, By) then
            Conversion_Reason.Set_Next (VC_Overflow_Check);
            return Expr;

         --  Otherwise, this is the regular case: the range check and the
         --  the overflow check will be different, so we cannot count on the
         --  conversion scheme to introduce the second.

         else
            return
              New_Located_Call
                (Domain   => Domain,
                 Ada_Node => Ada_Node,
                 Name     =>
                   Overflow_Check_Name.Id (Full_Name (Get_Ada_Node (+By))),
                 Progs    => (1 => +Expr),
                 Reason   => VC_Overflow_Check);
         end if;
      end Insert_Overflow_Check;

      ------------------------------
      -- Insert_Single_Conversion --
      ------------------------------

      function Insert_Single_Conversion
        (To   : W_Base_Type_Id;
         From : W_Base_Type_Id;
         Expr : W_Expr_Id) return W_Expr_Id is
      begin
         if Eq (From, To) then
            return Expr;
         else
            declare
               Name : constant W_Identifier_Id :=
                        Conversion_Name (From => From, To => To);
            begin
               --  Conversions from a base why type to an Ada type should
               --  generate a check in program space.

               if Domain = EW_Prog
                 and then Get_Base_Type (From) in EW_Scalar
                 and then not (Get_Base_Type (To) in EW_Scalar)
               then
                  return
                    New_Located_Call
                      (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => To_Program_Space (Name),
                       Progs    => (1 => +Expr),
                       Reason   => Conversion_Reason.Pop);

               --  In any other case (logic space, or conversions to a more
               --  general type), no check is needed.

               else
                  return
                    New_Call
                      (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => Name,
                       Args     => (1 => +Expr));
               end if;
            end;
         end if;
      end Insert_Single_Conversion;

   --  Start of processing for Insert_Conversion

   begin
      if By /= Why_Empty then
         return
           Insert_Conversion
             (Domain   => Domain,
              Ada_Node => Ada_Node,
              To       => To,
              From     => Base,
              By       => Why_Empty,
              Expr     =>
                Insert_Overflow_Check
                  (Expr =>
                     Insert_Conversion
                       (Domain   => Domain,
                        Ada_Node => Ada_Node,
                        To       => Base,
                        From     => From,
                        By       => Why_Empty,
                        Expr     => Expr)));
      end if;

      if Eq (To, From) then
         return Expr;
      end if;

      declare
         Up_From : constant W_Base_Type_Id := Up (From, Base);
         Up_To   : constant W_Base_Type_Id := Up (To, Base);
      begin
         return
           Insert_Single_Conversion
             (To   => To,
              From => Up_To,
              Expr =>
                Insert_Conversion
                  (Domain   => Domain,
                   Ada_Node => Ada_Node,
                   To       => Up_To,
                   From     => Up_From,
                   By       => Why_Empty,
                   Expr     =>
                     Insert_Single_Conversion
                       (To   => Up_From,
                        From => From,
                        Expr => Expr)));
      end;
   end Insert_Conversion;

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

   --------------------
   -- New_Range_Expr --
   --------------------

   function New_Range_Expr
     (Domain    : EW_Domain;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id) return W_Expr_Id
   is
   begin
      return
         New_And_Then_Expr
           (Left  =>
              New_Comparison
                (Domain    => Domain,
                 Arg_Types => New_Base_Type (Base_Type => EW_Int),
                 Cmp       => EW_Le,
                 Left      => +Low,
                 Right     => +Expr),
            Right  =>
              New_Comparison
                (Domain    => Domain,
                 Arg_Types => New_Base_Type (Base_Type => EW_Int),
                 Cmp       => EW_Le,
                 Left      => +Expr,
                 Right     => High),
            Domain => Domain);
   end New_Range_Expr;

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

   function New_Simpl_Any_Expr
     (Domain   : EW_Domain;
      Arg_Type : W_Primitive_Type_Id;
      Id       : W_Identifier_OId;
      Pred     : W_Pred_Id) return W_Expr_Id is
   begin
      case Domain is
         when EW_Term => return +New_Simpl_Epsilon_Term (Arg_Type, Id, Pred);
         when EW_Prog => return +New_Simpl_Any_Prog (Arg_Type, Pred);
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
