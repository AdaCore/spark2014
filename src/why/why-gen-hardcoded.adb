------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    W H Y - G E N - H A R D C O D E D                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2020-2021, AdaCore                     --
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

with Common_Containers;   use Common_Containers;
with Errout;              use Errout;
with Namet;               use Namet;
with Snames;              use Snames;
with SPARK_Util.Types;    use SPARK_Util.Types;
with Stringt;             use Stringt;
with Uintp;               use Uintp;
with Urealp;              use Urealp;
with VC_Kinds;            use VC_Kinds;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Progs;       use Why.Gen.Progs;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;

package body Why.Gen.Hardcoded is
   package BIN renames Big_Integers_Names; use BIN;
   package BRN renames Big_Reals_Names;    use BRN;

   function Uint_From_String (Str_Value : String) return Uint;
   --  Read an integer value from a string. Might raise Constraint_Error.

   -------------------------------------
   -- Emit_Hardcoded_Type_Declaration --
   -------------------------------------

   procedure Emit_Hardcoded_Type_Declaration (Th : Theory_UC; E : Entity_Id) is
      Alias : W_Type_Id;
   begin

      --  The Why3 type used to represent the type is stored in Alias
      --  The following case statement is meant to be extended in the
      --  future.

      case Get_Hardcoded_Unit (E) is
         when Big_Integers => Alias := EW_Int_Type;
         when Big_Reals    => Alias := EW_Real_Type;
      end case;

      Emit (Th,
            New_Type_Decl
              (Name  => To_Name (WNE_Rec_Rep),
               Alias => Alias));

   end Emit_Hardcoded_Type_Declaration;

   ---------------------------------------
   -- Transform_Hardcoded_Function_Call --
   ---------------------------------------

   function Transform_Hardcoded_Function_Call
     (Subp     : Entity_Id;
      Args     : W_Expr_Array;
      Domain   : EW_Domain;
      Ada_Node : Node_Id)
      return W_Expr_Id
   is
      T           : W_Expr_Id := Why_Empty;
      Name_String : constant String :=
        Get_Name_String (Chars (Subp));
   begin

      --  Conversion functions are translated in the same way in
      --  the Big_Integers package and its generic subpackages.

      if (Is_From_Hardcoded_Generic_Unit (Subp, Big_Integers)
        and then Name_String in BIN.Generic_To_Big_Integer
                              | BIN.Generic_From_Big_Integer)
            or else
         (Is_From_Hardcoded_Unit (Subp, Big_Integers)
        and then Name_String in BIN.To_Big_Integer | BIN.To_Integer)
      then

         --  Conversion from an integer type to type Big_Integer, no check
         --  needed.

         if Name_String in BIN.Generic_To_Big_Integer | BIN.To_Big_Integer then
            T := Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                           Domain   => Domain,
                                           Expr     => Args (1),
                                           To       => EW_Int_Type);

            --  Big_Integer is an alias of int in Why3, but in GNAT2why,
            --  they are different types. We reestablish the proper type
            --  in the AST by adding a dummy node.

            T := New_Label (Labels => Symbol_Sets.Empty_Set,
                            Def    => T,
                            Domain => Domain,
                            Typ    => Type_Of_Node (Etype (Subp)));

         --  Conversion from a Big_Integer to an integer type

         elsif Name_String in BIN.Generic_From_Big_Integer
                            | BIN.To_Integer
         then

            T := Insert_Simple_Conversion
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Expr     => New_Label (Ada_Node => Ada_Node,
                                      Domain   => Domain,
                                      Labels   => Symbol_Sets.Empty_Set,
                                      Def      => Args (1),
                                      Typ      => EW_Int_Type),
               To       => Type_Of_Node (Etype (Subp)));

            --  A check is needed when in the program domain. We don't use
            --  Insert_Checked_Conversion because it relies on frontend flags
            --  to insert checks on scalar conversions. These flags are not
            --  set for these conversions.

            if Domain = EW_Prog then
               T := +Sequence
                 (Ada_Node => Ada_Node,
                  Left     =>
                    New_Ignore
                      (Ada_Node => Ada_Node,
                       Prog     => Do_Range_Check
                         (Ada_Node   => Ada_Node,
                          Ty         =>
                            Type_Of_Node (Etype (Subp)),
                          W_Expr     =>

                            --  Do_Range_Check takes integer types in entry,
                            --  but in GNAT2why, Big_Integer is not an integer
                            --  type. We add this dummy node to treat Args (1)
                            --  as an integer type in Do_Range_Check.

                            New_Label
                              (Ada_Node => Ada_Node,
                               Domain   => Domain,
                               Labels   => Symbol_Sets.Empty_Set,
                               Def      => Args (1),
                               Typ      => EW_Int_Type),
                          Check_Kind => RCK_Range)),
                  Right    => +T);
            end if;
         end if;

      --  Transformation of the other functions in Big_Integers

      elsif Is_From_Hardcoded_Unit (Subp, Big_Integers) then

         --  This block transforms the comparison operators, binary operators,
         --  Min, Max and Greatest_Common_Divisor.

         if Args'Length = 2 then

            declare
               Base      : constant W_Type_Id :=
                 Type_Of_Node (Etype (Subp));
               Left_Rep  : constant W_Expr_Id := Args (1);
               Right_Rep : constant W_Expr_Id :=
                 (if Chars (Subp) = Name_Op_Expon
                  then Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                                 Domain   => Domain,
                                                 Expr     => Args (2),
                                                 To       => EW_Int_Type)
                  else Args (2));
               Name : W_Identifier_Id;
            begin

               --  The following block assigns a value to Name which will be
               --  called in New_Call afterwards.

               if Name_String = BIN.Min then
                  Name := M_Int_Minmax.Min;

               elsif Name_String = BIN.Max then
                  Name := M_Int_Minmax.Max;

               elsif Name_String = BIN.Gcd then
                  Name := M_Int_Gcd.Gcd;

               else
                  case Chars (Subp) is
                     when Name_Op_Add      =>
                        Name := Int_Infix_Add;

                     when Name_Op_Subtract =>
                        Name := Int_Infix_Subtr;

                     when Name_Op_Multiply =>
                        Name := Int_Infix_Mult;

                     when Name_Op_Divide   =>
                        Name := M_Int_Div.Div;

                     when Name_Op_Mod      =>
                        Name := M_Int_Div.Mod_Id;

                     when Name_Op_Rem      =>
                        Name := M_Int_Div.Rem_Id;

                     when Name_Op_Expon    =>
                        Name := M_Int_Power.Power;

                     when Name_Op_Eq       =>
                        Name := (if Domain = EW_Term
                                 then M_Integer.Bool_Eq
                                 else Why_Eq);

                     when Name_Op_Lt       =>
                        Name := (if Domain = EW_Term
                                 then M_Integer.Bool_Lt
                                 else Int_Infix_Lt);

                     when Name_Op_Le      =>
                        Name := (if Domain = EW_Term
                                 then M_Integer.Bool_Le
                                 else Int_Infix_Le);

                     when Name_Op_Gt       =>
                        Name := (if Domain = EW_Term
                                 then M_Integer.Bool_Gt
                                 else Int_Infix_Gt);

                     when Name_Op_Ge       =>
                        Name := (if Domain = EW_Term
                                 then M_Integer.Bool_Ge
                                 else Int_Infix_Ge);

                     when others           =>
                        raise Program_Error;
                  end case;
               end if;

               --  Divide, Mod, Rem and Gcd need a division or precondition
               --  check.

               declare
                  Check : constant Boolean :=
                    Domain = EW_Prog
                    and then
                      (Chars (Subp) in Name_Op_Divide
                                     | Name_Op_Mod
                                     | Name_Op_Rem
                        or else Name_String = BIN.Gcd);
                  pragma Assert (if Check then Present (Ada_Node));

                  Reason : constant VC_Kind :=
                    (if Name_String = BIN.Gcd
                     then VC_Precondition
                     else VC_Division_Check);
               begin
                  if Reason = VC_Division_Check then
                     Add_Division_Check_Information
                       (Ada_Node,
                        Divisor => Get_Ada_Node (+Args (2)));
                  end if;

                  T := New_Operator_Call
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Name     => Name,
                     Args     => (1 => Left_Rep, 2 => Right_Rep),
                     Reason   => Reason,
                     Check    => Check,
                     Typ      => Base);
               end;
            end;

         --  This block transforms the unary operators, Is_Valid, and
         --  From_String.

         elsif Args'Length = 1 then

            --  Is_Valid is handled as the attribute 'Valid

            if Name_String = BIN.Is_Valid and then Args'Length = 1 then
               pragma Assert (Args'Length = 1);
               Error_Msg_F ("?function Is_Valid is assumed to return True",
                            Ada_Node);

               if Domain = EW_Prog then
                  T := +Sequence (Ada_Node => Ada_Node,
                                  Left  => New_Ignore (Prog => +Args (1)),
                                  Right => New_Literal (Value => EW_True));
               else
                  T := Why.Conversions."+"(New_Literal (Value  => EW_True,
                                                        Domain => Domain));
               end if;

            --  Imprecise translation of From_String. This is a function taking
            --  a string representing an integer value.
            --  We translate From_String (Val) as:
            --    int_value (of_string (val))
            --  This translation is imprecise as int_value and of_string are
            --  abstract Why3 functions left mostly uninterpreted.
            --  In the special case where Val is a string literal, a more
            --  precise translation is attempted first, see
            --  Transform_Hardcoded_Literal.

            elsif Name_String = BIN.From_String then
               T :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Of_String_Id,
                    Args     => (1 => Args (1)));

               T := New_Operator_Call
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Name     => M_Builtin_From_Image.Int_Value,
                  Args     => (1 => T),
                  Reason   => VC_Precondition,
                  Check    => Domain = EW_Prog,
                  Typ      => EW_Int_Type);

               T := New_Label
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Labels   => Symbol_Sets.Empty_Set,
                  Def      => T,
                  Typ      => Type_Of_Node (Etype (Subp)));

            elsif Chars (Subp) = Name_Op_Add then
               T := Args (1);
            else
               declare
                  Base     : constant W_Type_Id :=
                    Type_Of_Node (Etype (Subp));
                  Name : W_Identifier_Id;
               begin
                  case Chars (Subp) is
                     when Name_Op_Subtract => Name := Int_Unary_Minus;
                     when Name_Op_Abs      => Name := M_Int_Abs.Abs_Id;
                     when others           => raise Program_Error;
                  end case;

                  T := New_Call (Domain   => Domain,
                                 Ada_Node => Ada_Node,
                                 Name     => Name,
                                 Args     => (1 => Args (1)),
                                 Typ      => Base);
               end;
            end if;

         else
            raise Program_Error;
         end if;

      --  Transformation of Big_Reals

      elsif Is_From_Hardcoded_Unit (Subp, Big_Reals) then
         if Args'Length = 2 then

            --  Imprecise translation of From_Universal_Image. This is a
            --  function taking two strings representing integer values
            --  standing for the numerator and denominator of a big real.
            --  We translate From_Universal_Value (Num, Den) as:
            --    to_real (int_value (of_string (num))) /
            --      to_real (int_value (of_string (den)))
            --  This translation is imprecise as int_value and of_string are
            --  both abstract Why3 functions left mostly uninterpreted.
            --  In the special case where Num and Den are string literals, a
            --  more precise translation is attempted first, see
            --  Transform_Hardcoded_Literal.

            if Name_String = BRN.From_Universal_Image then
               declare
                  Num : W_Expr_Id := New_Call
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Name     => Of_String_Id,
                     Args     => (1 => Args (1)));
                  Den : W_Expr_Id := New_Call
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Name     => Of_String_Id,
                     Args     => (1 => Args (2)));

               begin
                  --  Translate each operand from an image to an integer

                  Num := New_Operator_Call
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Name     => M_Builtin_From_Image.Int_Value,
                     Args     => (1 => Num),
                     Reason   => VC_Precondition,
                     Check    => Domain = EW_Prog,
                     Typ      => EW_Int_Type);
                  Den := New_Operator_Call
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Name     => M_Builtin_From_Image.Int_Value,
                     Args     => (1 => Den),
                     Reason   => VC_Precondition,
                     Check    => Domain = EW_Prog,
                     Typ      => EW_Int_Type);

                  --  Insert a conversion to real on both operands

                  Num  := New_Call
                    (Domain   => Domain,
                     Ada_Node => Ada_Node,
                     Name     => M_Real_From_Int.From_Int,
                     Args     => (1 => Num));
                  Den := New_Call
                    (Domain   => Domain,
                     Ada_Node => Ada_Node,
                     Name     => M_Real_From_Int.From_Int,
                     Args     => (1 => Den));

                  --  Reconstruct the real value by doing the division

                  Add_Division_Check_Information
                    (Ada_Node,
                     Divisor => Get_Ada_Node (+Args (2)));

                  T := New_Operator_Call
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Name     => Real_Infix_Div,
                     Fix_Name => True,
                     Args     => (1 => Num, 2 => Den),
                     Reason   => VC_Division_Check,
                     Check    => Domain = EW_Prog,
                     Typ      => EW_Real_Type);

                  T := New_Label
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Labels   => Symbol_Sets.Empty_Set,
                     Def      => T,
                     Typ      => Type_Of_Node (Etype (Subp)));
               end;

            --  This block transforms the comparison operators, binary
            --  operators, Min, and Max.

            else
               declare
                  Base      : constant W_Type_Id :=
                    Type_Of_Node (Etype (Subp));
                  Left_Rep  : W_Expr_Id := Args (1);
                  Right_Rep : W_Expr_Id := Args (2);
                  Name      : W_Identifier_Id;
               begin

                  --  The following block assigns a value to Name which will be
                  --  called in New_Call afterwards.

                  if Name_String = BRN.Min then
                     Name := M_Real_Minmax.Min;

                  elsif Name_String = BIN.Max then
                     Name := M_Real_Minmax.Max;

                  else
                     case Chars (Subp) is
                        when Name_Op_Add      =>
                           Name := Real_Infix_Add;

                        when Name_Op_Subtract =>
                           Name := Real_Infix_Subtr;

                        when Name_Op_Multiply =>
                           Name := Real_Infix_Mult;

                        when Name_Op_Divide   =>
                           --  If the division is done on big integers, we need
                           --  to insert a conversion to real on both operands.

                           if Is_From_Hardcoded_Unit
                             (Root_Retysp (Etype (First_Formal (Subp))),
                              Big_Integers)
                           then
                              Left_Rep  := New_Call
                                (Domain   => Domain,
                                 Ada_Node => Ada_Node,
                                 Name     => M_Real_From_Int.From_Int,
                                 Args     => (1 => Left_Rep));
                              Right_Rep := New_Call
                                (Domain   => Domain,
                                 Ada_Node => Ada_Node,
                                 Name     => M_Real_From_Int.From_Int,
                                 Args     => (1 => Right_Rep));
                           end if;

                           Name := Real_Infix_Div;

                        when Name_Op_Expon    =>
                           --  For exponentiation, a mathematical integer is
                           --  expected for the second parameter.

                           Right_Rep := Insert_Simple_Conversion
                             (Ada_Node => Ada_Node,
                              Domain   => Domain,
                              Expr     => Right_Rep,
                              To       => EW_Int_Type);
                           Name := M_Real_Power.Power;

                        when Name_Op_Eq       =>
                           Name := (if Domain = EW_Term
                                    then M_Real.Bool_Eq
                                    elsif Domain = EW_Pred
                                    then Why_Eq
                                    else Real_Infix_Eq);

                        when Name_Op_Lt       =>
                           Name := (if Domain = EW_Term
                                    then M_Real.Bool_Lt
                                    else Real_Infix_Lt);

                        when Name_Op_Le      =>
                           Name := (if Domain = EW_Term
                                    then M_Real.Bool_Le
                                    else Real_Infix_Le);

                        when Name_Op_Gt       =>
                           Name := (if Domain = EW_Term
                                    then M_Real.Bool_Gt
                                    else Real_Infix_Gt);

                        when Name_Op_Ge       =>
                           Name := (if Domain = EW_Term
                                    then M_Real.Bool_Ge
                                    else Real_Infix_Ge);

                        when others           =>
                           raise Program_Error;
                     end case;
                  end if;

                  --  Divide needs a division check

                  declare
                     Check : constant Boolean :=
                       Domain = EW_Prog
                       and then Chars (Subp) = Name_Op_Divide;
                  begin
                     pragma Assert (if Check then Present (Ada_Node));

                     Add_Division_Check_Information
                       (Ada_Node,
                        Divisor => Get_Ada_Node (+Args (2)));

                     T := New_Operator_Call
                       (Ada_Node => Ada_Node,
                        Domain   => Domain,
                        Name     => Name,
                        Fix_Name => True,
                        Args     => (1 => Left_Rep, 2 => Right_Rep),
                        Reason   => VC_Division_Check,
                        Check    => Check,
                        Typ      => Base);
                  end;
               end;
            end if;

         --  This block transforms the unary operators, Is_Valid, and
         --  From_String.

         elsif Args'Length = 1 then

            --  Is_Valid is handled as the attribute 'Valid

            if Name_String = BRN.Is_Valid and then Args'Length = 1 then
               pragma Assert (Args'Length = 1);
               Error_Msg_F ("?function Is_Valid is assumed to return True",
                            Ada_Node);

               if Domain = EW_Prog then
                  T := +Sequence (Ada_Node => Ada_Node,
                                  Left  => New_Ignore (Prog => +Args (1)),
                                  Right => New_Literal (Value => EW_True));
               else
                  T := Why.Conversions."+"(New_Literal (Value  => EW_True,
                                                        Domain => Domain));
               end if;

            --  Imprecise translation of From_String. This is a function taking
            --  a string representing a real value.
            --  We translate From_String (Val) as:
            --    real_value (of_string (val))
            --  This translation is imprecise as real_value and of_string are
            --  abstract Why3 functions left mostly uninterpreted.
            --  In the special case where Val is a string literal, a more
            --  precise translation is attempted first, see
            --  Transform_Hardcoded_Literal.

            elsif Name_String = BRN.From_String then
               T :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Of_String_Id,
                    Args     => (1 => Args (1)));

               T := New_Operator_Call
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Name     => M_Builtin_From_Image.Real_Value,
                  Args     => (1 => T),
                  Reason   => VC_Precondition,
                  Check    => Domain = EW_Prog,
                  Typ      => EW_Real_Type);

               T := New_Label
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Labels   => Symbol_Sets.Empty_Set,
                  Def      => T,
                  Typ      => Type_Of_Node (Etype (Subp)));

            elsif Chars (Subp) = Name_Op_Add then
               T := Args (1);
            else
               declare
                  Base : constant W_Type_Id :=
                    Type_Of_Node (Etype (Subp));
                  Name : W_Identifier_Id;
               begin
                  case Chars (Subp) is
                     when Name_Op_Subtract => Name := Real_Unary_Minus;
                     when Name_Op_Abs      => Name := M_Real_Abs.Abs_Id;
                     when others           => raise Program_Error;
                  end case;

                  T := New_Call (Domain   => Domain,
                                 Ada_Node => Ada_Node,
                                 Name     => Name,
                                 Args     => (1 => Args (1)),
                                 Typ      => Base);
               end;
            end if;

         --  Otherwise, we are converting from a floting point or fixed
         --  point type.

         else
            raise Program_Error;
         end if;
      elsif Is_From_Hardcoded_Generic_Unit (Subp, Big_Reals)
        and then Name_String = BRN.Generic_To_Big_Real
      then
         pragma Assert (Args'Length = 1);

         declare
            From_Ty : constant Entity_Id :=
              Retysp (Etype (First_Formal (Subp)));
         begin
            if Is_Fixed_Point_Type (From_Ty) then
               T := New_Call
                 (Domain   => Domain,
                  Ada_Node => Ada_Node,
                  Name     => Real_Infix_Mult,
                  Args     =>
                    (1 => New_Call
                         (Domain   => Domain,
                          Ada_Node => Ada_Node,
                          Name     => M_Real_From_Int.From_Int,
                          Args     => (1 => Args (1))),
                     2 => New_Real_Constant
                       (Ada_Node => Ada_Node,
                        Value    => Small_Value (From_Ty))),
                  Typ      => Type_Of_Node (Etype (Subp)));
            else
               pragma Assert (Is_Floating_Point_Type (From_Ty));
               T := New_Call
                 (Domain   => Domain,
                  Ada_Node => Ada_Node,
                  Name     => MF_Floats (Base_Why_Type (From_Ty)).To_Real,
                  Args     => (1 => Args (1)),
                  Typ      => Type_Of_Node (Etype (Subp)));
            end if;
         end;
      else
         raise Program_Error;
      end if;
      return T;
   end Transform_Hardcoded_Function_Call;

   ---------------------------------
   -- Transform_Hardcoded_Literal --
   ---------------------------------

   function Transform_Hardcoded_Literal
     (Call   : Node_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Subp      : constant Entity_Id := Get_Called_Entity (Call);
      Root_Type : constant W_Type_Id :=
        Type_Of_Node (Root_Retysp (Etype (Call)));
      Actual    : Node_Id := First_Actual (Call);
   begin
      --  Go over the actuals to check that their are all string literals

      while Present (Actual) loop
         if Nkind (Actual) /= N_String_Literal then
            return Why_Empty;
         end if;
         Actual := Next_Actual (Actual);
      end loop;

      --  Transformation of integer literals from Big_Integers

      if Is_From_Hardcoded_Unit (Subp, Big_Integers) then
         pragma Assert (Get_Name_String (Chars (Subp)) = BIN.From_String);

         declare
            String_Literal : constant Node_Id := First_Actual (Call);
            pragma Assert
              (Present (String_Literal)
               and then No (Next_Actual (String_Literal)));
            Str_Value      : constant String_Id := Strval (String_Literal);
            Len            : constant Nat := String_Length (Str_Value);
            Value_String   : String (1 .. Natural (Len));
            UI_Val         : Uint;

         begin
            --  Fetch the value of the string literal

            String_To_Name_Buffer (Str_Value);
            Value_String := Name_Buffer (1 .. Natural (Len));

            --  Get its value as a Uint

            UI_Val := Uint_From_String (Value_String);

            --  Return the appropriate integer constant

            return New_Label
              (Ada_Node => String_Literal,
               Domain   => Domain,
               Labels   => Symbol_Sets.Empty_Set,
               Def      => New_Integer_Constant (Ada_Node => String_Literal,
                                                 Value    => UI_Val),
               Typ      => Root_Type);

         exception
            when Constraint_Error =>
               --  If we did not manage to transform the literal to an integer,
               --  default to the imprecise translation.

               return Why_Empty;
         end;

      --  Transformation of real literals from Big_Reals

      elsif Is_From_Hardcoded_Unit (Subp, Big_Reals) then
         if Get_Name_String (Chars (Subp)) = BRN.From_String then
            declare
               function UI_From_Integer is new UI_From_Integral (Integer);

               String_Literal : constant Node_Id := First_Actual (Call);
               pragma Assert
                 (Present (String_Literal)
                  and then No (Next_Actual (String_Literal)));
               Str_Value      : constant String_Id := Strval
                 (String_Literal);
               Len            : constant Nat := String_Length (Str_Value);
               Arg            : String (1 .. Natural (Len));
               Frac           : Uint;
               Exp            : Uint := Uint_0;
               Pow            : Int := 0;
               Index          : Natural := 0;
               Last           : Natural := Arg'Last;
               Num            : Uint;
               Den            : Uint;
               Result         : W_Expr_Id;

            begin
               --  Fetch the value of the string literal

               String_To_Name_Buffer (Str_Value);
               Arg := Name_Buffer (Arg'Range);

               --  Parse the real value. The code is inspired from the
               --  implementation of Big_Reals.From_String.

               --  Search for:
               --    The last index before the dot, stored in Index,
               --    The last index before the exponent, stored in Last

               for J in reverse Arg'Range loop
                  if Arg (J) in 'e' | 'E' then
                     if Last /= Arg'Last then
                        raise Constraint_Error
                          with "multiple exponents specified";
                     end if;

                     Last := J - 1;
                     Pow := 0;
                     Exp := UI_From_Integer
                       (Integer'Value (Arg (J + 1 .. Arg'Last)));

                  elsif Arg (J) = '.' then
                     Index := J - 1;
                     exit;
                  else
                     Pow := Pow + 1;
                  end if;
               end loop;

               --  Pow is the number of digits after the dot

               pragma Assert
                 (if Index /= 0 then Pow = Int (Last - Index - 1));

               --  Exp is the exponent if one was supplied 0 otherwise

               pragma Assert
                 (if Last /= Arg'Last
                  then Exp = Uint_From_String (Arg (Last + 2 .. Arg'Last))
                  else Exp = Uint_0);

               if Index = 0 then
                  raise Constraint_Error with "invalid real value";
               end if;

               --  From <Int> . <Frac> E <Exp>,
               --  generate
               --     ((Int * 10 ** Pow +/- Frac) / 10 ** Pow) * 10 ** Exp

               Den := Uint_10 ** Pow;
               Num := Uint_From_String (Arg (Arg'First .. Index)) * Den;
               Frac := Uint_From_String (Arg (Index + 2 .. Last));

               if Num < Uint_0 then
                  Num := Num - Frac;
               else
                  Num := Num + Frac;
               end if;

               if Exp > Uint_0 then
                  Num := Num * Uint_10 ** Exp;
               elsif Exp < Uint_0 then
                  Den := Den * Uint_10 ** (-Exp);
               end if;

               --  Return the appropriate real constant. There is no possible
               --  division by zero, as Den cannot be 0.

               declare
                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Prog and then Den /= Uint_0
                     then EW_Pterm else Domain);
                  W_Args    : constant W_Expr_Array :=
                    (1 => New_Real_Constant
                       (Ada_Node => String_Literal,
                        Value    => UR_From_Uint (Num)),
                     2 => New_Real_Constant
                       (Ada_Node => String_Literal,
                        Value    => UR_From_Uint (Den)));
                  Name      : constant W_Identifier_Id :=
                    (if Subdomain = EW_Prog then Real_Infix_Div
                     else M_Real.Div);
               begin
                  Result := New_Operator_Call
                    (Ada_Node => Call,
                     Domain   => Subdomain,
                     Name     => Name,
                     Fix_Name => True,
                     Args     => W_Args,
                     Reason   => VC_Division_Check,
                     Check    => False,
                     Typ      => EW_Real_Type);
               end;

               return New_Label
                 (Ada_Node => String_Literal,
                  Domain   => Domain,
                  Labels   => Symbol_Sets.Empty_Set,
                  Def      => Result,
                  Typ      => Root_Type);

            exception
               when Constraint_Error =>
                  --  If the parameter is not a valid real value, or if its
                  --  components exceed Long_Long_Integer, then default to
                  --  imprecise translation.

                  return Why_Empty;
            end;

         elsif Get_Name_String (Chars (Subp)) = BRN.From_Universal_Image then

            declare
               Num_Literal : constant Node_Id := First_Actual (Call);
               pragma Assert (Present (Num_Literal));
               Den_Literal : constant Node_Id := Next_Actual (Num_Literal);
               pragma Assert
                 (Present (Den_Literal)
                  and then No (Next_Actual (Den_Literal)));
               Num_Str_Id  : constant String_Id := Strval (Num_Literal);
               Den_Str_Id  : constant String_Id := Strval (Den_Literal);
               Num_Len     : constant Nat := String_Length (Num_Str_Id);
               Den_Len     : constant Nat := String_Length (Den_Str_Id);
               Num_String  : String (1 .. Natural (Num_Len));
               Den_String  : String (1 .. Natural (Den_Len));
               Num_Val     : Uint;
               Den_Val     : Uint;
               Result      : W_Expr_Id;

            begin
               --  Fetch the value of the string literals

               String_To_Name_Buffer (Num_Str_Id);
               Num_String := Name_Buffer (1 .. Natural (Num_Len));
               String_To_Name_Buffer (Den_Str_Id);
               Den_String := Name_Buffer (1 .. Natural (Den_Len));

               --  Get their values as a Uint

               Num_Val := Uint_From_String (Num_String);
               Den_Val := Uint_From_String (Den_String);

               --  Return the appropriate real constant. Only emit a division
               --  check if Den_Val is 0.

               declare
                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Prog and then Den_Val /= Uint_0
                     then EW_Pterm else Domain);
                  W_Args    : constant W_Expr_Array :=
                    (1 => New_Real_Constant
                       (Ada_Node => Num_Literal,
                        Value    => UR_From_Uint (Num_Val)),
                     2 => New_Real_Constant
                       (Ada_Node => Den_Literal,
                        Value    => UR_From_Uint (Den_Val)));
                  Name      : constant W_Identifier_Id :=
                    (if Subdomain = EW_Prog then Real_Infix_Div
                     else M_Real.Div);
               begin
                  Add_Division_Check_Information
                    (Call,
                     Divisor => Den_Literal);

                  Result := New_Operator_Call
                    (Ada_Node => Call,
                     Domain   => Subdomain,
                     Name     => Name,
                     Fix_Name => True,
                     Args     => W_Args,
                     Reason   => VC_Division_Check,
                     Check    => Subdomain = EW_Prog,
                     Typ      => EW_Real_Type);
               end;

               return New_Label
                 (Ada_Node => Call,
                  Domain   => Domain,
                  Labels   => Symbol_Sets.Empty_Set,
                  Def      => Result,
                  Typ      => Root_Type);

            exception
               when Constraint_Error =>
                  --  If the parameter is not a valid real value, or if its
                  --  components exceed Long_Long_Integer, then default to
                  --  imprecise translation.

                  return Why_Empty;
            end;
         else
            raise Program_Error;
         end if;
      else
         raise Program_Error;
      end if;
   end Transform_Hardcoded_Literal;

   ----------------------
   -- Uint_From_String --
   ----------------------

   function Uint_From_String (Str_Value : String) return Uint is

      function UI_From_Long_Long_Long_Integer is
        new UI_From_Integral (Long_Long_Long_Integer);

      Def    : Long_Long_Long_Integer;
      UI_Val : Uint;

   begin
      --  Try to get the value of Str_Value as a long long long integer

      Def := Long_Long_Long_Integer'Value (Str_Value);

      --  Transform Def into a Uint

      UI_Val := UI_From_Long_Long_Long_Integer (Def);

      return UI_Val;

   exception
      when Constraint_Error =>

         --  Otherwise, try the slow path

         declare
            Neg    : Boolean := False;
            J      : Natural := Str_Value'First;
            Result : Uint := Uint_0;

         begin
            --  Scan past leading blanks

            while J <= Str_Value'Last and then Str_Value (J) = ' ' loop
               J := J + 1;
            end loop;

            if J > Str_Value'Last then
               raise;
            end if;

            --  Scan and store negative sign if found

            if Str_Value (J) = '-' then
               Neg := True;
               J   := J + 1;
            end if;

            --  Scan decimal value. If something which is not between '0' and
            --  '9' or '_' is found ('#' or 'E') we don't support it yet.

            while J <= Str_Value'Last loop
               if Str_Value (J) in '0' .. '9' then
                  Result :=
                    UI_Add
                      (UI_Mul (Result, Uint_10),
                       (case Str_Value (J) is
                           when '0'    => Uint_0,
                           when '1'    => Uint_1,
                           when '2'    => Uint_2,
                           when '3'    => Uint_3,
                           when '4'    => Uint_4,
                           when '5'    => Uint_5,
                           when '6'    => Uint_6,
                           when '7'    => Uint_7,
                           when '8'    => Uint_8,
                           when '9'    => Uint_9,
                           when others => raise Program_Error));
               elsif Str_Value (J) = '_' then
                  if J = Str_Value'Last or else Str_Value (J + 1) = '_' then
                     raise;
                  end if;
               else
                  raise;
               end if;

               J := J + 1;
            end loop;

            if Neg then
               return UI_Negate (Result);
            else
               return Result;
            end if;
         end;
   end Uint_From_String;

end Why.Gen.Hardcoded;
