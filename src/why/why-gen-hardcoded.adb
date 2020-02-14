------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    W H Y - G E N - H A R D C O D E D                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2020-2020, AdaCore                     --
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

with Common_Containers;  use Common_Containers;
with Errout;             use Errout;
with Namet;              use Namet;
with Snames;             use Snames;
with SPARK_Atree;        use SPARK_Atree;
with VC_Kinds;           use VC_Kinds;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Modules;  use Why.Atree.Modules;
with Why.Conversions;    use Why.Conversions;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Expr;       use Why.Gen.Expr;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Progs;      use Why.Gen.Progs;
with Why.Inter;          use Why.Inter;

package body Why.Gen.Hardcoded is
   package BIN renames Big_Integers_Names; use BIN;

   -------------------------------------
   -- Emit_Hardcoded_Type_Declaration --
   -------------------------------------

   procedure Emit_Hardcoded_Type_Declaration
     (P : W_Section_Id;
      E : Entity_Id)
   is
      Alias : W_Type_Id;
   begin

      --  The Why3 type used to represent the type is stored in Alias
      --  The following case statement is meant to be extended in the
      --  future.

      case Get_Hardcoded_Unit (E) is
         when Big_Integers => Alias := EW_Int_Type;
      end case;

      Emit (P,
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
      return     W_Expr_Id
   is
      T           : W_Expr_Id;
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

         if Args'Length = 3 and then Name_String = BIN.In_Range then

            T := New_And_Expr
                   (Left  => New_Call
                              (Ada_Node => Ada_Node,
                               Domain   => Domain,
                               Name     => Int_Infix_Le,
                               Args     => (1 => Args (2),
                                            2 => Args (1)),
                               Typ      => Type_Of_Node (Etype (Subp))),
                    Right => New_Call
                               (Ada_Node => Ada_Node,
                                Domain   => Domain,
                                Name     => Int_Infix_Le,
                                Args     => (1 => Args (1),
                                             2 => Args (3)),
                                Typ      => Type_Of_Node (Etype (Subp))),
                    Domain => Domain);

         --  This block transforms the comparison operators, binary operators,
         --  Min, Max and Greatest_Common_Divisor.

         elsif Args'Length = 2 then

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

               if Domain = EW_Prog
                 and then
                   (Chars (Subp) in Name_Op_Divide
                                  | Name_Op_Mod
                                  | Name_Op_Rem
                      or else Name_String = BIN.Gcd)
               then
                  pragma Assert (Present (Ada_Node));

                  declare
                     Reason : constant VC_Kind :=
                       (if Name_String = BIN.Gcd
                        then VC_Precondition
                        else VC_Division_Check);
                  begin
                     T :=
                       New_VC_Call
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Name     => To_Program_Space (Name),
                          Progs    => (1 => Left_Rep, 2 => Right_Rep),
                          Reason   => Reason,
                          Typ      => Base);
                  end;
               else
                  T := New_Call
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Name     => Name,
                     Args     => (1 => Left_Rep,
                                  2 => Right_Rep),
                     Typ      => Base);
               end if;
            end;

         --  This block transforms the unary operators and Is_Valid

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

      else
         raise Program_Error;
      end if;
      return T;
   end Transform_Hardcoded_Function_Call;

end Why.Gen.Hardcoded;
