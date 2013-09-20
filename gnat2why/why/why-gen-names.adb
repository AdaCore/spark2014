------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Stand;               use Stand;
with String_Utils;        use String_Utils;

with SPARK_Util;          use SPARK_Util;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Conversions;     use Why.Conversions;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;

package body Why.Gen.Names is

   function Uint_To_Positive (U : Uint) return Positive;
   --  Limited version of conversion that only works for 1 to 4

   Pre_Computed_Idents : array (Why_Name_Enum) of W_Identifier_Id :=
     (others => Why_Empty);
   --  This array is used to precompute all fixed idents.

   --------------------
   -- Ada_Array_Name --
   --------------------

   function Ada_Array_Name (Dimension : Pos) return Why_Name_Enum
   is
   begin
      case Dimension is
         when 1 => return WNE_Array_1;
         when 2 => return WNE_Array_2;
         when 3 => return WNE_Array_3;
         when 4 => return WNE_Array_4;
         when others => raise Program_Error;
      end case;
   end Ada_Array_Name;

   ----------------------
   -- Append_Num --
   ----------------------

   function Append_Num (S : String; Count : Positive) return String is
   begin
      return (if Count = 1 then S else S & "_" & Int_Image (Count));
   end Append_Num;

   function Append_Num (S : String; Count : Uint) return String is
   begin
      return Append_Num (S, Uint_To_Positive (Count));
   end Append_Num;

   function Append_Num (S : String; Count : Positive) return W_Identifier_Id is
   begin
      return New_Identifier (Name => Append_Num (S, Count));
   end Append_Num;

   function Append_Num (W : Why_Name_Enum; Count : Positive)
                        return W_Identifier_Id
   is
   begin
      return Append_Num (To_String (W), Count);
   end Append_Num;

   function Append_Num (W : Why_Name_Enum; Count : Uint)
                        return W_Identifier_Id
   is
   begin
      return Append_Num (W, Uint_To_Positive (Count));
   end Append_Num;

   function Append_Num (P, W : Why_Name_Enum; Count : Positive)
                        return W_Identifier_Id
   is
   begin
      return Append_Num (To_String (P) & "." & To_String (W), Count);
   end Append_Num;

   ----------------------
   -- Attr_To_Why_Name --
   ----------------------

   function Attr_To_Why_Name (A : Attribute_Id) return Why_Name_Enum
   is
   begin
      case A is
         when Attribute_First   => return WNE_Attr_First;
         when Attribute_Image   => return WNE_Attr_Image;
         when Attribute_Last    => return WNE_Attr_Last;
         when Attribute_Modulus => return WNE_Attr_Modulus;
         when Attribute_Length  => return WNE_Attr_Length;
         when Attribute_Value   => return WNE_Attr_Value;
         when others =>
            raise Program_Error;
      end case;
   end Attr_To_Why_Name;

   ---------------------
   -- Conversion_Name --
   ---------------------

   function Conversion_Name
      (From : W_Base_Type_Id;
       To   : W_Base_Type_Id) return W_Identifier_Id
   is
      From_Kind : constant EW_Type := Get_Base_Type (From);
      To_Kind   : constant EW_Type := Get_Base_Type (To);
   begin
      case From_Kind is
         when EW_Unit | EW_Prop | EW_Private =>
            raise Not_Implemented;

         when EW_Scalar =>
            case To_Kind is
               when EW_Unit | EW_Prop | EW_Private =>
                  raise Not_Implemented;

               when EW_Scalar =>

                  --  Only certain conversions are OK

                  if From_Kind = EW_Int and then To_Kind = EW_Real then
                     return To_Ident (WNE_Real_Of_Int);

                  --  Conversions from real to int in Ada round to the nearest
                  --  integer, and away from zero in case of tie, exactly like
                  --  'Rounding attribute.

                  elsif From_Kind = EW_Real and then To_Kind = EW_Int then
                     return To_Ident (WNE_Real_Round);

                  elsif From_Kind = EW_Bool and then To_Kind = EW_Int then
                     return Prefix (Ada_Node => Standard_Boolean,
                                    S        => "Boolean",
                                    W        => WNE_To_Int);

                  elsif From_Kind = EW_Int and then To_Kind = EW_Bool then
                     return Prefix (Ada_Node => Standard_Boolean,
                                    S        => "Boolean",
                                    W        => WNE_Of_Int);

                  elsif From_Kind = EW_Real and To_Kind in EW_Float then
                     return To_Ident (WNE_Real_To_IEEE);

                  elsif From_Kind in EW_Float and To_Kind = EW_Real then
                     return To_Ident (WNE_IEEE_To_Real);

                  elsif From_Kind = EW_Int and To_Kind in EW_Float then
                     return To_Ident (WNE_Int_To_IEEE);

                  elsif From_Kind in EW_Float and To_Kind = EW_Real then
                     return To_Ident (WNE_IEEE_To_Int);

                  elsif From_Kind in EW_Float and To_Kind in EW_Float then
                     case To_Kind is
                        when EW_Float32 =>
                           return Prefix
                             (S => To_String (From_Kind) & "_Conversion",
                              W => WNE_Change_Precision_32);
                        when EW_Float64 =>
                           return Prefix
                             (S => To_String (From_Kind) & "_Conversion",
                              W => WNE_Change_Precision_64);
                        when others =>
                           raise Program_Error;
                     end case;

                  --  Either the two objects are of the same type
                  --  (in which case the conversion is useless) or
                  --  they are of incompatible types
                  --  In both cases, it is an error.

                  else
                     raise Program_Error;
                  end if;

               when EW_Abstract =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+To);
                  begin
                     return
                       Prefix (Ada_Node => A,
                               S        => Full_Name (A),
                               W        => Convert_From (From_Kind));
                  end;
            end case;

         when EW_Abstract =>
            case To_Kind is
               when EW_Unit | EW_Prop | EW_Private =>
                  raise Not_Implemented;

               when EW_Scalar =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+From);
                  begin
                     return
                       Prefix (Ada_Node => A,
                               S => Full_Name (A),
                               W => Convert_To (To_Kind));
                  end;

               --  Case of a conversion between two record types

               when EW_Abstract =>
                  declare
                     From_Node : constant Node_Id := Get_Ada_Node (+From);
                     To_Node   : constant Node_Id := Get_Ada_Node (+To);
                  begin
                     if Root_Record_Type (From_Node) = From_Node then
                        return
                          Prefix (Ada_Node => To_Node,
                                  S        => Full_Name (To_Node),
                                  W        => WNE_Of_Base);
                     else
                        return
                          Prefix (Ada_Node => From_Node,
                                  S        => Full_Name (From_Node),
                                  W        => WNE_To_Base);
                     end if;
                  end;
            end case;
      end case;
   end Conversion_Name;

   ------------------
   -- Convert_From --
   ------------------

   function Convert_From (Kind : EW_Basic_Type) return Why_Name_Enum
   is
   begin
      case Kind is
         when EW_Int   => return WNE_Of_Int;
         when EW_Real  => return WNE_Of_Real;
         when EW_Float => return WNE_Of_Float;
         when others =>
            raise Program_Error;
      end case;
   end Convert_From;

   ----------------
   -- Convert_To --
   ----------------

   function Convert_To (Kind : EW_Basic_Type) return Why_Name_Enum
   is
   begin
      case Kind is
         when EW_Int   => return WNE_To_Int;
         when EW_Real  => return WNE_To_Real;
         when EW_Float => return WNE_To_Float;
         when others =>
            raise Program_Error;
      end case;
   end Convert_To;

   -----------------------
   -- EW_Base_Type_Name --
   -----------------------

   function EW_Base_Type_Name (Kind : EW_Basic_Type) return String is
   begin
      case Kind is
         when EW_Unit    => return "unit";
         when EW_Prop    => return "prop";
         when EW_Float32 => return "single";
         when EW_Float64 => return "double";
         when EW_Real    => return "real";
         when EW_Int     => return "int";
         when EW_Bool    => return "bool";
      end case;
   end EW_Base_Type_Name;

   ----------------------
   -- Float_Round_Name --
   ----------------------

   function Float_Round_Name (Ty : Entity_Id) return W_Identifier_Id is
   begin
      return Prefix (Ada_Node => Ty,
                     S        => Full_Name (Ty),
                     W        => WNE_Float_Round);
   end Float_Round_Name;

   -------------
   -- New_Abs --
   -------------

   function New_Abs (Kind : EW_Numeric) return W_Identifier_Id is
   begin
      case Kind is
         when EW_Float =>
            return Prefix (To_String (Kind), WNE_Float_Abs);
         when EW_Real =>
            return To_Ident (WNE_Real_Abs);
         when EW_Int =>
            return To_Ident (WNE_Integer_Abs);
      end case;
   end New_Abs;

   ------------------
   -- New_Bool_Cmp --
   ------------------

   function New_Bool_Cmp
     (Rel       : EW_Relation;
      Arg_Types : W_Base_Type_Id) return W_Identifier_Id
   is
      Kind : constant EW_Type := Get_Base_Type (Arg_Types);
      A    : constant Node_Id :=
        (if Kind = EW_Abstract then Get_Ada_Node (+Arg_Types)
         else Empty);
      R : constant Why_Name_Enum :=
        (case Rel is
         when EW_Eq   => WNE_Bool_Eq,
         when EW_Ne   => WNE_Bool_Ne,
         when EW_Le   => WNE_Bool_Le,
         when EW_Lt   => WNE_Bool_Lt,
         when EW_Gt   => WNE_Bool_Gt,
         when EW_Ge   => WNE_Bool_Ge,
         when EW_None => WNE_Bool_Eq
        );
      S : constant String :=
        (case Kind is
           when EW_Int   => "Integer",
           when EW_Float => "IEEE_Floating",
           when EW_Real  => "Floating",
           when EW_Bool  => "Boolean",
           when EW_Unit .. EW_Prop | EW_Private => "Main",
           when EW_Abstract => Full_Name (Get_Ada_Node (+Arg_Types)));
   begin
      return Prefix (Ada_Node => A,
                     S        => S,
                     W        => R);
   end New_Bool_Cmp;

   ------------------
   -- New_Division --
   ------------------

   function New_Division (Kind : EW_Numeric) return W_Identifier_Id is
   begin
      case Kind is
         when EW_Float =>
            return To_Ident (WNE_Float_Div);
         when EW_Real =>
            return To_Ident (WNE_Real_Div);
         when EW_Int =>
            return To_Ident (WNE_Integer_Div);
      end case;
   end New_Division;

   -------------
   -- New_Exp --
   -------------

   function New_Exp (Kind : EW_Numeric) return W_Identifier_Id is
   begin
      case Kind is
         when EW_Float =>
            return To_Ident (WNE_Float_Exp);
         when EW_Real =>
            return To_Ident (WNE_Real_Exp);
         when EW_Int =>
            return To_Ident (WNE_Integer_Exp);
      end case;
   end New_Exp;

   --------------------
   -- New_Identifier --
   --------------------

   function New_Identifier (Ada_Node : Node_Id := Empty; Name : String)
                            return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node, EW_Term, Name);
   end New_Identifier;

   function New_Identifier (Ada_Node : Node_Id := Empty;
                            Name    : String;
                            Context : String)
                            return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node, EW_Term, Name, Context);
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String)
     return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Domain => Domain,
                             Symbol => NID (Name));
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String;
      Context  : String)
     return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Domain   => Domain,
                             Symbol   => NID (Name),
                             Context  => NID (Capitalize_First (Context)));
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String;
      Context  : Name_Id)
     return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Domain   => Domain,
                             Symbol   => NID (Name),
                             Context  => Context);
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Symbol   : Name_Id)
     return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Domain   => Domain,
                             Symbol   => Symbol,
                             Context  => No_Name);
   end New_Identifier;

   ---------
   -- NID --
   ---------

   function NID (Name : String) return Name_Id is
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Name);
      return Name_Find;
   end NID;

   -------------------------
   -- New_Temp_Identifier --
   -------------------------

   New_Temp_Identifier_Counter : Natural := 0;

   function New_Temp_Identifier return String is
      Counter_Img : constant String :=
                      Natural'Image (New_Temp_Identifier_Counter);
   begin
      New_Temp_Identifier_Counter := New_Temp_Identifier_Counter + 1;
      return
        "temp___" & To_String (New_Temp_Identifier_Suffix) & "_"
        & Counter_Img (Counter_Img'First + 1 .. Counter_Img'Last);
   end New_Temp_Identifier;

   function New_Temp_Identifier return W_Identifier_Id is
   begin
      return New_Identifier (Name => New_Temp_Identifier);
   end New_Temp_Identifier;

   --------------------------
   -- New_Temp_Identifiers --
   --------------------------

   function New_Temp_Identifiers (Num : Positive) return W_Identifier_Array is
      Result : constant W_Identifier_Array (1 .. Num) :=
                 (others => +New_Temp_Identifier);
   begin
      return Result;
   end New_Temp_Identifiers;

   --------------
   -- To_Exprs --
   --------------

   function To_Exprs (Ids : W_Identifier_Array) return W_Expr_Array is
      Result : W_Expr_Array (Ids'Range);
   begin
      for J in Result'Range loop
         Result (J) := +Ids (J);
      end loop;

      return Result;
   end To_Exprs;

   ---------------
   -- To_String --
   ---------------

   function To_String (W : Why_Name_Enum) return String
   is
   begin
      case W is
         when WNE_Range_Pred   => return "in_range";
         when WNE_To_Int       => return "to_int";
         when WNE_Of_Int       => return "of_int";
         when WNE_To_Real      => return "to_real";
         when WNE_Of_Real      => return "of_real";
         when WNE_To_Array     => return "to_array";
         when WNE_Of_Array     => return "of_array";
         when WNE_To_Base      => return "to_base";
         when WNE_Of_Base      => return "of_base";
         when WNE_Type         => return "t";
         when WNE_Ignore       => return "___ignore";
         when WNE_Result       => return "result";
         when WNE_Result_Exc   => return "Return__exc";
         when WNE_Range_Check_Fun => return "range_check_";
         when WNE_Eq           => return "eq";
         when WNE_Range_Axiom  => return "range_axiom";
         when WNE_Unicity      => return "unicity_axiom";
         when WNE_Coerce       => return "coerce_axiom";
         when WNE_Bool_And     => return "andb";
         when WNE_Bool_Or      => return "orb";
         when WNE_Bool_Xor     => return "xorb";
         when WNE_Bool_Not     => return "notb";
         when WNE_Bitwise_And  => return "Integer.bitwise_and";
         when WNE_Bitwise_Or   => return "Integer.bitwise_or";
         when WNE_Bitwise_Xor  => return "Integer.bitwise_xor";
         when WNE_Integer_Div  => return "Integer.div";
         when WNE_Integer_Exp  => return "Integer.power";
         when WNE_Integer_Rem  => return "Integer.rem";
         when WNE_Integer_Mod  => return "Integer.mod";
         when WNE_Integer_Math_Mod => return "Integer.math_mod";
         when WNE_Integer_Max  => return "Integer.int_max";
         when WNE_Integer_Min  => return "Integer.int_min";
         when WNE_Real_Div     => return "Floating.div_real";
         when WNE_Integer_Abs  => return "Integer.abs";
         when WNE_Real_Abs     => return "Floating.AbsReal.abs";
         when WNE_Real_Ceil    => return "Floating.ceil";
         when WNE_Real_Exp     => return "Floating.power";
         when WNE_Real_Floor   => return "Floating.floor";
         when WNE_Real_Of_Int  => return "Floating.real_of_int";
         when WNE_Real_Round   => return "Floating.round";
         when WNE_Real_Truncate => return "Floating.truncate";
         when WNE_Real_Max  => return "Floating.real_max";
         when WNE_Real_Min  => return "Floating.real_min";
         when WNE_Float_Round   => return "round_real";
         when WNE_Float_Round_Tmp => return "round_real_tmp";
         when WNE_Float_Round_Single => return "Floating.round_single";
         when WNE_Float_Round_Double => return "Floating.round_double";
         when WNE_Array_1      => return "Array__1";
         when WNE_Array_2      => return "Array__2";
         when WNE_Array_3      => return "Array__3";
         when WNE_Array_4      => return "Array__4";
         when WNE_First_Static => return "first_static";
         when WNE_Last_Static  => return "last_static";
         when WNE_Array_Access => return "get";
         when WNE_Array_Elts   => return "elts";
         when WNE_Array_First_Field => return "first";
         when WNE_Array_Last_Field => return "last";
         when WNE_Array_Offset => return "offset";
         when WNE_Array_Update => return "set";
         when WNE_Bool_Eq      => return "bool_eq";
         when WNE_Bool_Ne      => return "bool_ne";
         when WNE_Bool_Lt      => return "bool_lt";
         when WNE_Bool_Le      => return "bool_le";
         when WNE_Bool_Gt      => return "bool_gt";
         when WNE_Bool_Ge      => return "bool_ge";
         when WNE_Def          => return "def";
         when WNE_Pre_Check    => return "pre_check";
         when WNE_Def_Axiom    => return "def_axiom";
         when WNE_Dummy        => return "dummy";
         when WNE_Func         => return "func";
         when WNE_Sandbox      => return "sandbox";
         when WNE_Range_Field  => return "rt";
         when WNE_Range_Type   => return "range_type";
         when WNE_String       => return "__string";
         when WNE_Char_Type    => return "__character";
         when WNE_Private      => return "__private";
         when WNE_Keep_On_Simp => return "keep_on_simp";
         when WNE_Pretty_Ada   => return "GP_Pretty_Ada";
         when WNE_Expr_Fun_Axiom   => return "__expr_fun_axiom";
         when WNE_Expr_Fun_Closure => return "__expr_fun_closure";
         when WNE_Constant_Axiom => return "__constant_axiom";
         when WNE_Constant_Closure => return "__constant_closure";
         when WNE_Check_Not_First => return "check_not_first";
         when WNE_Check_Not_Last => return "check_not_last";
         when WNE_Attr_First => return "first";
         when WNE_Attr_Last => return "last";
         when WNE_Attr_Length => return "length";
         when WNE_Attr_Image   =>
            return "attr__" & Attribute_Id'Image (Attribute_Image);
         when WNE_Attr_Modulus =>
            return "attr__" & Attribute_Id'Image (Attribute_Modulus);
         when WNE_Attr_Value   =>
            return "attr__" & Attribute_Id'Image (Attribute_Value);
         when WNE_Attr_Value_Pre_Check =>
            return "attr__" & Attribute_Id'Image (Attribute_Value)
              & "__pre_check";

         when WNE_Change_Precision_32 =>
            return "to_single_rne";
         when WNE_Change_Precision_64 =>
            return "to_double_rne";

         when WNE_Real_To_IEEE  => return "of_real";
         when WNE_IEEE_To_Real  => return "ieee_to_real";
         when WNE_Int_To_IEEE   => return "int_to_ieee";
         when WNE_IEEE_To_Int   => return "ieee_to_int";
         when WNE_Of_Float      => return "of_float";
         when WNE_To_Float      => return "to_float";
         when WNE_Float_Abs     => return "fp_abs";
         when WNE_Float_Div     => return "div_float";
         when WNE_Float_Exp     => return "TBD_exp_TBD";
         when WNE_Float_Min     => return "fp_min";
         when WNE_Float_Max     => return "fp_max";
         when WNE_Float_Floor   => return "floor";
         when WNE_Float_Ceiling => return "ceiling";

      end case;
   end To_String;

   function To_String (T : EW_Float) return String
   is
   begin
      case T is
         when EW_Float32 => return "Single_RNE";
         when EW_Float64 => return "Double_RNE";
      end case;
   end To_String;

   --------------
   -- To_Ident --
   --------------

   function To_Ident (W        : Why_Name_Enum;
                      Ada_Node : Node_Id := Empty) return W_Identifier_Id
   is
   begin
      if No (Ada_Node) then
         if Pre_Computed_Idents (W) /= Why_Empty then
            return Pre_Computed_Idents (W);
         else
            declare
               Id : constant W_Identifier_Id :=
                 New_Identifier (Name => To_String (W));
            begin
               Pre_Computed_Idents (W) := Id;
               return Id;
            end;
         end if;
      else
         return New_Identifier (Ada_Node => Ada_Node, Name => To_String (W));
      end if;
   end To_Ident;

   -----------------
   -- To_Fp_Ident --
   -----------------

   function To_Fp_Ident (T    : EW_Float;
                         Kind : Node_Kind)
                         return W_Identifier_Id
   is
      S : constant String :=
        (case Kind is
           when N_Op_Minus    => "fp_neg",
           when N_Op_Add      => "fp_add",
           when N_Op_Multiply => "fp_mul",
           when N_Op_Subtract => "fp_sub",
           when N_Op_Gt       => "fp_gt",
           when N_Op_Lt       => "fp_lt",
           when N_Op_Eq       => "fp_eq",
           when N_Op_Ge       => "fp_geq",
           when N_Op_Le       => "fp_leq",
           when N_Op_Ne       => "fp_neq",
           when others => "");
   begin
      if S = "" then
         raise Not_Implemented;
      else
         return Prefix (To_String (T), S);
      end if;
   end To_Fp_Ident;

   function To_Fp_Ident (T    : EW_Float;
                         Kind : EW_Relation)
                         return W_Identifier_Id
   is
      S : constant String :=
        (case Kind is
           when EW_None => "",
           when EW_Gt => "fp_gt",
           when EW_Lt => "fp_lt",
           when EW_Eq => "fp_eq",
           when EW_Ge => "fp_geq",
           when EW_Le => "fp_leq",
           when EW_Ne => "fp_neq");
   begin
      if S = "" then
         raise Not_Implemented;
      else
         return Prefix (To_String (T), S);
      end if;
   end To_Fp_Ident;

   ------------
   -- Prefix --
   ------------

   function Prefix (S        : String;
                    W        : Why_Name_Enum;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Context => S,
         Name    => To_String (W),
         Ada_Node => Ada_Node);
   end Prefix;

   function Prefix (P        : String;
                    N        : String;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Context => P,
         Name     => N,
         Ada_Node => Ada_Node);
   end Prefix;

   function Prefix (S        : Why_Name_Enum;
                    W        : Why_Name_Enum;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Context => To_String (S),
         Name    => To_String (W),
         Ada_Node => Ada_Node);
   end Prefix;

   ----------------------
   -- Range_Check_Name --
   ----------------------

   function Range_Check_Name
     (Ty : Entity_Id;
      R  : Range_Check_Kind) return W_Identifier_Id
   is
      Name : constant Why_Name_Enum :=
        (case R is
            when RCK_Not_First => WNE_Check_Not_First,
            when RCK_Not_Last  => WNE_Check_Not_Last,
            when others        => WNE_Range_Check_Fun);
   begin
      if Ty = Standard_Boolean then
         return Prefix (Ada_Node => Standard_Boolean,
                        S        => "Boolean",
                        W        => Name);
      else
         return Prefix (Ada_Node => Ty,
                        S        => Full_Name (Ty),
                        W        => Name);
      end if;
   end Range_Check_Name;

   ---------------------
   -- Range_Pred_Name --
   ---------------------

   function Range_Pred_Name (Ty : Entity_Id) return W_Identifier_Id
   is
   begin
      if Ty = Standard_Boolean then
         return Prefix (Ada_Node => Standard_Boolean,
                        S        => "Boolean",
                        W        => WNE_Range_Pred);
      else
         return Prefix (Ada_Node => Ty,
                        S        => Full_Name (Ty),
                        W        => WNE_Range_Pred);
      end if;
   end Range_Pred_Name;

   ----------------------
   -- To_Program_Space --
   ----------------------

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id is
      Suffix : constant String := "_";
      N_Id   : constant Name_Id := Get_Symbol (Name);
      Img    : constant String := Get_Name_String (N_Id);
      Context : constant Name_Id := Get_Context (Name);
   begin
      return New_Identifier
        (Get_Ada_Node (+Name), EW_Prog, Img & Suffix, Context);
   end To_Program_Space;

   ----------------------
   -- Uint_To_Positive --
   ----------------------

   function Uint_To_Positive (U : Uint) return Positive
   is
   begin
      if U = Uint_1 then
         return 1;
      elsif U = Uint_2 then
         return 2;
      elsif U = Uint_3 then
         return 3;
      elsif U = Uint_4 then
         return 4;
      else
         raise Program_Error;
      end if;
   end Uint_To_Positive;

   --------------------------
   -- Why_Scalar_Type_Name --
   --------------------------

   function Why_Scalar_Type_Name (Kind : EW_Scalar) return String is
   begin
      case Kind is
         when EW_Bool    => return "bool";
         when EW_Int     => return "int";
         when EW_Float32 => return "single";
         when EW_Float64 => return "double";
         when EW_Real    => return "real";
      end case;
   end Why_Scalar_Type_Name;

end Why.Gen.Names;
