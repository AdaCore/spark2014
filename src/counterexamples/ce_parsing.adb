------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            C E _ P A R S I N G                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2022-2022, AdaCore                     --
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

with Ada.Strings.Unbounded;    use Ada.Strings.Unbounded;
with Ada.Unchecked_Conversion;
with CE_Utils;                 use CE_Utils;
with Interfaces;               use Interfaces;
with SPARK_Atree;              use SPARK_Atree;
with SPARK_Util;               use SPARK_Util;
with SPARK_Util.Types;         use SPARK_Util.Types;
with Stand;                    use Stand;
with Uintp;                    use Uintp;
with Urealp;                   use Urealp;

package body CE_Parsing is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Boolean_Value (B : Boolean) return Scalar_Value is
     (K           => Enum_K,
      Enum_Entity => Boolean_Literals (B));

   function Parse_Float
     (Cnt_Value : Cntexmp_Value;
      Ty        : Entity_Id) return Scalar_Value;

   function Size (S : String) return Integer is
     (if S (S'First + 1) = 'x'
      then 4 * (S'Length - 2)
      else (S'Length - 2));
   --  Size returns the associate binary size of a #b or #x number (to help
   --  when building an unsigned integer).

   --  This package is generic so that part of the work done can be shared
   --  between 32bit, 64 bits, and extended precision float numbers.

   generic
      type T_Unsigned is mod <>;
      type T_Float is digits <>;
   package Parse_Conversion is

      Bound : constant Integer := T_Unsigned'Size;

      function StringBits_To_Floatrepr
        (Sign, Significand, Exp : String) return T_Unsigned;
      --  Transform three stringbits into a single unsigned modular number
      --  (representing a float).

      function Unsigned_To_Float (U : T_Unsigned) return T_Float;
      --  Convert an unsigned number to a floating point number

      function StringBits_To_Float
        (Sign, Significand, Exp : String) return T_Float
      is
        (Unsigned_To_Float
           (StringBits_To_Floatrepr (Sign, Significand, Exp)));

   end Parse_Conversion;

   ----------------------
   -- Parse_Conversion --
   ----------------------

   package body Parse_Conversion is

      pragma Assert (T_Unsigned'Size = T_Float'Size);

      function StringBits_To_Unsigned (S : String) return T_Unsigned;
      --  This transforms a number written in bin #b0101 or hex #x5 to an
      --  unsigned integer. (Inside a generic package so the size of unsigned
      --  integer can vary: checks for the size are done outside this
      --  function).

      ----------------------------
      -- StringBits_To_Unsigned --
      ----------------------------

      function StringBits_To_Unsigned (S : String) return T_Unsigned
      is
      begin
         pragma Assert (S (S'First) = '#');
         return T_Unsigned'Value
           (if S (S'First + 1) = 'x' then
              "16#" & S (S'First + 2 .. S'Last) & "#"
            elsif S (S'First + 1) = 'b' then
               "2#" & S (S'First + 2 .. S'Last) & "#"
            else
              raise Program_Error);
      end StringBits_To_Unsigned;

      -----------------------------
      -- StringBits_To_Floatrepr --
      -----------------------------

      function StringBits_To_Floatrepr
        (Sign, Significand, Exp : String) return T_Unsigned
      is
         I_Sign           : constant T_Unsigned :=
           StringBits_To_Unsigned (Sign);
         I_Significand    : constant T_Unsigned :=
           StringBits_To_Unsigned (Significand);
         Size_Significand : constant Integer := Size (Significand);
         I_Exp            : constant T_Unsigned :=
           StringBits_To_Unsigned (Exp);
      begin
         return I_Sign * 2 ** (Bound - 1) +
           I_Exp * 2 ** Size_Significand +
           I_Significand;
      end StringBits_To_Floatrepr;

      -----------------------
      -- Unsigned_To_Float --
      -----------------------

      function Unsigned_To_Float (U : T_Unsigned) return T_Float is
         function Convert is new Ada.Unchecked_Conversion
           (Source => T_Unsigned,
            Target => T_Float);

      begin
         if Convert (U)'Valid then

            --  Unchecked conversion
            return Convert (U);
         else
            raise Parse_Error;
         end if;
      end Unsigned_To_Float;

   end Parse_Conversion;

   -----------------
   -- Parse_Float --
   -----------------

   function Parse_Float
     (Cnt_Value : Cntexmp_Value;
      Ty        : Entity_Id) return Scalar_Value
   is
      F : VC_Kinds.Float_Value renames Cnt_Value.F.all;
   begin
      case F.F_Type is
         when Float_Plus_Infinity | Float_Minus_Infinity | Float_NaN =>

            --  Decision: we don't handle infinities or Nan
            raise Parse_Error;

         when Float_Plus_Zero | Float_Minus_Zero =>
            if Is_Single_Precision_Floating_Point_Type (Ty) then
               return (Float_K, (Float_32_K, 0.0));
            elsif Is_Double_Precision_Floating_Point_Type (Ty) then
               return (Float_K, (Float_64_K, 0.0));
            elsif Is_Extended_Precision_Floating_Point_Type (Ty) then
               return (Float_K, (Extended_K, 0.0));
            else
               raise Program_Error;
            end if;

         when Float_Val =>
            declare
               Sign        : constant String := To_String (F.F_Sign);
               Significand : constant String := To_String (F.F_Significand);
               Exp         : constant String := To_String (F.F_Exponent);
            begin
               pragma Assert (Size (Sign) = 1);
               if Is_Single_Precision_Floating_Point_Type (Ty) then
                  pragma Assert (Size (Exp) = 8);
                  pragma Assert (Size (Significand) = 23);
                  declare
                     package P is new Parse_Conversion (Unsigned_32, Float);
                     F : constant Float :=
                       P.StringBits_To_Float (Sign, Significand, Exp);
                  begin
                     return (Float_K, (Float_32_K, F));
                  end;
               elsif Is_Double_Precision_Floating_Point_Type (Ty) then
                  pragma Assert (Size (Exp) = 11);
                  pragma Assert (Size (Significand) = 52);
                  declare
                     package P is new Parse_Conversion
                       (Interfaces.Unsigned_64, Long_Float);
                     F : constant Long_Float :=
                       P.StringBits_To_Float (Sign, Significand, Exp);
                  begin
                     return (Float_K, (Float_64_K, F));
                  end;
               elsif Is_Extended_Precision_Floating_Point_Type (Ty) then
                  pragma Assert (Size (Exp) = 15);
                  pragma Assert (Size (Significand) = 63);
                  declare
                     package P is new Parse_Conversion
                       (Interfaces.Unsigned_128, Long_Long_Float);
                     F : constant Long_Long_Float :=
                       P.StringBits_To_Float (Sign, Significand, Exp);
                  begin
                     return (Float_K, (Extended_K, F));
                  end;
               else
                  raise Program_Error;
               end if;
            end;
      end case;
   end Parse_Float;

   ------------------------
   -- Parse_Scalar_Value --
   ------------------------

   function Parse_Scalar_Value
     (Cnt_Value : Cntexmp_Value_Ptr;
      AST_Type  : Entity_Id) return Scalar_Value
   is
      Why3_Type : constant Cntexmp_Type := Cnt_Value.all.T;
   begin
      case Why3_Type is
         when Cnt_Integer =>

            --  Necessary for some types that makes boolean be translated to
            --  integers like: "subype only_true := True .. True".

            if Is_Boolean_Type (AST_Type) then
               return Boolean_Value (Cnt_Value.I /= "0");

            elsif Is_Enumeration_Type (AST_Type) then
               declare
                  Value : constant Uint := UI_From_String
                    (To_String (Cnt_Value.I));

                  --  Call Get_Enum_Lit_From_Pos to get a corresponding
                  --  enumeration entity.

                  Lit : Node_Id;

               begin
                  --  Initialization of Enum can raise Constraint_Error if
                  --  there is no literal value for the position.

                  Lit := Get_Enum_Lit_From_Pos (AST_Type, Value);
                  return
                    (K           => Enum_K,
                     Enum_Entity =>
                       (if Nkind (Lit) = N_Character_Literal then Lit
                        else Entity (Lit)));

               --  An exception is raised by Get_Enum_Lit_From_Pos if the
               --  position Value is outside the bounds of the enumeration.
               --  In such a case, return the raw integer returned by the
               --  prover.

               exception
                  when Constraint_Error =>
                     raise Parse_Error;
               end;

            --  Cvc4 returns Floating_point value with integer type. We
            --  don't want to consider those.

            elsif Is_Floating_Point_Type (AST_Type) then
               raise Parse_Error;

            elsif Is_Fixed_Point_Type (AST_Type) then
               declare
                  Small : constant Ureal := Small_Value (AST_Type);
                  Num   : constant Big_Integer :=
                    From_String (UI_Image (Norm_Num (Small), Decimal));
                  Den   : constant Big_Integer :=
                    From_String (UI_Image (Norm_Den (Small), Decimal));
                  Val    : Big_Integer;

               begin
                  Val := From_String (To_String (Cnt_Value.I));
                  return (Fixed_K, Val, Num / Den);

               exception
                  when Constraint_Error =>
                     raise Parse_Error;
               end;

            --  Only integer types are expected in that last case

            else
               pragma Assert (Has_Integer_Type (AST_Type));

               declare
                  Val : Big_Integer;

               begin
                  Val := From_String (To_String (Cnt_Value.I));
                  return (Integer_K, Val);

               exception
                  when Constraint_Error =>
                     raise Parse_Error;
               end;
            end if;

         when Cnt_Boolean =>
               return Boolean_Value (Cnt_Value.Bo);

         when Cnt_Bitvector =>

            --  Boolean are translated into bitvector of size 1 for CVC4
            --  because it fails to produce a model when booleans are used
            --  inside translated arrays_of_records.

            if Is_Boolean_Type (AST_Type) then
               return Boolean_Value (Cnt_Value.B = "0");
            end if;

            declare
               Val : Big_Integer;

            begin
               Val := From_String (To_String (Cnt_Value.B));
               return (Integer_K, Val);

            exception
               when Constraint_Error =>
                  raise Parse_Error;
            end;

         when Cnt_Decimal =>
            pragma Assert (Is_Floating_Point_Type (AST_Type));

            begin
               if Is_Single_Precision_Floating_Point_Type (AST_Type) then
                  return
                    (Float_K,
                     (Float_32_K, Float'Value (To_String (Cnt_Value.B))));
               elsif Is_Double_Precision_Floating_Point_Type (AST_Type) then
                  return
                    (Float_K,
                     (Float_64_K, Long_Float'Value (To_String (Cnt_Value.B))));
               elsif Is_Extended_Precision_Floating_Point_Type (AST_Type) then
                  return
                    (Float_K,
                     (Extended_K,
                      Long_Long_Float'Value (To_String (Cnt_Value.B))));
               else
                  raise Program_Error;
               end if;
            exception
               when Constraint_Error =>
                  raise Parse_Error;
            end;

         when Cnt_Float =>
            pragma Assert (Is_Floating_Point_Type (AST_Type));

            return Parse_Float (Cnt_Value.all, AST_Type);

         when Cnt_Unparsed
            | Cnt_Invalid
            | Cnt_Projection
            | Cnt_Record
            | Cnt_Array
          =>
            raise Parse_Error;
      end case;
   end Parse_Scalar_Value;

end CE_Parsing;
