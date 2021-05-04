------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   C E _ P R E T T Y _ P R I N T I N G                    --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2021, AdaCore                     --
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

with Ada.Strings.Fixed;        use Ada.Strings.Fixed;
with Ada.Text_IO;
with Ada.Unchecked_Conversion;
with Casing;                   use Casing;
with Gnat2Why.CE_Utils;        use Gnat2Why.CE_Utils;
with Gnat2Why_Args;
with Interfaces;               use Interfaces;
with Namet;                    use Namet;
with SPARK_Atree;              use SPARK_Atree;
with SPARK_Util;               use SPARK_Util;
with SPARK_Util.Types;         use SPARK_Util.Types;
with String_Utils;             use String_Utils;
with Uintp;                    use Uintp;

package body Ce_Pretty_Printing is

   ------------------
   -- Make_Trivial --
   ------------------

   function Make_Trivial
     (Nul : Boolean;
      Str : Unbounded_String;
      Cnt : Natural := 1;
      Els : S_String_List.List := S_String_List.Empty)
      return CNT_Unbounded_String
   is
      Nul_Internal : constant Boolean :=
        Nul and not Gnat2Why_Args.Debug_Trivial;
      Elems : S_String_List.List;

   begin
      --  Leave Elems empty for a nul value
      if Nul_Internal then
         null;

      --  Otherwise if Els is empty, use the singleton " = Str " for the value

      elsif Els.Is_Empty then
         Elems.Append (" = " & Str);

      --  Otherwise use Els

      else
         Elems := Els;
      end if;

      return (Nul   => Nul_Internal,
              Str   => Str,
              Count => Cnt,
              Elems => Elems);
   end Make_Trivial;

   ----------
   -- Size --
   ----------

   function Size (S : String) return Integer is
     (if S (S'First + 1) = 'x' then
           4 * (S'Length - 2)
      else
        (S'Length - 2));
   --  Size returns the associate binary size of a #b or #x number (to help
   --  when building an unsigned integer).

   --  This package is generic so that part of the work done can be shared
   --  between 32bit and 64 bits float numbers.

   ----------------------
   -- Print_Conversion --
   ----------------------

   generic
      type T_Unsigned is mod <>;
      type T_Float is digits <>;
   package Print_Conversion is

      Bound : constant Integer := T_Unsigned'Size;

      function StringBits_To_Floatrepr (Sign, Significand, Exp : String)
                                        return T_Unsigned;
      --  Transform three stringbits into a single unsigned modular number
      --  (representing a float).

      function Unsigned_To_Float_String (U : T_Unsigned)
                                         return String;
      --  Convert an unsigned number to string representation of a float.

      function StringBits_To_Float_Approx (Sign, Significand, Exp : String)
                                           return String
      is
        (Unsigned_To_Float_String (
           StringBits_To_Floatrepr (Sign, Significand, Exp)));

   end Print_Conversion;

   --------------------
   -- Print_Discrete --
   --------------------

   function Print_Discrete (Nb : String; Ty : Entity_Id) return String is

      function Beautiful_Source_Name (Ty : Entity_Id) return String
        with Pre => Is_Discrete_Type (Ty);
      --  Does the same as Source_Name except for types defined in Standard
      --  which we print with Upper case letter after each '_'.

      ---------------------------
      -- Beautiful_Source_Name --
      ---------------------------

      function Beautiful_Source_Name (Ty : Entity_Id) return String is
      begin
         if Is_Standard_Type (Ty) then
            --  Put lower-case name in Global_Name_Buffer
            Get_Unqualified_Name_String (Chars (Ty));

            --  Convert the content of Global_Name_Buffer to "Mixed_Case"
            Set_Casing (Mixed_Case);

            --  Return the converted name
            return Name_Buffer (1 .. Name_Len);
         else
            return Source_Name (Ty);
         end if;
      end Beautiful_Source_Name;

      --  Local variables

      Nb_Value : Uint;
      Nb_Type  : Entity_Id := Ty;

   --  Start of processing for Print_Discrete

   begin
      --  Handle exception from UI_From_String
      begin
         Nb_Value := UI_From_String (Nb);
      exception
         when others => return Nb;
      end;

      --  Do not print the counterexample if a value falls outside of the
      --  bounds of its type.

      if Compile_Time_Known_Value (Type_Low_Bound (Nb_Type))
        and then Nb_Value < Expr_Value (Type_Low_Bound (Nb_Type))
      then
         return "";

      elsif Compile_Time_Known_Value (Type_High_Bound (Nb_Type))
        and then Nb_Value > Expr_Value (Type_High_Bound (Nb_Type))
      then
         return "";
      end if;

      --  If one of the bounds is not known, use the base type for evaluating
      --  the type range to decide if we alter printing.
      if not Compile_Time_Known_Value (Type_Low_Bound (Nb_Type)) or else
         not Compile_Time_Known_Value (Type_High_Bound (Nb_Type))
      then
         Nb_Type := Base_Type (Nb_Type);
      end if;

      --  Beginning of safe computations

      declare
         --  Type informations
         Low_Bound  : constant Uint   :=
           Expr_Value (Type_Low_Bound (Nb_Type));
         High_Bound : constant Uint   :=
           Expr_Value (Type_High_Bound (Nb_Type));
         Type_Range : constant Uint   := High_Bound - Low_Bound;
         Type_Name  : constant String := Beautiful_Source_Name (Nb_Type);

         --  Difference calculations
         Diff_To_High : constant Uint := abs (Nb_Value - High_Bound);
         Diff_To_Low  : constant Uint := abs (Nb_Value - Low_Bound);
         Side         : Character;

      begin
         --  If the range of type is too small, we do nothing. If the type
         --  we are given is internal then we don't want to print it as it
         --  would confuse the user.
         --  Example: type Data_T is array (1 .. 1000) of Integer;
         --  There is an internal type Tdata_tD1 for range (1..1000) for
         --  indices: we don't want to print Tdata_tD1'First.
         if Type_Range <= UI_From_Int (Bound_Type) or else
           (not Comes_From_Source (Nb_Type) and then
                not Is_Standard_Type (Nb_Type))
         then
            return Nb;
         end if;

         --  Nb is closer to the highest bound
         if Diff_To_High <= Diff_To_Low then

            if Diff_To_High = 0 then
               return Type_Name & "'Last";

            elsif Diff_To_High < Bound_Value then
               Side := (if Nb_Value < High_Bound then '-' else '+');
               return Type_Name & "'Last" & Side & UI_Image (Diff_To_High);

            else
               return Nb;
            end if;

         --  We don't want to print Natural'First + 5 as counterexample. So,
         --  there is a special case when Low_Bound of the type is in 0 .. 1.

         elsif Low_Bound = 0 or else Low_Bound = 1 then
            return Nb;

         else
            if Diff_To_Low = 0 then
               return Type_Name & "'First";

            elsif Diff_To_Low < Bound_Value then
               Side := (if Nb_Value < Low_Bound then '-' else '+');
               return Type_Name & "'First" & Side & UI_Image (Diff_To_Low);

            else
               return Nb;
            end if;
         end if;
      end;
   end Print_Discrete;

   --  Start of package body for Print_Conversion

   package body Print_Conversion is

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

      function StringBits_To_Floatrepr (Sign, Significand, Exp : String)
                                       return T_Unsigned
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

      ------------------------------
      -- Unsigned_To_Float_String --
      ------------------------------

      function Unsigned_To_Float_String (U : T_Unsigned) return String is
         function Convert is new Ada.Unchecked_Conversion
           (Source => T_Unsigned,
            Target => T_Float);
         package F_IO is new Ada.Text_IO.Float_IO (T_Float);
         Result        : T_Float;
         Result_String : String (1 .. Bound);
      begin
         if Convert (U)'Valid then

            --  Unchecked conversion
            Result := Convert (U);

            --  To get nicer results we print small, exactly represented
            --  integers as 123.0 and not in the scientific notation. The
            --  choice of what is "small" is arbitrary; it could be anything
            --  within +/- 2**24 and +/- 2**54 (bounds excluded) for single and
            --  double precision floating point numbers, respectively.

            if abs (Result) < 1000.0
              and then Result = T_Float'Truncation (Result)
            then
               F_IO.Put (To   => Result_String,
                         Item => Result,
                         Aft  => 0,
                         Exp  => 0);
            else
               F_IO.Put (To   => Result_String,
                         Item => Result,
                         --  In the case of long_float, we print 10 decimals
                         --  and we print 7 in case of short float.
                         Aft  => (if Bound = 64 then 10 else 7),
                         Exp  => 1);
            end if;

            return Trim (Source => Result_String,
                         Side   => Ada.Strings.Both);
         else
            return "";
         end if;
      end Unsigned_To_Float_String;

   end Print_Conversion;

   --------------------------
   -- StringBits_To_Approx --
   --------------------------

   function StringBits_To_Approx (Sign, Significand, Exp : String)
                                  return String
   is
   begin
      pragma Assert (Size (Sign) = 1);
      if Size (Significand) <= 23 then
         pragma Assert (Size (Exp) = 8);
         pragma Assert (Size (Significand) = 23);
         declare
            package P is new Print_Conversion (Unsigned_32, Float);
         begin
            return P.StringBits_To_Float_Approx (Sign, Significand, Exp);
         end;
      else
         pragma Assert (Size (Exp) = 11);
         pragma Assert (Size (Significand) = 52);
         declare
            package P is new Print_Conversion (Unsigned_64, Long_Float);
         begin
            return P.StringBits_To_Float_Approx (Sign, Significand, Exp);
         end;

      end if;
   end StringBits_To_Approx;

   -----------------
   -- Print_Fixed --
   -----------------

   function Print_Fixed (Small : Ureal; Nb : String) return String
   is
   begin
      declare
         Nb_Int : constant Uint := UI_From_String (Nb);
         Nb_Real : constant Ureal := UR_From_Uint (Nb_Int) * Small;
      begin
         if Nb_Real = UR_From_Uint (UR_Trunc (Nb_Real)) then
            return UI_Image (UR_To_Uint (Nb_Real), Decimal);
         else
            declare
               Num_Small : constant String :=
                 UI_Image (Norm_Num (Small), Decimal);
               Den_Small : constant String :=
                 UI_Image (Norm_Den (Small), Decimal);
            begin
               return Nb
                 & (if Num_Small /= "1" then "*" & Num_Small else "")
                 & (if Den_Small /= "1" then "/" & Den_Small else "");
            end;
         end if;
      end;
   exception when others =>
         return "";
   end Print_Fixed;

   -----------------
   -- Print_Float --
   -----------------

   function Print_Float (Cnt_Value : Cntexmp_Value) return Unbounded_String
   is
      F : Float_Value renames Cnt_Value.F.all;
   begin
      case F.F_Type is
         when Float_Plus_Infinity | Float_Minus_Infinity | Float_NaN =>

            --  Decision: we don't print infinities or Nan
            return Null_Unbounded_String;

         when Float_Plus_Zero | Float_Minus_Zero =>

            --  Decision: we print zero+ and zero- as 0 (0.0 for type)
            return To_Unbounded_String ("0.0");

         when Float_Val =>
            declare
               F_S   : constant String := To_String (F.F_Sign);
               F_Si  : constant String := To_String (F.F_Significand);
               F_Exp : constant String := To_String (F.F_Exponent);
            begin
               return
                 To_Unbounded_String
                   (Ce_Pretty_Printing.StringBits_To_Approx
                      (F_S, F_Si, F_Exp));
            end;
      end case;
   end Print_Float;

   -------------------------
   -- Print_Cntexmp_Value --
   -------------------------

   function Print_Cntexmp_Value (Cnt_Value : Cntexmp_Value_Ptr;
                                 AST_Type  : Entity_Id;
                                 Is_Index  : Boolean := False)
                                 return CNT_Unbounded_String
   is

      Why3_Type : constant Cntexmp_Type := Cnt_Value.all.T;
   begin
      case Why3_Type is
         when Cnt_Integer =>

            --  Necessary for some types that makes boolean be translated to
            --  integers like: "subype only_true := True .. True".

            if Is_Boolean_Type (AST_Type) then
               return Make_Trivial (Nul => Cnt_Value.I = "0",
                                    Str => To_Unbounded_String
                                      (Cnt_Value.I /= "0"));

            elsif Is_Enumeration_Type (AST_Type) then
               declare
                  Value : constant Uint := UI_From_String
                    (To_String (Cnt_Value.I));
                  Nul   : constant Boolean := Cnt_Value.I = "0";

                  --  Call Get_Enum_Lit_From_Pos to get a corresponding
                  --  enumeration entity.

                  Enum  : Entity_Id;

               begin
                  --  Initialization of Enum can raise Constraint_Error if
                  --  there is no literal value for the position.

                  Enum := Get_Enum_Lit_From_Pos (AST_Type, Value);

                  --  Special case for characters, which are defined in the
                  --  standard unit Standard.ASCII, and as such do not have
                  --  a source code representation.

                  if Is_Character_Type (AST_Type) then
                     --  Call Get_Unqualified_Decoded_Name_String to get a
                     --  correctly printed character in Name_Buffer.

                     Get_Unqualified_Decoded_Name_String (Chars (Enum));

                     --  The call to Get_Unqualified_Decoded_Name_String set
                     --  Name_Buffer to '<char>' where <char> is the character
                     --  we are interested in. Just retrieve it directly at
                     --  Name_Buffer(2).

                     return Make_Trivial (Nul => Nul,
                                          Str => "'" & To_Unbounded_String
                                            (Char_To_String_Representation
                                               (Name_Buffer (2))) & "'");

                     --  For all enumeration types that are not character,
                     --  call Get_Enum_Lit_From_Pos to get a corresponding
                     --  enumeratio n entity, then Source_Name to get a
                     --  correctly capitalized enumeration value.

                  else
                     return Make_Trivial
                       (Nul => Nul,
                        Str => To_Unbounded_String (Source_Name (Enum)));
                  end if;

                  --  An exception is raised by Get_Enum_Lit_From_Pos if the
                  --  position Value is outside the bounds of the enumeration.
                  --  In such a case, return the raw integer returned by the
                  --  prover.

               exception
                  when Constraint_Error =>
                     if Is_Index then
                        return Make_Trivial (Nul => True,
                                             Str => Null_Unbounded_String);
                     else
                        return Make_Trivial (Nul => Nul,
                                             Str => Cnt_Value.I);
                     end if;
               end;

               --  Cvc4 returns Floating_point value with integer type. We
               --  don't want to print those.

            elsif Is_Floating_Point_Type (AST_Type) then
               return Make_Trivial (Nul => True,
                                    Str => Null_Unbounded_String);

            elsif Is_Fixed_Point_Type (AST_Type) then
               return Make_Trivial
                 (Nul => Cnt_Value.I = "0",
                  Str => To_Unbounded_String
                    (Print_Fixed (Small_Value (AST_Type),
                     To_String (Cnt_Value.I))));

            --  Only integer types are expected in that last case

            else
               pragma Assert (Has_Integer_Type (AST_Type));

               declare
                  --  Decision: generic values for Bound_Type and Bound_Value
                  --  are random for now. They can be adjusted in the future.

                  function Pretty_Print is
                    new Print_Discrete (Bound_Type  => 10,
                                        Bound_Value => 5);
               begin
                  return Make_Trivial
                    (Nul => Cnt_Value.I = "0",
                     Str => To_Unbounded_String (
                       Pretty_Print
                         (To_String (Cnt_Value.I), AST_Type)));
               end;
            end if;

         when Cnt_Boolean =>
            return Make_Trivial
              (Nul => not Cnt_Value.Bo,
               Str => To_Unbounded_String (Cnt_Value.Bo));

         when Cnt_Bitvector =>

            --  Boolean are translated into bitvector of size 1 for CVC4
            --  because it fails to produce a model when booleans are used
            --  inside translated arrays_of_records.

            if Is_Boolean_Type (AST_Type) then
               return Make_Trivial
                 (Nul => Cnt_Value.B = "0",
                  Str => To_Unbounded_String (Cnt_Value.B /= "0"));
            end if;

            return Make_Trivial (Nul => Cnt_Value.B = "0",
                                 Str => Cnt_Value.B);

         when Cnt_Decimal =>
            return Make_Trivial (Nul => Cnt_Value.D = "0.0",
                                 Str => Cnt_Value.D);

         when Cnt_Float =>

            pragma Assert (Is_Floating_Point_Type (AST_Type));
            declare
               S : constant Unbounded_String := Print_Float (Cnt_Value.all);
            begin
               return Make_Trivial (Nul => S = "0.0", Str => S);
            end;

         when Cnt_Unparsed =>
            return Make_Trivial (Nul => Cnt_Value.U = "0",
                                 Str => Cnt_Value.U);

            --  This case only happens when the why3 counterexamples are
            --  incorrect. Ideally, this case should be removed but it
            --  still happens in practice.

         when Cnt_Invalid =>
            return Make_Trivial (Nul => True,
                                 Str => Cnt_Value.S);

         when Cnt_Projection =>
            pragma Assert (False);
            --  This case should never happen: we never built a Cnt_Projection
            --  ever.
            return Make_Trivial (Nul => True,
                                 Str => Cnt_Value.Er);

         when Cnt_Record | Cnt_Array =>
            pragma Assert (False);
            return Dont_Display;
      end case;
   end Print_Cntexmp_Value;

end Ce_Pretty_Printing;
