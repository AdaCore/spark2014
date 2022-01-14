------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   C E _ P R E T T Y _ P R I N T I N G                    --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2022, AdaCore                     --
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

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;
with Ada.Strings;              use Ada.Strings;
with Ada.Strings.Fixed;        use Ada.Strings.Fixed;
with Ada.Text_IO;
with Ada.Unchecked_Conversion;
with Casing;                   use Casing;
with CE_Parsing;               use CE_Parsing;
with Gnat2Why_Args;
with Namet;                    use Namet;
with SPARK_Atree;              use SPARK_Atree;
with SPARK_Atree.Entities;     use SPARK_Atree.Entities;
with SPARK_Util;               use SPARK_Util;
with SPARK_Util.Types;         use SPARK_Util.Types;
with Stand;                    use Stand;
with Uintp;                    use Uintp;

package body CE_Pretty_Printing is

   -----------------------
   -- Local_Subprograms --
   -----------------------

   generic
      Bound_Type  : Big_Natural;
      Bound_Value : Big_Natural;
   function Print_Discrete (Nb : Big_Integer; Ty : Entity_Id) return String
     with Pre => Is_Discrete_Type (Ty);
   --  This routine is used to alter printing for values of Discrete_Type.
   --  When a value is close enough to the bounds of its type (Bound_Value
   --  close) and the type is not too small (Range greater than Bound_Type)
   --  then we print the value as a function of the bound of the type.
   --  Example:
   --  type Byte is range -128..127;
   --  V = - 127 is printed V = Byte'First + 1

   function Print_Fixed (Small : Big_Real; Nb : Big_Integer) return String;
   --  If the computation of Small * Nb is an integer we print it as an
   --  integer. If not, we print Nb * Num (Small) / Den (Small) with Small
   --  normalized.

   generic
      type T_Float is digits <>;
      K : CE_Parsing.Float_Kind;
   function Print_Float (Nb : T_Float) return String;
   --  Print a counterexample value as a float

   -------------------------------
   -- Make_CNT_Unbounded_String --
   -------------------------------

   function Make_CNT_Unbounded_String
     (Nul : Boolean;
      Str : Unbounded_String;
      Cnt : Natural := 1;
      Els : S_String_List.List := S_String_List.Empty)
      return CNT_Unbounded_String
   is
      Nul_Internal : constant Boolean :=
        Nul and not Gnat2Why_Args.Debug_Trivial;
      Elems        : S_String_List.List;

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
   end Make_CNT_Unbounded_String;

   --------------------
   -- Print_Discrete --
   --------------------

   function Print_Discrete (Nb : Big_Integer; Ty : Entity_Id) return String is

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

      Nb_Type  : Entity_Id := Ty;

   --  Start of processing for Print_Discrete

   begin
      --  If one of the bounds is not known, use the base type for evaluating
      --  the type range to decide if we alter printing.

      if not Compile_Time_Known_Value (Type_Low_Bound (Nb_Type))
        or else not Compile_Time_Known_Value (Type_High_Bound (Nb_Type))
      then
         Nb_Type := Base_Type (Nb_Type);
      end if;

      --  Beginning of safe computations

      declare
         --  Type informations

         Low_Bound  : constant Big_Integer :=
           From_String
             (UI_Image (Expr_Value (Type_Low_Bound (Nb_Type)), Decimal));
         High_Bound : constant Big_Integer :=
           From_String
             (UI_Image (Expr_Value (Type_High_Bound (Nb_Type)), Decimal));
         Type_Range : constant Big_Integer := High_Bound - Low_Bound;
         Type_Name  : constant String := Beautiful_Source_Name (Nb_Type);

         --  Difference calculations

         Diff_To_High : constant Big_Natural := abs (Nb - High_Bound);
         Diff_To_Low  : constant Big_Natural := abs (Nb - Low_Bound);
         Side         : Character;

      begin
         --  Do not print the counterexample if a value falls outside of the
         --  bounds of its type.

         if Nb < Low_Bound or else Nb > High_Bound then
            raise Parse_Error;
         end if;

         --  If the range of type is too small, we do nothing. If the type
         --  we are given is internal then we don't want to print it as it
         --  would confuse the user.
         --  Example: type Data_T is array (1 .. 1000) of Integer;
         --  There is an internal type Tdata_tD1 for range (1..1000) for
         --  indices: we don't want to print Tdata_tD1'First.

         if Type_Range <= Bound_Type
           or else (not Comes_From_Source (Nb_Type)
                    and then not Is_Standard_Type (Nb_Type))
         then
            return To_String (Nb);
         end if;

         --  Nb is closer to the highest bound

         if Diff_To_High <= Diff_To_Low then

            if Diff_To_High = 0 then
               return Type_Name & "'Last";

            elsif Diff_To_High < Bound_Value then
               Side := (if Nb < High_Bound then '-' else '+');
               return Type_Name & "'Last" & Side
                 & Trim (To_String (Diff_To_High), Left);

            else
               return To_String (Nb);
            end if;

         --  We don't want to print Natural'First + 5 as counterexample. So,
         --  there is a special case when Low_Bound of the type is in 0 .. 1.

         elsif Low_Bound = 0 or else Low_Bound = 1 then
            return To_String (Nb);

         else
            if Diff_To_Low = 0 then
               return Type_Name & "'First";

            elsif Diff_To_Low < Bound_Value then
               Side := (if Nb < Low_Bound then '-' else '+');
               return Type_Name & "'First" & Side
                 & Trim (To_String (Diff_To_Low), Left);

            else
               return To_String (Nb);
            end if;
         end if;
      end;
   end Print_Discrete;

   -----------------
   -- Print_Fixed --
   -----------------

   function Print_Fixed (Small : Big_Real; Nb : Big_Integer) return String is
   begin
      declare
         Nb_Real : constant Big_Real := To_Big_Real (Nb) * Small;
      begin
         if Denominator (Nb_Real) = 1 then
            return To_String (Numerator (Nb_Real));
         else
            declare
               Num_Small : constant Big_Integer := Numerator (Small);
               Den_Small : constant Big_Integer := Denominator (Small);
            begin
               return To_String (Nb)
                 & (if Num_Small /= 1
                    then "*" & Trim (To_String (Num_Small), Left)
                    else "")
                 & (if Den_Small /= 1
                    then "/" & Trim (To_String (Den_Small), Left)
                    else "");
            end;
         end if;
      end;
   end Print_Fixed;

   -----------------
   -- Print_Float --
   -----------------

   function Print_Float (Nb : T_Float) return String is
      package F_IO is new Ada.Text_IO.Float_IO (T_Float);
      Bound : constant Natural :=
        (case K is
            when Float_32_K => 32,
            when Float_64_K => 64,
            when Extended_K => 80);
      Result : String (1 .. Bound);

   begin
      --  To get nicer results we print small, exactly represented
      --  integers as 123.0 and not in the scientific notation. The
      --  choice of what is "small" is arbitrary; it could be anything
      --  within +/- 2**24 and +/- 2**54 (bounds excluded) for single and
      --  double precision floating point numbers, respectively.

      if abs (Nb) < 1000.0 and then T_Float'Truncation (Nb) = Nb then
         F_IO.Put (To   => Result,
                   Item => Nb,
                   Aft  => 0,
                   Exp  => 0);
      else
         F_IO.Put (To   => Result,
                   Item => Nb,
                   --  In the case of long_float, we print 10 decimals
                   --  and we print 7 in case of short float.
                   Aft  => (case K is
                               when Float_32_K => 7,
                               when Float_64_K => 10,
                               when Extended_K => 10),
                   Exp  => 1);
      end if;
      return Trim (Source => Result,
                   Side   => Both);
   end Print_Float;

   ------------------------
   -- Print_Scalar_Value --
   ------------------------

   function Print_Scalar_Value
     (Cnt_Value : Cntexmp_Value_Ptr;
      AST_Type  : Entity_Id) return CNT_Unbounded_String
   is
      function To_String
        (Value : Scalar_Value; Nul : out Boolean) return String;
      --  Turn Value into a string. Set Nul to True if Value might be
      --  represented as 0.

      ---------------
      -- To_String --
      ---------------

      function To_String
        (Value : Scalar_Value; Nul : out Boolean) return String
      is
      begin
         case Value.K is
            when Integer_K =>

               declare
                  --  Decision: generic values for Bound_Type and Bound_Value
                  --  are random for now. They can be adjusted in the future.

                  function Pretty_Print is
                    new Print_Discrete (Bound_Type  => 10,
                                        Bound_Value => 5);
               begin
                  Nul := Value.Integer_Content = 0;
                  return Pretty_Print (Value.Integer_Content, AST_Type);
               end;

            when Enum_K =>

               --  Necessary for some types that makes boolean be translated to
               --  integers like: "subype only_true := True .. True".

               if Is_Boolean_Type (AST_Type) then
                  Nul := Value.Enum_Entity = Boolean_Literals (False);
                  if Value.Enum_Entity = Boolean_Literals (True) then
                     return "True";
                  else
                     return "False";
                  end if;

               else
                  pragma Assert (Is_Enumeration_Type (AST_Type));

                  declare
                     Lit : constant Entity_Id := Value.Enum_Entity;

                  begin
                     --  Special case for characters, which are defined in the
                     --  standard unit Standard.ASCII, and as such do not have
                     --  a source code representation.

                     if Is_Character_Type (AST_Type) then

                        --  Nul is True if we have the literal at position 0

                        Nul := Char_Literal_Value (Value.Enum_Entity) = Uint_0;

                        --  Call Get_Unqualified_Decoded_Name_String to get a
                        --  correctly printed character in Name_Buffer.

                        Get_Unqualified_Decoded_Name_String (Chars (Lit));

                        --  The call to Get_Unqualified_Decoded_Name_String set
                        --  Name_Buffer to '<char>' where <char> is the
                        --  character we are interested in. Just retrieve it
                        --  directly at Name_Buffer(2).

                        return "'"
                          & Char_To_String_Representation (Name_Buffer (2))
                          & "'";

                     --  For all enumeration types that are not character,
                     --  call Get_Enum_Lit_From_Pos to get a corresponding
                     --  enumeratio n entity, then Source_Name to get a
                     --  correctly capitalized enumeration value.

                     else
                        --  Nul is True if we have the literal at position 0

                        Nul := (Enumeration_Pos (Value.Enum_Entity) = 0);

                        return Source_Name (Lit);
                     end if;
                  end;
               end if;

            when Fixed_K =>
               Nul := Value.Fixed_Content = 0;
               return Print_Fixed (Value.Small, Value.Fixed_Content);

            when Float_K =>
               case Value.Float_Content.K is
                  when Float_32_K =>
                     Nul := Value.Float_Content.Content_32 = 0.0;
                     declare
                        function Print is new Print_Float
                          (Float, Value.Float_Content.K);
                     begin
                        return Print (Value.Float_Content.Content_32);
                     end;
                  when Float_64_K =>
                     Nul := Value.Float_Content.Content_64 = 0.0;
                     declare
                        function Print is new Print_Float
                          (Long_Float, Value.Float_Content.K);
                     begin
                        return Print (Value.Float_Content.Content_64);
                     end;
                  when Extended_K =>
                     Nul := Value.Float_Content.Ext_Content = 0.0;
                     declare
                        function Print is new Print_Float
                          (Long_Long_Float, Value.Float_Content.K);
                     begin
                        return Print (Value.Float_Content.Ext_Content);
                     end;
               end case;
         end case;
      end To_String;

   --  Start of processing for Print_Scalar_Value

   begin
      declare
         Value  : constant Scalar_Value :=
           Parse_Scalar_Value (Cnt_Value, AST_Type);
         Nul    : Boolean;
         Result : constant String := To_String (Value, Nul);
      begin
         return Make_CNT_Unbounded_String
           (Nul => Nul,
            Str => To_Unbounded_String (Trim (Result, Both)));
      end;
   exception
      when Parse_Error =>
         return Dont_Display;
   end Print_Scalar_Value;

end CE_Pretty_Printing;
