------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           W H Y - I M A G E S                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2011, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Types; use Types;

with Ada.Strings.Unbounded;

package body Why.Images is

   ---------
   -- Img --
   ---------

   function Img (Name : Name_Id) return String is
   begin
      return Get_Name_String (Name);
   end Img;

   function Img (Node : Why_Node_Id) return String is
      Result : constant String := Why_Node_Id'Image (Node);
      First  : constant Positive := Result'First + 1;
   begin
      return Result (First .. Result'Last);
   end Img;

   function Img (Value : Uint) return String is
   begin
      --  ??? The Why Reference does not give any detail about
      --  the syntax of integer constants. We shall suppose that
      --  it is similar to Ocaml's integer litterals:
      --
      --  IntegerLiteral ::=
      --     [-]  UnprefixedIntegerLiteral
      --
      --  UnprefixedIntegerLiteral ::=
      --      DecimalLiteral
      --      HexadecimalLiteral
      --      OctalLiteral
      --      BinaryLiteral
      --
      --  DecimalLiteral ::=
      --      DecimalLiteral  Digit
      --      DecimalLiteral  _
      --      Digit
      --
      --  HexadecimalLiteral ::=
      --      HexadecimalLiteral  HexadecimalDigit
      --      HexadecimalLiteral  _
      --      0x  HexadecimalDigit
      --      0X  HexadecimalDigit
      --
      --  OctalLiteral ::=
      --      OctalLiteral  OctalDigit
      --      OctalLiteral  _
      --      0o  OctalDigit
      --      0O  OctalDigit
      --
      --  BinaryLiteral ::=
      --      BinaryLiteral  BinaryDigit
      --      BinaryLiteral  _
      --      0b  BinaryDigit
      --      0B  BinaryDigit
      --
      --  Digit ::=
      --      DecimalDigit
      --
      --  HexadecimalDigit ::=  { 0123456789abcdefABCDEF }
      --
      --  DecimalDigit ::=  { 0123456789 }
      --
      --  OctalDigit ::=  { 01234567 }
      --
      --  BinaryDigit ::=  { 01 }

      UI_Image (Value, Decimal);
      return UI_Image_Buffer (1 .. UI_Image_Length);
   end Img;

   function Img (Value : Ureal) return String is
      use Ada.Strings.Unbounded;

      Num    : constant Uint := Numerator (Value);
      Den    : constant Uint := Denominator (Value);
      Base   : constant Nat := Rbase (Value);
      Result : Unbounded_String := To_Unbounded_String ("");
   begin
      --  ??? Same remark as in the case of integer constants:
      --  I suppose that Why's real constants follows the same syntax
      --  as Ocaml's floating-point literals:
      --
      --      FloatingPointLiteral ::=
      --        [-]  UnprefixedFloatingPointLiteral
      --
      --      UnprefixedFloatingPointLiteral ::=
      --        DecimalLiteral  FractionalPart  ExponentPart
      --        DecimalLiteral  FractionalPart
      --        DecimalLiteral  ExponentPart
      --
      --      FractionalPart ::=
      --        FractionalPart  Digit
      --        FractionalPart  _
      --        .
      --
      --      ExponentPart ::=
      --        ExponentLetter  +  DecimalLiteral
      --        ExponentLetter  -  DecimalLiteral
      --        ExponentLetter     DecimalLiteral
      --
      --       ExponentLetter ::=  { eE }

      if UR_Is_Negative (Value) then
         Append (Result, "-");
      end if;

      if Base = 0 then
         Append (Result, Img (Num));
         Append (Result, "/");
         Append (Result, Img (Den));

      elsif Base = 10 then
         Append (Result, Img (Num));
         Append (Result, "E-");
         Append (Result, Img (Den));

      else
         Append (Result, Img (Num));

         if UI_To_Int (Den) > 0 then
            Append (Result, "/");
            Append (Result, Img ((UI_Expon (Den, Base))));

         elsif UI_To_Int (Den) < 0 then
            Append (Result, "*");
            Append (Result, Img ((UI_Expon (UI_Negate (Den), Base))));
         end if;
      end if;

      return To_String (Result);
   end Img;

end Why.Images;
