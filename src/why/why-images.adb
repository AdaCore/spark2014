------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           W H Y - I M A G E S                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2011-2021, AdaCore                     --
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

with Sinput;           use Sinput;
with SPARK_Util;

package body Why.Images is

   ----------------------------------------
   -- Can_Be_Printed_In_Decimal_Notation --
   ----------------------------------------

   function Can_Be_Printed_In_Decimal_Notation (N : Nat) return Boolean is
      M : Nat := N;
   begin
      while M mod 2 = 0 loop
         M := M / 2;
      end loop;

      while M mod 5 = 0 loop
         M := M / 5;
      end loop;

      return M = 1;
   end Can_Be_Printed_In_Decimal_Notation;

   function Img (Node : Node_Id) return String;

   function Img (Name : Symbol) return String is
     (if Name = No_Symbol then "<>" else Get (Name).all);

   function Img (Node : Why_Node_Set) return String is
      Result : constant String := Why_Node_Set'Image (Node);
      First  : constant Positive := Result'First + 1;
   begin
      return Result (First .. Result'Last);
   end Img;

   function Img (Node : Node_Id) return String is
      Result : constant String := Node_Id'Image (Node);
      First  : constant Positive := Result'First + 1;
   begin
      if Node = 0 then
         return "[empty]";
      else
         return Result (First .. Result'Last);
      end if;
   end Img;

   function Img (Ty : EW_Type) return String is
   begin
      case Ty is
         when EW_Builtin  => return "builtin";
         when EW_Abstract => return "[abstract node]";
         when EW_Split    => return "[split node]";
      end case;
   end Img;

   -------
   -- P --
   -------

   procedure P (O : Output_Id; Name : Symbol; As_String : Boolean := False) is
   begin
      P (O, Img (Name), As_String);
   end P;

   procedure P
     (O      : Output_Id;
      Value  : Source_Ptr;
      Marker : Symbol := No_Symbol)
   is
   begin
      if Value > No_Location then
         declare
            File : constant String := SPARK_Util.File_Name (Value);
            Line : constant Physical_Line_Number :=
              Get_Physical_Line_Number (Value);
            Mark : constant String :=
              (if Marker = No_Symbol then ""
               else "'@" & Img (Marker) & "@'");

            Sloc_Tag : constant String :=
              "[#""" & Mark & File & """" &
              Physical_Line_Number'Image (Line) & " " &
              "0" & " " &  --  dummy column1 0
              "0" & "]";   --  dummy column2 0
         begin
            P (O, Sloc_Tag);
         end;
      end if;
   end P;

   procedure P (O : Output_Id; Node : Why_Node_Id) is
   begin
      P (O, Why_Node_Set (Node));
   end P;

   procedure P (O : Output_Id; Node : Why_Node_Set) is
   begin
      P (O, Img (Node));
   end P;

   procedure P (O : Output_Id; Value : Boolean) is
   begin
      P (O, Boolean'Image (Value));
   end P;

   procedure P (O : Output_Id; Value : Uint) is
      H         : constant array (Int range 0 .. 15) of Character :=
                    "0123456789ABCDEF";
      Base      : constant := 10;
      Abs_Value : Uint;
      S         : constant Uintp.Save_Mark := Mark;
   begin
      --  ??? The Why Reference does not give any detail about
      --  the syntax of integer constants. We shall suppose that
      --  it is similar to OCaml's integer litterals:
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

      if Value = No_Uint then
         P (O, "?");
         return;
      end if;

      if Value < Uint_0 then
         P (O, "-");
         Abs_Value := -Value;
      else
         Abs_Value := Value;
      end if;

      declare
         Index : Natural := Natural (UI_Decimal_Digits_Hi (Abs_Value));
         Buf : String (1 .. Index);
      begin
         while Abs_Value >= Base loop
            Buf (Index) := H (UI_To_Int (Abs_Value rem Base));
            Abs_Value := Abs_Value / Base;
            Index := Index - 1;
         end loop;
         P (O, "" & H (UI_To_Int (Abs_Value rem Base)));
         P (O, Buf (Index + 1 .. Buf'Last));
      end;
      Release (S);
   end P;

   procedure P (O : Output_Id; Value : Ureal) is

      function Max_Number_Of_Decimals (Den : Uint) return Nat;
      --  Returns the maximal number of decimals when dividing a natural number
      --  by Den. Den is a multiple of factors 2 and 5 only. Every factor of
      --  10, 5 or 2 potentially adds a decimal.

      procedure Print_Decimal_Notation (Num, Den : Uint);
      --  Prints the decimal notation of fraction Num/Den. This fraction should
      --  be a number that can be written exactly in decimal notation.

      ----------------------------
      -- Max_Number_Of_Decimals --
      ----------------------------

      function Max_Number_Of_Decimals (Den : Uint) return Nat is
         M   : Uint := Den;
         Max : Nat := 0;

      begin
         while M mod 10 = 0 loop
            Max := Max + 1;
            M := M / 10;
         end loop;

         while M mod 2 = 0 loop
            Max := Max + 1;
            M := M / 2;
         end loop;

         while M mod 5 = 0 loop
            Max := Max + 1;
            M := M / 5;
         end loop;

         pragma Assert (M = 1);

         return Max;
      end Max_Number_Of_Decimals;

      ----------------------------
      -- Print_Decimal_Notation --
      ----------------------------

      --  To print Num/Den in decimal notation, compute the maximum number of
      --  decimals of the result, scale Num by 10 this maximum number of times,
      --  perform the exact division, and retrieve the integral and fractional
      --  parts of the result.

      procedure Print_Decimal_Notation (Num, Den : Uint) is
         Max          : constant Nat := Max_Number_Of_Decimals (Den);
         Scale_Factor : constant Uint := UI_From_Int (10) ** Max;
         Scale_Num    : constant Uint := Num * Scale_Factor;
         Scale_Result : constant Uint := Scale_Num / Den;

         pragma Assert (Scale_Num mod Den = 0);

         Int_Part   : constant Uint := Scale_Result / Scale_Factor;
         Fact_Part  : constant Uint := Scale_Result mod Scale_Factor;
         Scale_Part : Uint := Scale_Factor / 10;

      begin
         P (O, Int_Part);
         P (O, ".");

         --  If there is a fractional part, first print as many zeros as needed
         --  to reach the non-zero fractional part.

         if Fact_Part /= 0 then
            while Scale_Part > Fact_Part loop
               P (O, "0");
               Scale_Part := Scale_Part / 10;
            end loop;
         end if;

         P (O, Fact_Part);
      end Print_Decimal_Notation;

      Num    : constant Uint := Numerator (Value);
      Den    : constant Uint := Denominator (Value);
      Base   : constant Nat  := Rbase (Value);

   --  Start of processing for P

   begin
      --  ??? Same remark as in the case of integer constants:
      --  I suppose that Why's real constants follows the same syntax
      --  as OCaml's floating-point literals:
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

      --  As documented in urealp.ads, Ureal representation is constrained as
      --  follows:

      --  Negative numbers are represented by the sign flag being True.

      --  If the base is zero, then the absolute value of the Ureal is simply
      --  numerator/denominator, where denominator is positive. If the base is
      --  non-zero, then the absolute value is
      --       numerator / (base ** denominator).
      --  In that case, since base is positive, (base ** denominator) is also
      --  positive, even when denominator is negative or null.

      if UR_Is_Negative (Value) then
         P (O, "-.");
      end if;

      --  The base is zero, hence the absolute value is numerator/denominator

      if Base = 0 then
         P (O, Num);
         P (O, ".0");
         P (O, "/.");
         P (O, Den);
         P (O, ".0");

      --  The base is 10, hence the absolute value can be expressed directly in
      --  Why using the exponent notation E.

      elsif Base = 10 then
         P (O, Num);
         P (O, ".0");
         P (O, "E");
         P (O, -Den);

      --  The denominator is negative or null, hence the real number is
      --     numerator * (base ** (- denominator)).

      elsif Den <= Uint_0 then
         P (O, UI_Mul (Num, UI_Expon (Base, UI_Negate (Den))));
         P (O, ".0");

      --  The base has only 2 and 5 as prime factors, hence the real number can
      --  be written exactly in decimal notation.

      elsif Can_Be_Printed_In_Decimal_Notation (Base) then
         Print_Decimal_Notation (Num, UI_Expon (Base, Den));

      --  Otherwise, print a fraction

      else
         pragma Assert (Den > Uint_0);
         P (O, Num);
         P (O, ".0");
         P (O, "/.");
         P (O, UI_Expon (Base, Den));
         P (O, ".0");
      end if;
   end P;

   procedure P (O : Output_Id; Value : EW_Type) is
   begin
      P (O, Img (Value));
   end P;

   procedure P
     (O      : Output_Id;
      Value  : EW_Literal;
      Domain : EW_Domain := EW_Prog)
   is
   begin
      case Value is
         when EW_True =>
            if Domain in EW_Prog | EW_Term | EW_Pterm then
               P (O, "True");
            else
               P (O, "true");
            end if;

         when EW_False =>
            if Domain in EW_Prog | EW_Term | EW_Pterm then
               P (O, "False");
            else
               P (O, "false");
            end if;
      end case;
   end P;

   procedure P (O : Output_Id; Value : EW_Connector) is
   begin
      case Value is
         when EW_Or_Else =>
            P (O, "||");

         when EW_And_Then =>
            P (O, "&&");

         when EW_Imply =>
            P (O, "->");

         when EW_Equivalent =>
            P (O, "<->");

         when EW_Or =>
            P (O, "\/");

         when EW_And =>
            P (O, "/\");
      end case;
   end P;

   procedure P (O : Output_Id; Value : EW_Domain) is
   begin
      case Value is
         when EW_Term =>
            P (O, "[term]");

         when EW_Pred =>
            P (O, "[predicate]");

         when EW_Prog =>
            P (O, "[program]");

         when EW_Pterm =>
            P (O, "[program term]");
      end case;
   end P;

   procedure P (O : Output_Id; Value : EW_Clone_Type) is
   begin
      case Value is
         when EW_Import        =>
            P (O, "      "); --  import is now the default

         when EW_Export        =>
            P (O, "export");

         when EW_Clone_Default =>
            P (O, "      ");  --  for alignment of include declarations
      end case;
   end P;

   procedure P (O : Output_Id;
                Value : EW_Theory_Type;
                Empty_For_Theory : Boolean := False) is
   begin
      case Value is
         when EW_Theory =>
            if Empty_For_Theory then
               P (O, "      ");  --  for alignment of include declarations
            else
               P (O, "theory");
            end if;

         when EW_Module =>
            P (O, "module");
      end case;
   end P;

   procedure P (O : Output_Id; Value : EW_Subst_Type) is
   begin
      case Value is
         when EW_Type_Subst =>
            P (O, "type");

         when EW_Function   =>
            P (O, "function");

         when EW_Predicate  =>
            P (O, "predicate");

         when EW_Namepace   =>
            P (O, "namespace");

         when EW_Lemma      =>
            P (O, "lemma");

         when EW_Goal       =>
            P (O, "goal");
      end case;
   end P;

   procedure P (O : Output_Id; Value : EW_Assert_Kind) is
   begin
      case Value is
         when EW_Assert =>
            P (O, "assert");

         when EW_Check =>
            P (O, "check");

         when EW_Assume =>
            P (O, "assume");
      end case;
   end P;

   procedure P (O : Output_Id; Node : Node_Id) is
   begin
      P (O, Img (Node));
   end P;

   procedure P
     (O         : Output_Id;
      Value     : Symbol_Set;
      As_Labels : Boolean := False) is
   begin
      for Name of Value loop
         if As_Labels then
            P (O, "[@");
         end if;
         P (O, Name);
         if As_Labels then
            P (O, "]");
         end if;
         P (O, " ");
      end loop;
   end P;

   procedure P
     (O         : Output_Id;
      Value     : String_Sets.Set;
      As_Labels : Boolean := False) is
   begin
      for Name of Value loop
         if As_Labels then
            P (O, "[@");
         end if;
         P (O, Name);
         if As_Labels then
            P (O, "]");
         end if;
         P (O, " ");
      end loop;
   end P;

end Why.Images;
