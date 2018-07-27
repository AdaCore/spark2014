------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   C E _ P R E T T Y _ P R I N T I N G                    --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                    Copyright (C) 2018-2018, AdaCore                      --
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
with Interfaces;               use Interfaces;

package body Ce_Pretty_Printing is

   --  Size returns the associate binary size of a #b or #x number (to help
   --  when building an unsigned integer).
   function Size (S : String) return Integer is
     (if S (S'First + 1) = 'x' then
           4 * (S'Length - 2)
      else
        (S'Length - 2));

   --  This package is generic so that part of the work done can be shared
   --  between 32bit and 64 bits float numbers.
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
            F_IO.Put (To   => Result_String,
                      Item => Result,
                      --  In the case of long_float, we print 10 decimals
                      --  and we print 7 in case of short float.
                      Aft  => (if Bound = 64 then 10 else 7),
                      Exp  => 1);
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

end Ce_Pretty_Printing;
