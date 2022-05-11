------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             C E _ V A L U E S                            --
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

with Ada.Characters.Handling;   use Ada.Characters.Handling;
with Ada.Strings;               use Ada.Strings;
with Ada.Strings.Fixed;         use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Namet;                     use Namet;
with SPARK_Atree;               use SPARK_Atree;
with SPARK_Atree.Entities;      use SPARK_Atree.Entities;
with Uintp;                     use Uintp;

package body CE_Values is

   function Enum_Entity_To_String (E : Entity_Id) return String;
   --  Return a string for an enum entity

   function To_String (Value : Opt_Big_Integer) return String is
     (if Value.Present then To_String (Value.Content) else "UNDEFINED");
   --  Convert an optional big integer into a string

   function To_String (V : Float_Value) return String;
   --  Convert a float value to a string

   function To_String (V : Scalar_Value_Type) return String;
   --  Convert a scalar value to a string

   function To_String (B : Multidim_Bounds) return String;
   --  Convert the representation of a multi-dimensional array to a string

   function To_String
     (Fst, Lst : Opt_Big_Integer;
      M        : Big_Integer_To_Value_Maps.Map;
      O        : Value_Access)
      return String;
   --  Convert the fields of an array value to a string

   function To_String
     (F : Entity_To_Value_Maps.Map;
      B : Opt_Boolean) return String;
   --  Convert the fields of a record value to a string

   function To_String
     (V : Value_Access;
      N : Opt_Boolean) return String;
   --  Convert the fields of an access value to a string

   ---------------------------
   -- Enum_Entity_To_String --
   ---------------------------

   function Enum_Entity_To_String (E : Entity_Id) return String is
   begin
      if Nkind (E) = N_Character_Literal then
         return (1 => Get_Character
           (UI_To_CC (Char_Literal_Value (E))));
      else
         pragma Assert (Ekind (E) = E_Enumeration_Literal);
         return To_Upper (Get_Name_String (Chars (E)));
      end if;
   end Enum_Entity_To_String;

   ---------------
   -- To_String --
   ---------------

   function To_String (V : Float_Value) return String is
     (case V.K is
         when Float_32_K => V.Content_32'Image,
         when Float_64_K => V.Content_64'Image,
         when Extended_K => V.Ext_Content'Image);

   function To_String (V : Scalar_Value_Type) return String is
     (case V.K is
         when Enum_K    => Enum_Entity_To_String (V.Enum_Entity),
         when Integer_K => To_String (V.Integer_Content),
         when Fixed_K   => To_String (V.Fixed_Content) & " x "
           & To_String (V.Small),
         when Float_K   => To_String (V.Float_Content));

   function To_String
     (F : Entity_To_Value_Maps.Map;
      B : Opt_Boolean) return String
   is
      use Entity_To_Value_Maps;
      Res : Unbounded_String;
      C   : Cursor := F.First;

   begin
      if B.Present then
         Append (Res, "'Constrained => " & B.Content'Image);
         if Has_Element (C) then
            Append (Res, ", ");
         end if;
      end if;

      while Has_Element (C) loop
         Append (Res, Get_Name_String (Chars (Key (C)))
                 & " = " & To_String (F (C).all));
         Next (C);
         if Has_Element (C) then
            Append (Res, ", ");
         end if;
      end loop;
      return To_String ("(" & Res & ")");
   end To_String;

   function To_String
     (Fst, Lst : Opt_Big_Integer;
      M        : Big_Integer_To_Value_Maps.Map;
      O        : Value_Access)
      return String
   is
      use Big_Integer_To_Value_Maps;
      Res : Unbounded_String;
   begin
      Append (Res, "'First => " & To_String (Fst)
              & ", 'Last => " & To_String (Lst));
      for C in M.Iterate loop
         Append (Res, ", "
                 & To_String (Key (C)) & " => "
                 & To_String (M (C).all) & ",");
      end loop;
      Append (Res, ", others => " &
              (if O = null then "UNDEFINED" else To_String (O.all)));
      return To_String ("(" & Res & ")");
   end To_String;

   function To_String
     (V : Value_Access;
      N : Opt_Boolean) return String
   is
   begin
      if N.Present and then N.Content then
         return "NULL";
      elsif V = null then
         return "(ALL => UNDEFINED)";
      else
         return "(ALL => " & To_String (V.all) & ")";
      end if;
   end To_String;

   function To_String (B : Multidim_Bounds) return String is
      Res : Unbounded_String;
   begin
      for Dim in B.Content'Range loop
         if B.Content (Dim).First.Present then
            Append (Res, "'First (" & Trim (Dim'Image, Left) & ") => "
                    & To_String (B.Content (Dim).First.Content) & ", ");
         end if;
         if B.Content (Dim).Last.Present then
            Append (Res, "'Last (" & Trim (Dim'Image, Left) & ") => "
                    & To_String (B.Content (Dim).Last.Content) & ", ");
         end if;
      end loop;
      return To_String ("(" & Res & "others => ?)");
   end To_String;

   function To_String (V : Value_Type) return String is
     (case V.K is
         when Scalar_K  =>
           (if V.Initialized_Attr.Present
            then "('Initialize => " & V.Initialized_Attr.Content'Image
              & ", Value => "
            else "")
           & (if V.Scalar_Content = null then "UNDEFINED"
              else To_String (V.Scalar_Content.all))
           & (if V.Initialized_Attr.Present then ")" else ""),
         when Record_K   => To_String (V.Record_Fields, V.Constrained_Attr),
         when Array_K    => To_String
           (V.First_Attr, V.Last_Attr, V.Array_Values, V.Array_Others),
         when Multidim_K => To_String (V.Bounds),
         when Access_K   => To_String (V.Designated_Value, V.Is_Null));

   function To_String (V : Opt_Value_Type) return String is
     (if V.Present then To_String (V.Content) else "NONE");

end CE_Values;
