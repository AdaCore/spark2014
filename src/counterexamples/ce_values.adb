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
with Ada.Containers.Ordered_Sets;
with Ada.Strings;               use Ada.Strings;
with Ada.Strings.Fixed;         use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with CE_RAC;
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

   ---------
   -- "=" --
   ---------

   function "=" (V1, V2 : Float_Value) return Boolean is
     (V1.K = V2.K
      and then
        (case V1.K is
         when Float_32_K => V1.Content_32 = V2.Content_32,
         when Float_64_K => V1.Content_64 = V2.Content_64,
         when Extended_K => V1.Ext_Content = V2.Ext_Content));

   function "=" (V1, V2 : Scalar_Value_Type) return Boolean is
     (V1.K = V2.K
      and then
        (case V1.K is
            when Enum_K    =>
             (Nkind (V1.Enum_Entity) = Nkind (V2.Enum_Entity))
              and then
                (if Nkind (V1.Enum_Entity) = N_Character_Literal
                then Char_Literal_Value (V1.Enum_Entity) =
                  Char_Literal_Value (V2.Enum_Entity)
                else V1.Enum_Entity = V2.Enum_Entity),
            when Integer_K => V1.Integer_Content = V2.Integer_Content,
            --  The 2 following cases are currently unused as the rac does not
            --  support real values.
            when Float_K   => V1.Float_Content = V2.Float_Content,
            when Fixed_K   =>
               V1.Small = V2.Small
                 and then V1.Fixed_Content = V2.Fixed_Content));

   function "=" (V1, V2 : Value_Type) return Boolean is

      package Checked_Indices_Set is new Ada.Containers.Ordered_Sets
        (Element_Type => Big_Integer);
      --  Set of the indices that have been checked in an array.

      function Check_Array_Values
        (Arr1_Values :     Big_Integer_To_Value_Maps.Map;
         Arr1_First  :     Big_Integer;
         Arr2        :     Value_Type;
         Checked     : out Checked_Indices_Set.Set) return Boolean;
      --  Check that all the named components of the first array (which are all
      --  stored in Arr1_Values) are equal to the element at the same position
      --  in the second array Arr2. The Checked set is used to log which
      --  positions have been checked by the call to this function. Because
      --  equivalent arrays can have different First and Last indices, an
      --  element is identified by its offset from the array's first index
      --  Arr1_First.

      ------------------------
      -- Check_Array_Values --
      ------------------------

      function Check_Array_Values
        (Arr1_Values :     Big_Integer_To_Value_Maps.Map;
         Arr1_First  :     Big_Integer;
         Arr2        :     Value_Type;
         Checked     : out Checked_Indices_Set.Set) return Boolean
      is
         use Big_Integer_To_Value_Maps;

         Arr2_Values : constant Map          := Arr2.Array_Values;
         Arr2_Others : constant Value_Access := Arr2.Array_Others;
      begin

         for C1 in Arr1_Values.Iterate loop
            declare
               Checked_C :          Checked_Indices_Set.Cursor;
               Inserted  :          Boolean;
               Position  : constant Big_Integer := Key (C1) - Arr1_First;
               Offset    : constant Big_Integer :=
                 Position + Arr2.First_Attr.Content;
               C2        : constant Cursor      := Arr2_Values.Find (Offset);
            begin
               if (Has_Element (C2) and then Element (C1) = Element (C2))
                 or else Element (C1) = Arr2_Others
               then
                  Checked.Insert (Position, Checked_C, Inserted);
               else
                  return False;
               end if;
            end;
         end loop;

         return True;
      end Check_Array_Values;

   begin
      if V1.K /= V2.K then
         return False;
      end if;

      case V1.K is
         when Scalar_K =>

            --  Equality should only be called on initialized scalars

            if V1.Scalar_Content = null or else V2.Scalar_Content = null then
               raise Program_Error;
            end if;

            return V1.Scalar_Content.all = V2.Scalar_Content.all;

         when Record_K =>
            return Entity_To_Value_Maps."="
              (V1.Record_Fields, V2.Record_Fields);

         --  Multidimensional arrays are not supported yet

         when Multidim_K =>
            raise Program_Error;

         when Array_K  =>
            declare
               use Checked_Indices_Set;

               Length_V1  : constant Opt_Big_Integer := Get_Array_Length (V1);
               Length_V2  : constant Opt_Big_Integer := Get_Array_Length (V2);
               Checked_V1 : Set;
               Checked_V2 : Set;
            begin
               if Length_V1.Present and Length_V2.Present then
                  return (Length_V1.Content = 0 and then Length_V2.Content = 0)
                    or else (Length_V1.Content = Length_V2.Content
                    and then
                      Check_Array_Values
                        (V1.Array_Values, V1.First_Attr.Content, V2,
                         Checked_V1)
                    and then
                      Check_Array_Values
                        (V2.Array_Values, V2.First_Attr.Content, V1,
                         Checked_V2)
                    and then
                  --  If the length of the set containing all checked
                  --  indices is smaller than the total number of indices to
                  --  check (i.e. the values maps did not cover the whole
                  --  arrays) then the "others" values need to be checked for
                  --  equality.
                      (To_Big_Integer
                        (Integer
                           (Length (Union (Checked_V1, Checked_V2)))) =
                             Length_V1.Content
                      or else V1.Array_Others = V2.Array_Others));
               else
                  CE_RAC.RAC_Stuck
                    ("Missing index of array, cannot compute length");
               end if;
            end;

         when Access_K =>

            --  Equality on access should only be called when one operand in
            --  null. This case is currently unused as the rac does not support
            --  access values.

            if not (V1.Is_Null.Present and then V1.Is_Null.Content)
              and then not (V2.Is_Null.Present and then V2.Is_Null.Content)
            then
               raise Program_Error;
            end if;

            return (V1.Is_Null.Present and then V1.Is_Null.Content
                    and then V2.Is_Null.Present and then V2.Is_Null.Content);
      end case;
   end "=";

   function "=" (V1, V2 : Value_Access) return Boolean is
     (if Default_Equal (V1, null)
      then Default_Equal (V2, null)
      else not Default_Equal (V2, null) and then V1.all = V2.all);

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

   ----------------------
   -- Get_Array_Length --
   ----------------------

   function Get_Array_Length (V : Value_Type) return Opt_Big_Integer is
      Length : Big_Integer;
   begin
      if V.First_Attr.Present and V.Last_Attr.Present then
         Length := V.Last_Attr.Content - V.First_Attr.Content + 1;
         return (Present => True,
                 Content => (if Length > 0 then Length else 0));
      else
         return (Present => False);
      end if;
   end Get_Array_Length;

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
