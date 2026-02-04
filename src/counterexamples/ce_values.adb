------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             C E _ V A L U E S                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2022-2026, AdaCore                     --
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

with Ada.Characters.Handling; use Ada.Characters.Handling;
with Ada.Containers.Ordered_Sets;
with Ada.Strings;             use Ada.Strings;
with Ada.Strings.Fixed;       use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;   use Ada.Strings.Unbounded;
with CE_RAC;
with Gnat2Why.Tables;         use Gnat2Why.Tables;
with Namet;                   use Namet;
with SPARK_Atree;             use SPARK_Atree;
with String_Utils;            use String_Utils;
with Uintp;                   use Uintp;

package body CE_Values is

   function Char_Node_To_String (N : Node_Id) return String;
   --  Return a string for an enum entity

   function Enum_Entity_To_String (E : Entity_Id) return String;
   --  Return a string for an enum entity

   function To_String (Value : Opt_Big_Integer) return String
   is (if Value.Present then To_String (Value.Content) else "UNDEFINED");
   --  Convert an optional big integer into a string

   function To_String (V : Scalar_Value_Type) return String;
   --  Convert a scalar value to a string

   function To_String (B : Multidim_Bounds) return String;
   --  Convert the representation of a multi-dimensional array to a string

   function To_String
     (Fst, Lst : Opt_Big_Integer;
      M        : Big_Integer_To_Value_Maps.Map;
      O        : Value_Access) return String;
   --  Convert the fields of an array value to a string

   function To_String
     (F : Entity_To_Value_Maps.Map; B : Opt_Boolean) return String;
   --  Convert the fields of a record value to a string

   function To_String (V : Value_Access; N : Opt_Boolean) return String;
   --  Convert the fields of an access value to a string

   ---------
   -- "=" --
   ---------

   function "=" (V1, V2 : Float_Value) return Boolean
   is (V1.K = V2.K
       and then
         (case V1.K is
            when Float_32_K => V1.Content_32 = V2.Content_32,
            when Float_64_K => V1.Content_64 = V2.Content_64,
            when Extended_K => V1.Ext_Content = V2.Ext_Content));

   function "=" (V1, V2 : Scalar_Value_Type) return Boolean
   is (V1.K = V2.K
       and then
         (case V1.K is
            when Char_K    =>
              Nkind (V1.Char_Node) = Nkind (V2.Char_Node)
              and then
                Char_Literal_Value (V1.Char_Node)
                = Char_Literal_Value (V2.Char_Node),

            when Enum_K    =>
              Ekind (V1.Enum_Entity) = Ekind (V2.Enum_Entity)
              and then V1.Enum_Entity = V2.Enum_Entity,
            when Integer_K => V1.Integer_Content = V2.Integer_Content,
            --  The 2 following cases are currently unused as the rac
            --  does not support real values.
            when Float_K   => V1.Float_Content = V2.Float_Content,
            when Fixed_K   => V1.Fixed_Content = V2.Fixed_Content));

   function "=" (V1, V2 : Value_Type) return Boolean is

      package Checked_Indices_Set is new
        Ada.Containers.Ordered_Sets (Element_Type => Big_Integer);
      --  Set of the indices that have been checked in an array.

      function Check_Array_Values
        (Arr1_Values : Big_Integer_To_Value_Maps.Map;
         Arr1_First  : Big_Integer;
         Arr2        : Value_Type;
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
        (Arr1_Values : Big_Integer_To_Value_Maps.Map;
         Arr1_First  : Big_Integer;
         Arr2        : Value_Type;
         Checked     : out Checked_Indices_Set.Set) return Boolean
      is
         use Big_Integer_To_Value_Maps;

         Arr2_Values : constant Map := Arr2.Array_Values;
         Arr2_Others : constant Value_Access := Arr2.Array_Others;

      begin
         for C1 in Arr1_Values.Iterate loop
            declare
               Checked_C : Checked_Indices_Set.Cursor;
               Inserted  : Boolean;
               Position  : constant Big_Integer := Key (C1) - Arr1_First;
               Offset    : constant Big_Integer :=
                 Position + Arr2.First_Attr.Content;
               C2        : constant Cursor := Arr2_Values.Find (Offset);
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
         when Scalar_K   =>

            --  Equality should only be called on initialized scalars

            if V1.Scalar_Content = null or else V2.Scalar_Content = null then
               raise Program_Error;
            end if;

            return V1.Scalar_Content.all = V2.Scalar_Content.all;

         when Record_K   =>
            return
              Entity_To_Value_Maps."=" (V1.Record_Fields, V2.Record_Fields);

         --  Multidimensional arrays are not supported yet

         when Multidim_K =>
            raise Program_Error;

         when Array_K    =>
            declare
               use Checked_Indices_Set;

               Length_V1  : constant Opt_Big_Integer := Get_Array_Length (V1);
               Length_V2  : constant Opt_Big_Integer := Get_Array_Length (V2);
               Checked_V1 : Set;
               Checked_V2 : Set;
            begin
               if Length_V1.Present and Length_V2.Present then
                  return
                    (Length_V1.Content = 0 and then Length_V2.Content = 0)
                    or else
                      (Length_V1.Content = Length_V2.Content
                       and then
                         Check_Array_Values
                           (V1.Array_Values,
                            V1.First_Attr.Content,
                            V2,
                            Checked_V1)
                       and then
                         Check_Array_Values
                           (V2.Array_Values,
                            V2.First_Attr.Content,
                            V1,
                            Checked_V2)
                       and then
                         --  If the length of the set containing all
                         --  checked indices is smaller than the total
                         --  number of indices to check (i.e. the values
                         --  maps did not cover the whole arrays) then the
                         --  "others" values need to be checked for
                         --  equality.
                         (To_Big_Integer
                            (Integer (Length (Union (Checked_V1, Checked_V2))))
                          = Length_V1.Content
                          or else V1.Array_Others = V2.Array_Others));
               else
                  CE_RAC.RAC_Stuck
                    ("Missing index of array, cannot compute length");
               end if;
            end;

         when Access_K   =>

            --  Equality on access should only be called when one operand in
            --  null. This case is currently unused as the rac does not support
            --  access values.

            if not (V1.Is_Null.Present and then V1.Is_Null.Content)
              and then not (V2.Is_Null.Present and then V2.Is_Null.Content)
            then
               raise Program_Error;
            end if;

            return
              (V1.Is_Null.Present
               and then V1.Is_Null.Content
               and then V2.Is_Null.Present
               and then V2.Is_Null.Content);
      end case;
   end "=";

   function "=" (V1, V2 : Value_Access) return Boolean
   is (if Default_Equal (V1, null)
       then Default_Equal (V2, null)
       else not Default_Equal (V2, null) and then V1.all = V2.all);

   ---------------------
   -- Div_Fixed_Point --
   ---------------------

   function Div_Fixed_Point
     (Fixed_L, Fixed_R : Big_Integer; Small_L, Small_R, Small_Res : Big_Real)
      return Big_Integer
   is
      N_L   : constant Big_Integer := Numerator (Small_L);
      D_L   : constant Big_Integer := Denominator (Small_L);
      N_R   : constant Big_Integer := Numerator (Small_R);
      D_R   : constant Big_Integer := Denominator (Small_R);
      N_Res : constant Big_Integer := Numerator (Small_Res);
      D_Res : constant Big_Integer := Denominator (Small_Res);
   begin
      return (Fixed_L * N_L * D_R * D_Res) / (Fixed_R * N_R * D_L * N_Res);
   end Div_Fixed_Point;

   -------------------------
   -- Char_Node_To_String --
   -------------------------

   function Char_Node_To_String (N : Node_Id) return String is
   begin
      pragma Assert (Nkind (N) = N_Character_Literal);

      declare
         CC : constant Char_Code := UI_To_CC (Char_Literal_Value (N));
      begin
         if In_Character_Range (CC) then
            return (1 => Get_Character (CC));
         else
            CE_RAC.RAC_Stuck ("Bad value of character");
         end if;
      end;
   end Char_Node_To_String;

   ---------------------------
   -- Enum_Entity_To_String --
   ---------------------------

   function Enum_Entity_To_String (E : Entity_Id) return String is
   begin
      pragma Assert (Ekind (E) = E_Enumeration_Literal);

      return To_Upper (Get_Name_String (Chars (E)));
   end Enum_Entity_To_String;

   ----------------------
   -- Get_Array_Length --
   ----------------------

   function Get_Array_Length (V : Value_Type) return Opt_Big_Integer is
      Length : Big_Integer;
   begin
      if V.First_Attr.Present and V.Last_Attr.Present then
         Length := V.Last_Attr.Content - V.First_Attr.Content + 1;
         return
           (Present => True, Content => (if Length > 0 then Length else 0));
      else
         return (Present => False);
      end if;
   end Get_Array_Length;

   -----------------
   -- Valid_Value --
   -----------------

   function Valid_Value (V : Value_Type) return Boolean is
   begin
      case V.K is

         when Record_K =>
            declare
               use Entity_To_Value_Maps;
            begin
               for Cur in V.Record_Fields.Iterate loop
                  declare
                     C_Key : constant Entity_Id := Key (Cur);
                     C_Ty  : constant Entity_Id :=
                       Search_Component_In_Type (V.AST_Ty, C_Key);
                  begin
                     if not Present (C_Ty)
                       and then not Is_Tagged_Type (V.AST_Ty)
                     then
                        return False;
                     elsif Present (C_Ty) and then C_Key /= C_Ty then
                        return False;
                     end if;
                  end;
               end loop;
            end;

         when others   =>
            null;
      end case;
      return True;
   end Valid_Value;

   -------------------------------
   -- Search_Component_In_Value --
   -------------------------------

   function Search_Component_In_Value
     (Rec : Value_Type; Comp : Entity_Id) return Entity_Id is
   begin

      if Rec.Record_Fields.Contains (Comp) then
         return Comp;
      else
         declare
            Comp_In_AST_Ty : constant Entity_Id :=
              Search_Component_In_Type (Rec.AST_Ty, Comp);
         begin
            if Rec.Record_Fields.Contains (Comp_In_AST_Ty) then
               return Comp_In_AST_Ty;
            end if;
         end;
         return Types.Empty;
      end if;
   end Search_Component_In_Value;

   -----------------
   -- Update_Type --
   -----------------

   procedure Update_Type (V : in out Value_Type; T_New : Entity_Id) is
   begin
      if V.AST_Ty = T_New then
         return;  --  No change of the actual type.

      end if;

      if V.K = Record_K then
         pragma Assert (Is_Record_Type (T_New));
         declare
            use Entity_To_Value_Maps;
            Old_Fields : constant Entity_To_Value_Maps.Map := V.Record_Fields;
         begin
            V.Record_Fields.Clear;
            for C in Old_Fields.Iterate loop
               declare
                  Comp_In_T_New : constant Entity_Id :=
                    Search_Component_In_Type (T_New, Key (C));
               begin
                  if Present (Comp_In_T_New) then
                     V.Record_Fields.Insert (Comp_In_T_New, Element (C));
                  else
                     pragma Assert (Is_Tagged_Type (T_New));
                     --  For tagged types this is a legal scenario when
                     --  upcasting. For this component keep the component from
                     --  the old type.
                     V.Record_Fields.Insert (Key (C), Element (C));
                  end if;
               end;
            end loop;
         end;
      end if;

      V.AST_Ty := T_New;

   end Update_Type;

   --------------
   -- Is_Valid --
   --------------

   --  For checking the validity of floating-point values, disable validity
   --  checks introduced in debug builds by -gnatVa switch.

   pragma Suppress (Validity_Check);

   function Is_Valid (R : Float_Value) return Boolean is

      function Is_NaN (R : Float_Value) return Boolean
      is (case R.K is
            when Float_32_K => R.Content_32 /= R.Content_32,
            when Float_64_K => R.Content_64 /= R.Content_64,
            when Extended_K => R.Ext_Content /= R.Ext_Content);

      function Is_Infinity (R : Float_Value) return Boolean
      is (case R.K is
            when Float_32_K => abs R.Content_32 > Float'Last,
            when Float_64_K => abs R.Content_64 > Long_Float'Last,
            when Extended_K => abs R.Ext_Content > Long_Long_Float'Last);

   begin
      return not Is_NaN (R) and then not Is_Infinity (R);
      pragma
        Annotate
          (GNATSAS,
           False_Positive,
           "condition predetermined",
           "Is_NaN will return True on NaN values");
   end Is_Valid;

   pragma Unsuppress (Validity_Check);

   ----------------------
   -- Mult_Fixed_Point --
   ----------------------

   function Mult_Fixed_Point
     (Fixed_L, Fixed_R : Big_Integer; Small_L, Small_R, Small_Res : Big_Real)
      return Big_Integer
   is
      N_L   : constant Big_Integer := Numerator (Small_L);
      D_L   : constant Big_Integer := Denominator (Small_L);
      N_R   : constant Big_Integer := Numerator (Small_R);
      D_R   : constant Big_Integer := Denominator (Small_R);
      N_Res : constant Big_Integer := Numerator (Small_Res);
      D_Res : constant Big_Integer := Denominator (Small_Res);
   begin
      return (Fixed_L * N_L * Fixed_R * N_R * D_Res) / (D_L * D_R * N_Res);
   end Mult_Fixed_Point;

   --------------------
   -- To_Big_Integer --
   --------------------

   --  Conversion from float to integer rounds to the nearest integer, away
   --  from zero if exactly halfway between two integers.

   function To_Big_Integer (R : Float_Value) return Big_Integer is
      Big  : constant Big_Real := From_String (To_String (R));
      Bpos : constant Big_Real := abs Big;
      Sign : constant Big_Integer := (if Big < 0.0 then -1 else 1);
      Pos  : constant Big_Integer := Numerator (Bpos) / Denominator (Bpos);
      Rpos : constant Big_Real := To_Big_Real (Pos);
      Rnd  : constant Big_Integer := (if Bpos - Rpos <= 0.5 then 1 else 0);
   begin
      return Sign * (Pos + Rnd);
   end To_Big_Integer;

   ---------------
   -- To_String --
   ---------------

   --  Disable validity checks introduced in debug builds by -gnatVa switch so
   --  that invalid floating-point values like Inf or NaN could be represented.
   pragma Suppress (Validity_Check);

   function To_String (V : Float_Value) return String is
   begin
      return
        (case V.K is
           when Float_32_K => V.Content_32'Image,
           when Float_64_K => V.Content_64'Image,
           when Extended_K => V.Ext_Content'Image);
   end To_String;

   pragma Unsuppress (Validity_Check);

   function To_String (V : Scalar_Value_Type) return String
   is (case V.K is
         when Char_K    => Char_Node_To_String (V.Char_Node),
         when Enum_K    => Enum_Entity_To_String (V.Enum_Entity),
         when Integer_K => To_String (V.Integer_Content),
         when Fixed_K   => To_String (V.Fixed_Content),
         when Float_K   => To_String (V.Float_Content));

   function To_String
     (F : Entity_To_Value_Maps.Map; B : Opt_Boolean) return String
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
         Append
           (Res,
            Get_Name_String (Chars (Key (C))) & " = " & To_String (F (C).all));
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
      O        : Value_Access) return String
   is
      use Big_Integer_To_Value_Maps;
      Res : Unbounded_String;
   begin
      Append
        (Res,
         "'First => " & To_String (Fst) & ", 'Last => " & To_String (Lst));
      for C in M.Iterate loop
         Append
           (Res,
            ", " & To_String (Key (C)) & " => " & To_String (M (C).all) & ",");
      end loop;
      Append
        (Res,
         ", others => "
         & (if O = null then "UNDEFINED" else To_String (O.all)));
      return To_String ("(" & Res & ")");
   end To_String;

   function To_String (V : Value_Access; N : Opt_Boolean) return String is
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
            Append
              (Res,
               "'First ("
               & Trim (Dim'Image, Left)
               & ") => "
               & To_String (B.Content (Dim).First.Content)
               & ", ");
         end if;
         if B.Content (Dim).Last.Present then
            Append
              (Res,
               "'Last ("
               & Trim (Dim'Image, Left)
               & ") => "
               & To_String (B.Content (Dim).Last.Content)
               & ", ");
         end if;
      end loop;
      return To_String ("(" & Res & "others => ?)");
   end To_String;

   function To_String (V : Value_Type) return String
   is (case V.K is
         when Scalar_K   =>
           (if V.Initialized_Attr.Present
            then
              "('Initialized => "
              & V.Initialized_Attr.Content'Image
              & ", Value => "
            else "")
           & (if V.Scalar_Content = null
              then "UNDEFINED"
              else To_String (V.Scalar_Content.all))
           & (if V.Initialized_Attr.Present then ")" else ""),
         when Record_K   => To_String (V.Record_Fields, V.Constrained_Attr),
         when Array_K    =>
           To_String
             (V.First_Attr, V.Last_Attr, V.Array_Values, V.Array_Others),
         when Multidim_K => To_String (V.Bounds),
         when Access_K   => To_String (V.Designated_Value, V.Is_Null));

   function To_String (V : Opt_Value_Type) return String
   is (if V.Present then To_String (V.Content) else "NONE");

   function To_String (Attribute : Supported_Attribute) return String is
   begin
      return Standard_Ada_Case (Attribute'Img);
   end To_String;

end CE_Values;
