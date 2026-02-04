------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   C E _ P R E T T Y _ P R I N T I N G                    --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2026, AdaCore                     --
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

with Ada.Float_Text_IO;
with Ada.Long_Float_Text_IO;
with Ada.Long_Long_Float_Text_IO;
with Common_Containers;                     use Common_Containers;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Ordered_Maps;
with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;
with Ada.Strings;                           use Ada.Strings;
with Ada.Strings.Fixed;                     use Ada.Strings.Fixed;
with Ada.Strings.UTF_Encoding.Strings;
use Ada.Strings.UTF_Encoding.Strings;
with Ada.Text_IO;
with Casing;                                use Casing;
with CE_Parsing;                            use CE_Parsing;
with CE_RAC;                                use CE_RAC;
with CE_Utils;                              use CE_Utils;
with Gnat2Why.Tables;                       use Gnat2Why.Tables;
with Namet;                                 use Namet;
with SPARK_Atree;                           use SPARK_Atree;
with SPARK_Atree.Entities;                  use SPARK_Atree.Entities;
with SPARK_Util;                            use SPARK_Util;
with SPARK_Util.Types;                      use SPARK_Util.Types;
with Stand;                                 use Stand;
with Types;                                 use Types;
with Uintp;                                 use Uintp;

package body CE_Pretty_Printing is

   --------------
   -- Settings --
   --------------

   CE_Max_Print_Chars_String : constant := 30;
   --  Maximum length of a CE value having a String type and consisting only of
   --  printable characters that will fully be represented as a string literal.
   --  Longer values of such strings will be truncated.

   CE_Max_Print_Elems_Array : constant := 10;
   --  Maximum number of array elements in a CE value that are represented in
   --  an aggregate notation. Further elements will be represented by "...".

   function CE_Max_Print_Elems (Is_String : Boolean) return Natural
   is (if Is_String
       then CE_Max_Print_Chars_String
       else CE_Max_Print_Elems_Array);

   CE_Max_Exp_Others_In_Aggregate : constant := 1;
   --  Maximal number of elements for which the 'others' value can be expanded
   --  when printing as an aggregate. E.g., when the value is an array, but not
   --  one that can be printed as a string literal.

   ---------------------------------
   -- Types and Generic Instances --
   ---------------------------------

   type CNT_Attribute is record
      Attribute : Supported_Attribute;
      Name      : Unbounded_String;
      Value     : CNT_Unbounded_String;
   end record;
   --  Attributes are printed as a binding from a (possibly prefixed) name to a
   --  value. The Attribute field is used to keep the relation to the semantic
   --  attribute.

   package CNT_Attribute_Lists is new
     Ada.Containers.Doubly_Linked_Lists
       (Element_Type => CNT_Attribute,
        "="          => "=");

   subtype CNT_Attribute_List is CNT_Attribute_Lists.List;

   type Value_And_Attributes is record
      Value      : CNT_Unbounded_String;
      Attributes : CNT_Attribute_List;
   end record;
   --  Return type of the internal printing functions. It contains a string for
   --  the value parsed and a list of bindings for its attributes. The
   --  attribute bindings are relatively ordered according to the criteria in
   --  Ordered_Sloc_Maps and Ordered_Sloc_Attribute_Maps, i.e., first by
   --  components and then by attributes.

   type Component_Loc_Info is record
      Type_Ent : Entity_Id;
      Sloc     : Source_Ptr;
   end record;
   --  A location information for a component contains the type in which the
   --  component is declared first and the location of this first declaration.

   function Get_Loc_Info (Comp : Entity_Id) return Component_Loc_Info
   is ((Type_Ent => Original_Declaration (Comp),
        Sloc     =>
          Sloc
            (Search_Component_In_Type (Original_Declaration (Comp), Comp))));
   --  Construct the location information of a record component or
   --  discriminant.

   No_Loc_Info : constant Component_Loc_Info :=
     (Type_Ent => Empty, Sloc => No_Location);
   --  Component_Loc_Info value for the contexts where an actual source code
   --  location is not needed.

   function "<" (X, Y : Component_Loc_Info) return Boolean
   is ((X.Type_Ent /= Y.Type_Ent and then Is_Ancestor (X.Type_Ent, Y.Type_Ent))
       or else (X.Type_Ent = Y.Type_Ent and then X.Sloc < Y.Sloc));
   --  Order on location information. A component F1 is declared first than
   --  another F2 if F1 is declared in an ancestor of the type in which F2 is
   --  declared, or if they are declared in the same type and F1 occurs before
   --  in the source code.

   package Ordered_Sloc_Maps is new
     Ada.Containers.Ordered_Maps
       (Key_Type     => Component_Loc_Info,
        Element_Type => Value_And_Attributes,
        "<"          => "<");
   --  Map from sloc to strings, used to output component of record values in
   --  correct order.

   type Sloc_Attribute is record
      Sloc      : Component_Loc_Info;
      Attribute : Supported_Attribute;
   end record;

   function "<" (Left, Right : Sloc_Attribute) return Boolean
   is (if Left.Sloc /= Right.Sloc
       then Left.Sloc < Right.Sloc
       else Left.Attribute < Right.Attribute);

   package Ordered_Sloc_Attribute_Maps is new
     Ada.Containers.Ordered_Maps
       (Key_Type     => Sloc_Attribute,
        Element_Type => CNT_Attribute,
        "<"          => "<");
   --  Map for ordering pretty-printed names-value pairs of attributes
   --  according to the sloc of the respective entity, component index
   --  and attribute.

   subtype Ordered_Sloc_Attribute_Map is Ordered_Sloc_Attribute_Maps.Map;

   function To_List
     (Map : Ordered_Sloc_Attribute_Maps.Map) return CNT_Attribute_List;
   --  Returns all the elements of the map as a list. The list is sorted by the
   --  keys of the map.

   procedure Attributes_To_List
     (Res : in out CNT_Attribute_List; Map : in out Ordered_Sloc_Maps.Map);
   --  Appends the attribute values of all the elements in Map to the given
   --  list Res. The attributes are sorted by the keys of the map and the
   --  relative ordering of the attributes for each element is preserved.
   --  All attributes are removed from Map by the end of this procedure.

   -----------------------
   -- Local_Subprograms --
   -----------------------

   function Make_CNT_Attribute
     (Attribute   : Supported_Attribute;
      Value       : CNT_Unbounded_String;
      Name_Suffix : String := "") return CNT_Attribute;
   --  Create a CNT_Attribute, i.e., an attribute for pretty printing from the
   --  given Attribute, pretty-printed Value and an optional Name_Suffix.

   procedure Add_Attribute
     (Attributes : in out Ordered_Sloc_Attribute_Map;
      Attribute  : Supported_Attribute;
      Value      : CNT_Unbounded_String;
      Sloc       : Component_Loc_Info := No_Loc_Info);
   --  Add a new attribute to the Attributes map

   procedure Add_Attribute
     (Attributes       : in out Ordered_Sloc_Attribute_Map;
      Pretty_Attribute : CNT_Attribute;
      Sloc             : Component_Loc_Info := No_Loc_Info);
   --  Add a new attribute to the Attributes map

   function Prefix_Names
     (Elems : CNT_Attribute_List; Pref : String) return CNT_Attribute_List;
   --  Prefix all the names in Elems by Pref

   function Print_Access_Value (Value : Value_Type) return Value_And_Attributes
   with Pre => Value.K = Access_K;
   --  Print value of an access type. Designated values are printed as
   --  allocators, new Ty'(V).

   function Print_Array_Value (Value : Value_Type) return Value_And_Attributes
   with Pre => Value.K = Array_K;
   --  Print value of an array type in an aggregate-like syntax. When
   --  possible, string values are printed as string literals.

   generic
      Bound_Type : Big_Natural;
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

   function Print_Fixed
     (Small : Big_Real; Nb : Big_Integer; Always_Quotient : Boolean := False)
      return String;
   --  If the computation of Small * Nb is an integer we print it as an
   --  integer. If not, we print Nb * Num (Small) / Den (Small) with Small
   --  normalized. If Always_Quotient is True, always print as fraction.

   generic
      type T_Float is digits <>;
      K : CE_Values.Float_Kind;
   function Print_Float (Nb : T_Float) return String;
   --  Print a counterexample value as a float

   function Print_Record_Value (Value : Value_Type) return Value_And_Attributes
   with Pre => Value.K = Record_K;
   --  Print value of a record type in an aggregate like syntax. Hidden
   --  components are prefixed by the name of their enclosing type Ty.F => V.

   function Print_Scalar
     (Value : Scalar_Value_Type; AST_Type : Entity_Id)
      return CNT_Unbounded_String;
   --  Print a scalar counterexample value. The type is used to correctly print
   --  an Integer as a Character type for example.

   function Print_Value (Value : Value_Type) return Value_And_Attributes;
   --  Print a counterexample value

   -------------
   -- To_List --
   -------------

   function To_List
     (Map : Ordered_Sloc_Attribute_Maps.Map) return CNT_Attribute_List
   is
      Res : CNT_Attribute_List;
   begin
      for Elem of Map loop
         Res.Append (Elem);
      end loop;
      return Res;
   end To_List;

   ------------------------
   -- Attributes_To_List --
   ------------------------

   procedure Attributes_To_List
     (Res : in out CNT_Attribute_List; Map : in out Ordered_Sloc_Maps.Map) is
   begin
      for Position in Map.Iterate loop
         Res.Splice
           (CNT_Attribute_Lists.No_Element, Map (Position).Attributes);
      end loop;
   end Attributes_To_List;

   -------------------------------
   -- Make_CNT_Unbounded_String --
   -------------------------------

   function Make_CNT_Unbounded_String
     (Str : String;
      Cnt : Natural := 1;
      Els : String_Lists.List := String_Lists.Empty)
      return CNT_Unbounded_String
   is
      Elems : String_Lists.List;

   begin
      --  Otherwise if Els is empty, use the singleton " = Str " for the value

      if Els.Is_Empty then
         Elems.Append (" = " & Str);

      --  Otherwise use Els

      else
         Elems := Els;
      end if;

      return (Str => To_Unbounded_String (Str), Count => Cnt, Elems => Elems);
   end Make_CNT_Unbounded_String;

   ------------------------
   -- Make_CNT_Attribute --
   ------------------------

   function Make_CNT_Attribute
     (Attribute   : Supported_Attribute;
      Value       : CNT_Unbounded_String;
      Name_Suffix : String := "") return CNT_Attribute is
   begin
      return
        (Attribute,
         To_Unbounded_String (''' & To_String (Attribute) & Name_Suffix),
         Value);
   end Make_CNT_Attribute;

   -------------------
   -- Add_Attribute --
   -------------------

   procedure Add_Attribute
     (Attributes : in out Ordered_Sloc_Attribute_Map;
      Attribute  : Supported_Attribute;
      Value      : CNT_Unbounded_String;
      Sloc       : Component_Loc_Info := No_Loc_Info) is
   begin
      Add_Attribute (Attributes, Make_CNT_Attribute (Attribute, Value), Sloc);
   end Add_Attribute;

   procedure Add_Attribute
     (Attributes       : in out Ordered_Sloc_Attribute_Map;
      Pretty_Attribute : CNT_Attribute;
      Sloc             : Component_Loc_Info := No_Loc_Info)
   is
      Key : constant Sloc_Attribute := (Sloc, Pretty_Attribute.Attribute);
   begin
      Attributes.Insert (Key, Pretty_Attribute);
   end Add_Attribute;

   ------------------
   -- Prefix_Names --
   ------------------

   function Prefix_Names
     (Elems : CNT_Attribute_List; Pref : String) return CNT_Attribute_List
   is
      Res : CNT_Attribute_List := Elems;
   begin
      for E of Res loop
         E.Name := Pref & E.Name;
      end loop;
      return Res;
   end Prefix_Names;

   -------------------------
   -- Print_Access_Value --
   -------------------------

   function Print_Access_Value (Value : Value_Type) return Value_And_Attributes
   is
      Res : Value_And_Attributes;

   begin
      if Value.Is_Null.Present and then Value.Is_Null.Content then
         Res.Value := Make_CNT_Unbounded_String (Str => "null");

      elsif Value.Designated_Value = null then
         Res.Value := Dont_Display;

      --  Reconstruct the value

      else
         declare
            V      : constant Value_And_Attributes :=
              Print_Value (Value.Designated_Value.all);
            Elems  : String_Lists.List;
            Des_Ty : Entity_Id;
         begin
            if V.Value = Dont_Display then
               Res.Value := Dont_Display;
            else
               Elems := Prefix_Elements (V.Value.Elems, ".all");

               --  Get the designated type which will printed in the allocator.
               --  Avoid Itypes which might have internal names.

               Des_Ty := Value.Designated_Value.AST_Ty;
               if Is_Itype (Des_Ty) then
                  Des_Ty := Etype (Des_Ty);
               end if;

               Res.Value :=
                 Make_CNT_Unbounded_String
                   (Str =>
                      "new "
                      & Raw_Source_Name (Des_Ty)
                      & "'("
                      & To_String (V.Value.Str)
                      & ')',
                    Cnt => V.Value.Count,
                    Els => Elems);

            end if;
            Res.Attributes := Prefix_Names (V.Attributes, ".all");
         end;
      end if;
      return Res;
   end Print_Access_Value;

   -----------------------
   -- Print_Array_Value --
   -----------------------

   function Print_Array_Value (Value : Value_Type) return Value_And_Attributes
   is
      type Array_Elem is record
         Ind_Printed  : CNT_Unbounded_String; -- Index value as printed
         Elem_Printed : CNT_Unbounded_String; -- Element value as printed
      end record;

      package Sorted_Array is new
        Ada.Containers.Ordered_Maps
          (Key_Type     => Big_Integer,
           Element_Type => Array_Elem,
           "<"          => "<");

      procedure Add_Index
        (S_Array             : in out Sorted_Array.Map;
         Is_String_Lit       : in out Boolean;
         First_Non_Printable : in out Opt_Big_Integer;
         Index               : Big_Integer;
         Index_Type          : Entity_Id;
         Is_String           : Boolean;
         Is_Truncated        : Boolean;
         Element_Value       : Value_And_Attributes);
      --  Add a mapping for Index => Element_Value in S_Array if Index
      --  corresponds to a valid value of type Index_Type and both Index and
      --  Element_Value can be printed.
      --
      --  Note that attributes of the values of array elements are discarded
      --  since they are currently not expected to contain practically useful
      --  information.
      --
      --  @param S_Array Sorted collection of pretty-printed array elements.
      --  @param Is_String_Lit Flag to indicate whether the array can be
      --    represented as a string literal or not.
      --  @param First_Non_Printable The position of the first non-printable
      --    character. Irrelevant when the array is not a string.
      --  @param Index The currently selected index of the array.
      --  @param Index_Type The type of Index.
      --  @param Is_String True iff the array is a string.
      --  @param Is_Truncated Flag to indicate whether Index is already beyond
      --    the truncation limit or not. In this case the S_Array is not grown
      --    any more. The new element is added only if it has an index smaller
      --    than some existing element. The last element will be removed then.
      --  @param Element_Value Pretty-printed value of the array element at
      --    Index.

      function Is_Normal_Char (S : Unbounded_String) return Boolean
      is (Length (S) = 3)
      with
        Pre =>
          Length (S) >= 3
          and then Element (S, 1) = '''
          and then Element (S, Length (S)) = ''';
      --  Return True if S is the representation of a normal character

      function Parse_And_Print_Index
        (Index : Big_Integer; Index_Type : Entity_Id)
         return CNT_Unbounded_String;
      --  Use the parsing and pretty printing of scalars to transform an index
      --  value as a big integer into an appropriate string representation.

      procedure Print_Elements
        (Value         : Value_Type;
         S_Array       : out Sorted_Array.Map;
         Is_String_Lit : out Boolean;
         Is_Complete   : out Boolean;
         Is_Truncated  : out Boolean;
         Others_Val    : out CNT_Unbounded_String;
         Attributes    : out CNT_Attribute_List);
      --  Check and export all parts of Value in an appropriate format.
      --
      --  @param S_Array A map containing the pretty-printed elements sorted by
      --    index.
      --  @param Is_String_Lit A flag that is set to True iff all the printed
      --    elements are normal characters.
      --  @param Is_Complete A flag that is set to True iff the S_Array alone
      --    is sufficient to print the value up to the truncation limit. In
      --    this case the Others_Val is irrelevant.
      --  @param Is_Truncated A flag that is set to True iff Value contains
      --    more elements than a predefined limit and S_Array only contains a
      --    part of them.
      --  @param Others_Val The default value for the elements not in S_Array.
      --  @param Attributes The list of pretty-printed attributes of Value. The
      --    attributes only concern the array value as a whole. Attributes of
      --    array elements are not printed.

      ---------------
      -- Add_Index --
      ---------------

      procedure Add_Index
        (S_Array             : in out Sorted_Array.Map;
         Is_String_Lit       : in out Boolean;
         First_Non_Printable : in out Opt_Big_Integer;
         Index               : Big_Integer;
         Index_Type          : Entity_Id;
         Is_String           : Boolean;
         Is_Truncated        : Boolean;
         Element_Value       : Value_And_Attributes)
      is
         Ind_Printed : constant CNT_Unbounded_String :=
           Parse_And_Print_Index (Index, Index_Type);

      begin
         if Ind_Printed /= Dont_Display then
            if Element_Value.Value /= Dont_Display then
               S_Array.Include
                 (Key      => Index,
                  New_Item =>
                    (Ind_Printed  => Ind_Printed,
                     Elem_Printed => Element_Value.Value));

               if Is_String
                 and then not Is_Normal_Char (Element_Value.Value.Str)
               then
                  Is_String_Lit := False;
                  if First_Non_Printable.Present then
                     First_Non_Printable.Content :=
                       Min (First_Non_Printable.Content, Index);
                  else
                     First_Non_Printable :=
                       (Present => True, Content => Index);
                  end if;
               end if;

               --  If the output is going to be truncated, then we must keep
               --  the current size. Remove the last element (according to the
               --  sorted order).

               if Is_Truncated then
                  S_Array.Delete_Last;
               end if;
            end if;

         end if;
      end Add_Index;

      ---------------------------
      -- Parse_And_Print_Index --
      ---------------------------

      function Parse_And_Print_Index
        (Index : Big_Integer; Index_Type : Entity_Id)
         return CNT_Unbounded_String
      is
         Value : Scalar_Value_Type;
      begin
         Value :=
           Parse_Scalar_Value
             (Cntexmp_Value'
                (T => Cnt_Integer,
                 I => To_Unbounded_String (To_String (Index))),
              Index_Type);
         return Print_Scalar (Value, Index_Type);
      exception
         when Parse_Error =>
            return Dont_Display;
      end Parse_And_Print_Index;

      --------------------
      -- Print_Elements --
      --------------------

      procedure Print_Elements
        (Value         : Value_Type;
         S_Array       : out Sorted_Array.Map;
         Is_String_Lit : out Boolean;
         Is_Complete   : out Boolean;
         Is_Truncated  : out Boolean;
         Others_Val    : out CNT_Unbounded_String;
         Attributes    : out CNT_Attribute_List)
      is
         Fst_Index  : Node_Id := First_Index (Value.AST_Ty);
         Index_Type : Entity_Id;

         Others_Elem : Value_And_Attributes;

         Attr_First          : Opt_Big_Integer := Value.First_Attr;
         Attr_Last           : Opt_Big_Integer := Value.Last_Attr;
         Value_First_Pos     : Big_Integer;
         Value_Last_Pos      : Big_Integer;
         First_Non_Printable : Opt_Big_Integer := (Present => False);
         Full_Length         : Big_Integer;    --  Full length of the array
         Is_String           : constant Boolean :=
           Is_String_Type (Value.AST_Ty);

         use type Ada.Containers.Count_Type;

      begin
         Is_Truncated := False;

         --  Empty arrays can have bounds in the base type of their index type

         if Attr_First.Present
           and then Attr_Last.Present
           and then Attr_First.Content > Attr_Last.Content
         then
            Fst_Index := Etype (Etype (Fst_Index));
         end if;
         Index_Type := Retysp (Etype (Fst_Index));

         --  Use static array type bounds or index type bounds as default

         declare
            U_Fst : Uint;
            U_Lst : Uint;
         begin
            Find_First_Static_Range (Fst_Index, U_Fst, U_Lst);
            Value_First_Pos := From_String (UI_Image (U_Fst, Decimal));
            Value_Last_Pos := From_String (UI_Image (U_Lst, Decimal));
         end;

         --  Update bounds from the attribute values if any. We ignore out of
         --  bound values.

         if Attr_First.Present and then Attr_First.Content >= Value_First_Pos
         then
            Value_First_Pos := Attr_First.Content;
         else
            Attr_First := (Present => False);
         end if;

         if Attr_Last.Present and then Attr_Last.Content <= Value_Last_Pos then
            Value_Last_Pos := Attr_Last.Content;
         else
            Attr_Last := (Present => False);
         end if;

         Full_Length := Max (0, Value_Last_Pos - Value_First_Pos + 1);

         --  Format the "others" choice if any

         if Value.Array_Others /= null then
            Others_Elem := Print_Value (Value.Array_Others.all);
         else
            Others_Elem.Value := Dont_Display;
         end if;

         --  Make an initial guess if the value could be printed as a string
         --  literal or not. It will be refined further down.

         Is_String_Lit := Is_String;

         --  Populate the ordered S_Array with pretty-printed elements

         for C in Value.Array_Values.Iterate loop

            declare
               Index : Big_Integer renames Big_Integer_To_Value_Maps.Key (C);
               Elem  : Value_Access renames Value.Array_Values (C);

               Elem_Printed : constant Value_And_Attributes :=
                 Print_Value (Elem.all);
            begin
               --  We collapse indexes with the others choice if they are the
               --  same.

               if Value_First_Pos <= Index
                 and then Index <= Value_Last_Pos
                 and then
                   (Value_First_Pos = Value_Last_Pos
                    or else Elem_Printed /= Others_Elem)
               then
                  Add_Index
                    (S_Array,
                     Is_String_Lit,
                     First_Non_Printable,
                     Index,
                     Index_Type,
                     Is_String,
                     Is_Truncated,
                     Elem_Printed);

               end if;

               --  Check for the maximum printed length

               if Integer (S_Array.Length)
                 >= CE_Max_Print_Elems (Is_String_Lit)
               then

                  --  Record the fact that we've reached the truncation limit.
                  --  However, keep going through the values since there might
                  --  be elements with *lower* index positions remaining than
                  --  seen so far. Instead we avoid growing the length of
                  --  S_Array at this point.

                  Is_Truncated := True;
               end if;
            end;
         end loop;

         Is_Complete :=
           To_Big_Integer (Integer (S_Array.Length)) >= Full_Length;

         ------------------------------
         --  Handle the "others" part -
         ------------------------------

         --  If the list of printed elements is not yet complete we'll try to
         --  use the "others" value, if possible.

         if not Is_Complete then

            --  Update the initial guess for Is_String_Lit if the array
            --  elements are fully defined by "others".

            if Is_String_Lit
              and then S_Array.Length = 0
              and then Others_Elem.Value /= Dont_Display
            then
               Is_String_Lit := Is_Normal_Char (Others_Elem.Value.Str);
            end if;

            --  Expand "others" to individual array elements if
            --  * Others_Val is provided
            --  * and the bounds are known
            --  * and
            --    * we have a printable string
            --      - Note: If the expanded string would exceed printing limit
            --        it will be truncated.
            --    * or we are missing less than CE_Max_Exp_Others_In_Aggregate
            --      values
            --      - Note: The same truncation behavior as above is applied.

            if Others_Elem.Value /= Dont_Display
              and then
                ((Attr_First.Present and then Attr_Last.Present)
                 or else Is_Static_Array_Type (Value.AST_Ty))
              and then
                (Is_String_Lit
                 or else
                   To_Big_Integer (Integer (S_Array.Length))
                   >= Full_Length - CE_Max_Exp_Others_In_Aggregate)
            then
               declare
                  Index         : Big_Integer := Value_First_Pos;
                  Display_Limit : constant Natural :=
                    CE_Max_Print_Elems (Is_String_Lit);
                  Print_Upper   : constant Big_Integer :=
                    Min
                      (Value_Last_Pos,
                       Value_First_Pos
                       + To_Big_Integer (Integer (Display_Limit - 1)));
               begin

                  while Index <= Print_Upper loop
                     if not S_Array.Contains (Index) then

                        --  Add the element to S_Array, but make sure to keep
                        --  it within the Display_Limit,

                        if Natural (S_Array.Length) >= Display_Limit then
                           Is_Truncated := True;
                        end if;

                        Add_Index
                          (S_Array,
                           Is_String_Lit,
                           First_Non_Printable,
                           Index,
                           Index_Type,
                           Is_String,
                           Is_Truncated,
                           Others_Elem);
                     end if;

                     Index := Index + 1;
                  end loop;

                  --  All the elements that fit to the display limit should
                  --  exist in S_Array now.

                  pragma
                    Assert
                      (To_Big_Integer (Integer (S_Array.Length))
                       = Print_Upper - Value_First_Pos + 1);

                  --  If the full expansion would have exceeded the display
                  --  limit, then mark the final value still as truncated.

                  if Print_Upper < Value_Last_Pos then
                     Is_Truncated := True;

                  --  Otherwise, we have printed everything

                  else
                     Is_Complete := True;
                  end if;
               end;

            --  If we had reached the display limit already, the value will be
            --  marked as truncated regardless of whether an "others" value was
            --  provided or not.

            elsif Integer (S_Array.Length)
              >= CE_Max_Print_Elems (Is_String_Lit)
            then

               Is_Truncated := True;
               Others_Val := Dont_Display;

            --  Otherwise, if we have a printable "others" value, then let it
            --  be explicitly printed using aggregate notation.

            elsif Others_Elem.Value /= Dont_Display then

               --  Explicit "others" element will be printed. However, any
               --  attributes it might have had are dropped.

               Others_Val := Others_Elem.Value;

            --  Finally, if we don't have a printable "others" value, then
            --  treat it the same as a truncated value.

            else
               Is_Truncated := True;
               Others_Val := Dont_Display;

            end if;

         end if;

         -------------------------------
         --  Adjust printing as string -
         -------------------------------

         --  If the string has non-printable characters, but they occur after
         --  the truncation point, then still print as string.

         if Is_String
           and then Is_Truncated
           and then not Is_String_Lit
           and then First_Non_Printable.Present
           and then First_Non_Printable.Content > S_Array.Last_Key
         then
            Is_String_Lit := True;
         end if;

         -----------------------
         --  Handle attributes -
         -----------------------

         --  Add the First and Last attributes if any. Do not add the attribute
         --  if the array type is static or if they are implied by the
         --  aggregate value. For string literals, the first bound is not
         --  implied even if the aggregate is complete. No attributes are
         --  currently printed for the array elements.

         Attributes.Clear;

         if not Is_Static_Array_Type (Value.AST_Ty)
           and then
             (Is_String_Lit
              or else not Is_Complete
              or else Value_Last_Pos < Value_First_Pos)
         then
            if Attr_First.Present then
               declare
                  First_Str : constant CNT_Unbounded_String :=
                    Parse_And_Print_Index (Attr_First.Content, Index_Type);
               begin
                  if First_Str /= Dont_Display then
                     Attributes.Append (Make_CNT_Attribute (First, First_Str));
                  end if;
               end;
            end if;
            if (not Is_Complete or else Value_Last_Pos < Value_First_Pos)
              and then Attr_Last.Present
            then
               declare
                  Last_Str : constant CNT_Unbounded_String :=
                    Parse_And_Print_Index (Attr_Last.Content, Index_Type);
               begin
                  if Last_Str /= Dont_Display then
                     Attributes.Append (Make_CNT_Attribute (Last, Last_Str));
                  end if;
               end;
            end if;
         end if;
      end Print_Elements;

      --  Local variables

      S             : Unbounded_String;
      S_Array       : Sorted_Array.Map;
      Others_Val    : CNT_Unbounded_String;
      Is_Complete   : Boolean;
      Is_String_Lit : Boolean;
      Is_Truncated  : Boolean;
      Count         : Natural := 0;
      Elems         : String_Lists.List;
      Res           : Value_And_Attributes;

      ---------------------
      -- Truncate_Marker --
      ---------------------

      function Truncate_Marker return String
      is (if Is_Truncated
          then (if Is_String_Lit then " " else ", ") & "..."
          else "");

      use String_Lists;

      --  Start of processing for Print_Array_Value

   begin
      Print_Elements
        (Value,
         S_Array,
         Is_String_Lit,
         Is_Complete,
         Is_Truncated,
         Others_Val,
         Res.Attributes);

      --  Print complete strings containing only normal characters as string
      --  literals.

      if Is_String_Lit then
         for C of S_Array loop
            Append (S, Element (C.Elem_Printed.Str, 2));
         end loop;

         if S = "" then
            Res.Value := Dont_Display;
         else
            Res.Value :=
              Make_CNT_Unbounded_String
                (Str => '"' & To_String (S) & Truncate_Marker & '"');
         end if;

      --  Otherwise, use an aggregate notation

      else
         --  Add an association per specific element in S_Array

         for C in S_Array.Iterate loop
            declare
               Ind_Printed  : constant CNT_Unbounded_String :=
                 S_Array (C).Ind_Printed;
               Elem_Printed : constant CNT_Unbounded_String :=
                 S_Array (C).Elem_Printed;
               C_Elems      : String_Lists.List :=
                 Prefix_Elements
                   (Elem_Printed.Elems,
                    To_String ('(' & Ind_Printed.Str & ')'));
            begin
               if S /= "" then
                  Append (S, ", ");
               end if;

               pragma Assert (Elem_Printed /= Dont_Display);

               Count := Count + Elem_Printed.Count;
               Append (S, Ind_Printed.Str & " => " & Elem_Printed.Str);

               Elems.Splice (Before => No_Element, Source => C_Elems);
            end;
         end loop;

         --  If the aggregate is not complete and it wasn't truncated, add an
         --  association for its others case. Don't add it if the others case
         --  is unknown and there are no specific cases.

         if not Is_Complete
           and then not Is_Truncated
           and then Others_Val /= Dont_Display
         then
            if S /= "" then
               Append (S, ", ");
            end if;

            --  Append the "others" value to the buffer S, but do not insert
            --  a value for it in Elems.
            Append (S, "others => " & Others_Val.Str);
            Count := Count + Others_Val.Count;
         end if;

         if S = "" then
            Res.Value := Dont_Display;
         else
            Res.Value :=
              Make_CNT_Unbounded_String
                (Str => '(' & To_String (S) & Truncate_Marker & ')',
                 Cnt => Count,
                 Els => Elems);
         end if;
      end if;
      return Res;
   end Print_Array_Value;

   --------------------
   -- Print_Discrete --
   --------------------

   function Print_Discrete (Nb : Big_Integer; Ty : Entity_Id) return String is

      function Beautiful_Source_Name (Ty : Entity_Id) return String
      with Pre => Is_Discrete_Type (Ty);
      --  Does the same as Raw_Source_Name except for types defined in Standard
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
            return Raw_Source_Name (Ty);
         end if;
      end Beautiful_Source_Name;

      --  Local variables

      Nb_Type : Entity_Id := Ty;

      --  Start of processing for Print_Discrete

   begin
      --  Try to avoid base types introduced by the compiler if possible

      if not Comes_From_Source (Nb_Type)
        and then not Is_Standard_Type (Nb_Type)
        and then Present (First_Subtype (Nb_Type))
      then
         Nb_Type := First_Subtype (Nb_Type);
      end if;

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
           or else
             (not Comes_From_Source (Nb_Type)
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
               return
                 Type_Name
                 & "'Last"
                 & Side
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
               return
                 Type_Name
                 & "'First"
                 & Side
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

   function Print_Fixed
     (Small : Big_Real; Nb : Big_Integer; Always_Quotient : Boolean := False)
      return String is
   begin
      declare
         Nb_Real : constant Big_Real := To_Big_Real (Nb) * Small;
      begin
         if Denominator (Nb_Real) = 1 then
            return
              To_String (Numerator (Nb_Real))
              & (if Always_Quotient then "/1" else "");
         else
            declare
               Num_Small : constant Big_Integer := Numerator (Small);
               Den_Small : constant Big_Integer := Denominator (Small);
            begin
               return
                 To_String (Nb)
                 & (if Num_Small /= 1
                    then "*" & Trim (To_String (Num_Small), Left)
                    else "")
                 & (if Den_Small /= 1 or Always_Quotient
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
      Bound  : constant Natural :=
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

      if abs Nb < 1000.0 and then T_Float'Truncation (Nb) = Nb then
         F_IO.Put (To => Result, Item => Nb, Aft => 0, Exp => 0);
      else
         F_IO.Put
           (To   => Result,
            Item => Nb,
            --  In the case of long_float, we print 10 decimals
            --  and we print 7 in case of short float.
            Aft  =>
              (case K is
                 when Float_32_K => 7,
                 when Float_64_K => 10,
                 when Extended_K => 10),
            Exp  => 1);
      end if;
      return Trim (Source => Result, Side => Both);
   end Print_Float;

   ------------------------
   -- Print_Record_Value --
   ------------------------

   function Print_Record_Value (Value : Value_Type) return Value_And_Attributes
   is
      package Component_To_Value_Maps is new
        Ada.Containers.Hashed_Maps
          (Key_Type        => Entity_Id,
           Element_Type    => Value_And_Attributes,
           Hash            => Node_Hash,
           Equivalent_Keys => "=");

      Ada_Type                 : constant Entity_Id := Value.AST_Ty;
      Visibility_Map           : Component_Visibility_Maps.Map :=
        Get_Component_Visibility_Map (Ada_Type);
      Fields_Discrs_With_Value : Natural := 0;
      Ordered_Values           : Ordered_Sloc_Maps.Map;
      --  Ordered map containing the values for the components of
      --  the record. They are ordered in as in the source file,
      --  inherited components coming first.
      Ordered_Attributes       : Ordered_Sloc_Attribute_Map;
      --  Ordered map containing the *direct* attributes of the components
      --  of the record, e.g., whether the component is initialized or not.
      --  The ordering is the same as in Ordered_Values plus ordering by the
      --  attribute. Conversely, nested attributes of the values of components
      --  are stored together with the values of the respective components in
      --  the Ordered_Values map.
      Not_Printed_Values       : Component_To_Value_Maps.Map;
      --  Map from components to values + attributes that is used for
      --  temporarily storing values for components that should be present,
      --  but whose value is not printable, e.g., due to being uninitialized or
      --  invalid. In this case we can choose to output "?" for the value, but
      --  still print the attributes. The choice is made after processing all
      --  components. Hence the need to temporarily store them.

      procedure Store_Value_Of_Component
        (Comp       : Entity_Id;
         Comp_Val   : Value_And_Attributes;
         Sloc       : Component_Loc_Info;
         Visibility : Component_Visibility;
         Add_Prefix : Boolean := True);
      --  Build the pretty value for the value and attributes of the component
      --  and depending on whether the value can be fully printed insert
      --  it either to the Ordered_Values or Not_Printed_Values collection in
      --  the parent scope.
      --
      --  @param Comp The entity of the component to print
      --  @param Comp_Val The pretty-printed value of the current value in the
      --     component.
      --  @param Sloc Source location of the component instance
      --  @param Visibility Visibility of the component in the current context
      --  @param Add_Prefix Control flag to avoid duplicate prefix for elements
      --    that cannot be normally printed, but will be printed either as "?"
      --    or only their attributes will be printed.

      procedure Process_Component
        (Comp     : Entity_Id;
         Comp_Val : Value_And_Attributes;
         Sloc     : Component_Loc_Info);
      --  Go over counterexample values for record fields to fill
      --  the Ordered_Values map. Along the way, remove seen
      --  components from the Visibility_Map so that we can later
      --  check for unseen components.
      --
      --  @param Comp The entity of the component to print
      --  @param Comp_Val The pretty-printed value of the current value in the
      --     component.
      --  @param Sloc Source location of the component instance

      ------------------------------
      -- Store_Value_Of_Component --
      ------------------------------

      procedure Store_Value_Of_Component
        (Comp       : Entity_Id;
         Comp_Val   : Value_And_Attributes;
         Sloc       : Component_Loc_Info;
         Visibility : Component_Visibility;
         Add_Prefix : Boolean := True)
      is
         Comp_Name : constant String := Raw_Source_Name (Comp);
         Orig_Decl : constant Entity_Id := Original_Declaration (Comp);
         Prefix    : constant String :=
           (if Ekind (Comp) /= E_Discriminant and then Visibility = Duplicated
            then Raw_Source_Name (Orig_Decl) & '.'
            else "");
         --  Explanation. It is empty except for duplicated
         --  components where it points to the declaration of the
         --  component.

         To_Display : Boolean := True;

      begin

         if not Component_Is_Removed_In_Type
                  (Ty   => Value.AST_Ty,
                   Comp => Comp,
                   Vals => Value.Record_Fields)
         then

            --  Check if the component has a printable value

            if Comp_Val.Value = Dont_Display then
               To_Display := False;
            end if;

            --  Build the pretty value of the component and attributes

            declare
               Pretty_Val : constant CNT_Unbounded_String :=
                 (if To_Display
                  then
                    Make_CNT_Unbounded_String
                      (Str =>
                         Prefix
                         & Comp_Name
                         & " => "
                         & To_String (Comp_Val.Value.Str),
                       Cnt => Comp_Val.Value.Count,
                       Els =>
                         Prefix_Elements
                           (Comp_Val.Value.Elems, '.' & Prefix & Comp_Name))
                  else Make_CNT_Unbounded_String (Str => "?"));

               Pretty_Val_And_Attrs : constant Value_And_Attributes :=
                 (Value      => Pretty_Val,
                  Attributes =>
                    (if Add_Prefix
                     then
                       Prefix_Names
                         (Elems => Comp_Val.Attributes,
                          Pref  => '.' & Prefix & Comp_Name)
                     else Comp_Val.Attributes));
            begin

               if To_Display then
                  Ordered_Values.Insert (Sloc, Pretty_Val_And_Attrs);

                  Fields_Discrs_With_Value := Fields_Discrs_With_Value + 1;
               else
                  Not_Printed_Values.Insert (Comp, Pretty_Val_And_Attrs);
               end if;
            end;
         end if;

      end Store_Value_Of_Component;

      -----------------------
      -- Process_Component --
      -----------------------

      procedure Process_Component
        (Comp     : Entity_Id;
         Comp_Val : Value_And_Attributes;
         Sloc     : Component_Loc_Info)
      is
         Visibility : Component_Visibility;
      begin
         if not Is_Type (Comp) then
            declare
               Orig_Comp : constant Entity_Id :=
                 Search_Component_In_Type (Ada_Type, Comp);
            begin
               if Present (Orig_Comp) then
                  Visibility := Visibility_Map (Orig_Comp);

                  --  If Comp_Val is not Dont_Display, Comp has been displayed.
                  --  Remove it from the visibility map.

                  if Comp_Val.Value /= Dont_Display then
                     Visibility_Map.Exclude (Orig_Comp);
                  end if;
               else
                  Visibility := Removed;
               end if;
            end;

         --  Type component are not displayed as they stand
         --  for invisible components.

         else
            Visibility := Removed;
         end if;

         if Visibility /= Removed then
            pragma Assert (Comp_Val.Value.Str /= "?");
            Store_Value_Of_Component (Comp, Comp_Val, Sloc, Visibility);
         end if;
      end Process_Component;

      --  Start of processing for Print_Record_Value

   begin
      --  Add the 'Constrained to attributes if present

      if Value.Constrained_Attr.Present then
         declare
            Constr_Val : constant CNT_Unbounded_String :=
              Make_CNT_Unbounded_String
                (Str =>
                   (if Value.Constrained_Attr.Content
                    then "True"
                    else "False"));
         begin
            Add_Attribute
              (Ordered_Attributes,
               Attribute => Constrained,
               Value     => Constr_Val);
         end;
      end if;

      --  Add discriminants to Visibility_Map. Discriminants are
      --  considered to be always visible.

      if Has_Discriminants (Ada_Type) then
         declare
            Discr : Entity_Id := First_Discriminant (Ada_Type);
         begin
            while Present (Discr) loop
               Visibility_Map.Insert (Root_Discriminant (Discr), Regular);
               Next_Discriminant (Discr);
            end loop;
         end;
      end if;

      for C in Value.Record_Fields.Iterate loop
         declare
            use Entity_To_Value_Maps;
            Comp      : Entity_Id renames Key (C);
            Sloc_Comp : constant Component_Loc_Info := Get_Loc_Info (Comp);
         begin

            Process_Component (Comp, Print_Value (Element (C).all), Sloc_Comp);
         end;
      end loop;

      --  Go over the visibility map to see if there are missing
      --  components.

      declare
         Is_Before   : Boolean := False;
         Need_Others : Boolean := False;
         --  True if there are more than one missing value or if
         --  the record contains invisible fields (component of type
         --  kind).

         First_Unseen : Entity_Id := Empty;
         --  First component for which we are missing a value

         Str_Val : Unbounded_String := To_Unbounded_String ("(");
         Count   : Natural := 0;
         Elems   : String_Lists.List;
      begin
         for C in Visibility_Map.Iterate loop
            declare
               Visibility : Component_Visibility renames
                 Component_Visibility_Maps.Element (C);
               Comp       : Entity_Id renames
                 Component_Visibility_Maps.Key (C);
            begin
               if Visibility /= Removed
                 and then
                   not Component_Is_Removed_In_Type
                         (Ty   => Value.AST_Ty,
                          Comp => Comp,
                          Vals => Value.Record_Fields)
               then
                  if Is_Type (Comp) or else Present (First_Unseen) then
                     Need_Others := True;
                     exit;
                  else
                     First_Unseen := Comp;
                  end if;
               end if;
            end;
         end loop;

         --  If there is only one component which does not have a
         --  value, we output directly a ? for its value instead
         --  of introducing a others case.

         if not Need_Others and then Present (First_Unseen) then
            declare
               Position : constant Component_To_Value_Maps.Cursor :=
                 Not_Printed_Values.Find (First_Unseen);
            begin
               if Component_To_Value_Maps.Has_Element (Position) then

                  --  Value and attributes were seen, but discarded initially.
                  --  Print the value now as ? and make sure to avoid double
                  --  prefixing.

                  Store_Value_Of_Component
                    (First_Unseen,
                     Not_Printed_Values (Position),
                     Get_Loc_Info (First_Unseen),
                     Visibility_Map.Element (First_Unseen),
                     Add_Prefix => False);

               elsif Fields_Discrs_With_Value > 0 then

                  --  Value for this component was not seen, but there exists
                  --  at least one other printed component. So, output ? for
                  --  this missing one. Otherwise, if there wouldn't be any
                  --  components with a known value, there is nothing known
                  --  about the whole record and it wouldn't be useful to
                  --  output anything.

                  Store_Value_Of_Component
                    (First_Unseen,
                     (Value      => Make_CNT_Unbounded_String (Str => "?"),
                      Attributes => CNT_Attribute_Lists.Empty_List),
                     Get_Loc_Info (First_Unseen),
                     Visibility_Map.Element (First_Unseen));
               end if;
            end;
         end if;

         --  If there are no fields and discriminants of the processed
         --  value with values that can be displayed, do not display
         --  the value (this can happen if there were collected
         --  fields or discriminants, but their values should not
         --  be displayed).

         if Fields_Discrs_With_Value = 0 then

            --  Collect any attributes from non-printed fields. Especially the
            --  'Initialized and 'Valid attributes are likely to be useful in
            --  this case as one of them is likely to be False.

            for Position in Not_Printed_Values.Iterate loop
               for Pretty_Attribute of Not_Printed_Values (Position).Attributes
               loop
                  Add_Attribute
                    (Ordered_Attributes,
                     Pretty_Attribute => Pretty_Attribute,
                     Sloc             =>
                       Get_Loc_Info (Component_To_Value_Maps.Key (Position)));
               end loop;
            end loop;

            return
              (Value      => Dont_Display,
               Attributes => To_List (Ordered_Attributes));
         end if;

         --  Construct the counterexample value by appending the
         --  components in the right order.

         for V of Ordered_Values loop
            Append (Str_Val, (if Is_Before then ", " else "") & V.Value.Str);
            Is_Before := True;
            Count := Count + V.Value.Count;
            Elems.Splice
              (Before => String_Lists.No_Element, Source => V.Value.Elems);
         end loop;

         --  If there are more than one fields that are not
         --  mentioned in the counterexample, summarize them using
         --  the field others.

         if Need_Others then
            Append (Str_Val, (if Is_Before then ", " else "") & "others => ?");
            Count := Count + 1;
         end if;
         Append (Str_Val, ')');

         return Res : Value_And_Attributes do

            --  Values of the record components

            Res.Value :=
              Make_CNT_Unbounded_String
                (Str => To_String (Str_Val), Cnt => Count, Els => Elems);

            --  Attributes of the record as a whole

            Res.Attributes := To_List (Ordered_Attributes);

            --  Attributes of the record components

            Attributes_To_List (Res.Attributes, Ordered_Values);
         end return;
      end;
   end Print_Record_Value;

   ------------------
   -- Print_Scalar --
   ------------------

   function Print_Scalar
     (Value : Scalar_Value_Type; AST_Type : Entity_Id)
      return CNT_Unbounded_String
   is
      function To_String (Value : Scalar_Value_Type) return String;
      --  Turn Value into a string

      ---------------
      -- To_String --
      ---------------

      function To_String (Value : Scalar_Value_Type) return String is
      begin
         case Value.K is
            when Integer_K =>

               declare
                  --  Decision: generic values for Bound_Type and Bound_Value
                  --  are random for now. They can be adjusted in the future.

                  function Pretty_Print is new
                    Print_Discrete (Bound_Type => 10, Bound_Value => 5);
               begin
                  return Pretty_Print (Value.Integer_Content, AST_Type);
               end;

            when Char_K    =>

               --  Determine the underlying character and print it
               --  to a human-readable form. The printing is using a
               --  custom translation that is currently defined for
               --  the Latin-1 character range (0 .. 255).

               --  Note: As we are using a custom printing routine
               --  there is no need to go through the decoding
               --  provided by the 'Namet' package. Using the
               --  character code directly is sufficient and more
               --  efficient.

               declare
                  CC : constant Char_Code :=
                    UI_To_CC (Char_Literal_Value (Value.Char_Node));
                  C  : Character;
               begin
                  if In_Character_Range (CC) then
                     C := Get_Character (CC);
                     return ''' & Char_To_String_Representation (C) & ''';
                  else
                     RAC_Stuck ("Character value outside the Latin-1 range");
                  end if;
               end;

            when Enum_K    =>

               pragma
                 Assert
                   (Is_Enumeration_Type (AST_Type)
                    and then not Is_Character_Type (AST_Type));

               --  Necessary for some types that makes boolean be translated to
               --  integers like: "subype only_true := True .. True".

               if Is_Boolean_Type (AST_Type) then
                  if Value.Enum_Entity = Boolean_Literals (True) then
                     return "True";
                  else
                     return "False";
                  end if;

               else
                  --  Call Get_Enum_Lit_From_Pos to get a corresponding
                  --  enumeration entity, then Raw_Source_Name to get a
                  --  correctly capitalized enumeration value.

                  return Raw_Source_Name (Value.Enum_Entity);
               end if;

            when Fixed_K   =>
               return Print_Fixed (Value.Small, Value.Fixed_Content);

            when Float_K   =>
               case Value.Float_Content.K is
                  when Float_32_K =>
                     declare
                        function Print is new
                          Print_Float (Float, Value.Float_Content.K);
                     begin
                        return Print (Value.Float_Content.Content_32);
                     end;

                  when Float_64_K =>
                     declare
                        function Print is new
                          Print_Float (Long_Float, Value.Float_Content.K);
                     begin
                        return Print (Value.Float_Content.Content_64);
                     end;

                  when Extended_K =>
                     declare
                        function Print is new
                          Print_Float (Long_Long_Float, Value.Float_Content.K);
                     begin
                        return Print (Value.Float_Content.Ext_Content);
                     end;
               end case;
         end case;
      end To_String;

      --  Start of processing for Print_Scalar_Value

   begin
      declare
         Result : constant String := To_String (Value);
      begin
         return Make_CNT_Unbounded_String (Str => Trim (Result, Both));
      end;
   exception
      when Parse_Error =>
         return Dont_Display;
   end Print_Scalar;

   -----------------
   -- Print_Value --
   -----------------

   function Print_Value (Value : Value_Type) return Value_And_Attributes is
   begin
      case Value.K is
         when Scalar_K   =>

            --  Don't display uninitialized or invalid values

            declare
               Attributes : CNT_Attribute_List;
            begin
               if Value.Initialized_Attr.Present then
                  declare
                     Init_Val : constant CNT_Unbounded_String :=
                       Make_CNT_Unbounded_String
                         (Str =>
                            (if Value.Initialized_Attr.Content
                             then "True"
                             else "False"));
                  begin
                     Attributes.Append
                       (Make_CNT_Attribute (Initialized, Init_Val));
                  end;
               end if;

               if Value.Valid_Attr.Present then
                  declare
                     Valid_Val : constant CNT_Unbounded_String :=
                       Make_CNT_Unbounded_String
                         (Str =>
                            (if Value.Valid_Attr.Content
                             then "True"
                             else "False"));
                  begin
                     Attributes.Append (Make_CNT_Attribute (Valid, Valid_Val));
                  end;
               end if;

               --  Don't display scalar values if 'Initialized or 'Valid is
               --  False.

               if Value.Scalar_Content = null
                 or else
                   (Value.Initialized_Attr.Present
                    and then not Value.Initialized_Attr.Content)
                 or else
                   (Value.Valid_Attr.Present
                    and then not Value.Valid_Attr.Content)
               then
                  return (Value => Dont_Display, Attributes => Attributes);
               else
                  return
                    (Value      =>
                       Print_Scalar (Value.Scalar_Content.all, Value.AST_Ty),
                     Attributes => Attributes);
               end if;
            end;

         when Record_K   =>
            return Print_Record_Value (Value);

         when Multidim_K =>

            --  Add the bounds to Attributes

            declare
               Attributes : CNT_Attribute_List;
            begin
               for I in Value.Bounds.Content'Range loop
                  if Value.Bounds.Content (I).First.Present then
                     declare
                        Bound_Val : constant CNT_Unbounded_String :=
                          Make_CNT_Unbounded_String
                            (Str =>
                               (Trim
                                  (To_String
                                     (Value.Bounds.Content (I).First.Content),
                                   Left)));
                     begin
                        Attributes.Append
                          (Make_CNT_Attribute
                             (First,
                              Bound_Val,
                              " (" & Trim (I'Image, Left) & ')'));
                     end;
                  end if;
                  if Value.Bounds.Content (I).Last.Present then
                     declare
                        Bound_Val : constant CNT_Unbounded_String :=
                          Make_CNT_Unbounded_String
                            (Str =>
                               Trim
                                 (To_String
                                    (Value.Bounds.Content (I).Last.Content),
                                  Left));
                     begin
                        Attributes.Append
                          (Make_CNT_Attribute
                             (Last,
                              Bound_Val,
                              " (" & Trim (I'Image, Left) & ')'));
                     end;
                  end if;
               end loop;

               --  Return Dont_Display

               return (Value => Dont_Display, Attributes => Attributes);
            end;

         when Array_K    =>
            return Print_Array_Value (Value);

         when Access_K   =>
            return Print_Access_Value (Value);
      end case;
   end Print_Value;

   function Print_Value (Value : Value_Type) return CNT_Unbounded_String is
      Val_And_Attrs : constant Value_And_Attributes := Print_Value (Value);
   begin
      return Val_And_Attrs.Value;
   end Print_Value;

   --------------------------------
   -- Print_Value_And_Attributes --
   --------------------------------

   procedure Print_Value_And_Attributes
     (Name           : Unbounded_String;
      Value          : Value_Type;
      Pretty_Line    : in out Cntexample_Elt_Lists.List;
      Is_Json_Format : Boolean := False) is
   begin
      if Is_Json_Format then
         declare
            JSON_Obj : constant GNATCOLL.JSON.JSON_Value :=
              Serialize_Value (Value);
         begin
            Pretty_Line.Append
              (Cntexample_Elt'
                 (K        => Json_Format,
                  Kind     => CEE_Variable,
                  Name     => Name,
                  JSON_Obj => JSON_Obj));
         end;
      else
         declare
            Val_And_Attrs : constant Value_And_Attributes :=
              Print_Value (Value);
         begin
            --  Append the pretty printed value of Value
            if Val_And_Attrs.Value /= Dont_Display then
               Pretty_Line.Append
                 (Cntexample_Elt'
                    (K       => Pretty_Printed,
                     Kind    => CEE_Variable,
                     Name    => Name,
                     Val_Str => Val_And_Attrs.Value));
            end if;

            --  Add the attributes

            declare
               Val_Attrs : constant CNT_Attribute_List :=
                 Prefix_Names (Val_And_Attrs.Attributes, To_String (Name));
            begin
               for Name_And_Value of Val_Attrs loop
                  Pretty_Line.Append
                    (Cntexample_Elt'
                       (K       => Pretty_Printed,
                        Kind    => CEE_Variable,
                        Name    => Name_And_Value.Name,
                        Val_Str => Name_And_Value.Value));
               end loop;
            end;
         end;
      end if;
   end Print_Value_And_Attributes;

   ---------------------
   -- Serialize_Float --
   ---------------------

   function Serialize_Float
     (F : CE_Values.Float_Value) return GNATCOLL.JSON.JSON_Value
   is
      use GNATCOLL.JSON;
      JSON_Obj : constant GNATCOLL.JSON.JSON_Value := Create_Object;
   begin
      Set_Field (JSON_Obj, "quotient", False);
      case F.K is
         when Float_32_K =>
            declare
               Content_32 : constant Float := F.Content_32;
               F_Str      : String (1 .. Float'Digits * 3);
            begin
               Ada.Float_Text_IO.Put
                 (To   => F_Str,
                  Item => Content_32,
                  Aft  => Float'Digits,
                  Exp  => 1);
               Set_Field
                 (JSON_Obj, "value", Create (Trim (F_Str, Ada.Strings.Left)));
            end;

         when Float_64_K =>
            declare
               Content_64 : constant Long_Float := F.Content_64;
               F_Str      : String (1 .. Long_Float'Digits * 3);
            begin
               Ada.Long_Float_Text_IO.Put
                 (To   => F_Str,
                  Item => Content_64,
                  Aft  => Long_Float'Digits,
                  Exp  => 1);
               Set_Field
                 (JSON_Obj, "value", Create (Trim (F_Str, Ada.Strings.Left)));
            end;

         when others     =>
            declare
               Ext_Content : constant Long_Long_Float := F.Ext_Content;
               F_Str       : String (1 .. Long_Long_Float'Digits * 3);
            begin
               Ada.Long_Long_Float_Text_IO.Put
                 (To   => F_Str,
                  Item => Ext_Content,
                  Aft  => Long_Long_Float'Digits,
                  Exp  => 1);
               Set_Field
                 (JSON_Obj, "value", Create (Trim (F_Str, Ada.Strings.Left)));
            end;
      end case;
      return JSON_Obj;
   end Serialize_Float;

   ---------------------
   -- Serialize_Value --
   ---------------------

   function Serialize_Value
     (Value : CE_Values.Value_Type) return GNATCOLL.JSON.JSON_Value
   is
      use GNATCOLL.JSON;
      JSON_Obj : GNATCOLL.JSON.JSON_Value := Create_Object;
   begin
      case Value.K is
         when Scalar_K   =>
            if Value.Scalar_Content /= null then
               case Value.Scalar_Content.K is
                  when Integer_K =>
                     JSON_Obj :=
                       Create
                         (Trim
                            (To_String (Value.Scalar_Content.Integer_Content),
                             Ada.Strings.Left));

                  when Float_K   =>
                     JSON_Obj :=
                       Serialize_Float (Value.Scalar_Content.Float_Content);

                  when Fixed_K   =>
                     Set_Field
                       (JSON_Obj,
                        "value",
                        Create
                          (Print_Fixed
                             (Value.Scalar_Content.Small,
                              Value.Scalar_Content.Fixed_Content,
                              True)));
                     Set_Field (JSON_Obj, "quotient", True);

                  when Char_K    =>

                     declare
                        Value_As_String : constant String := To_String (Value);
                     begin

                        --  The direct conversion to String should always yield
                        --  1 character. Unlike pretty-printing where
                        --  non-printable or non-ASCII characters are
                        --  represented with longer strings.

                        pragma Assert (Value_As_String'Length = 1);

                        --  The JSON constructor expects UTF-8 strings. The
                        --  characters in CE-s are Latin-1, so a conversion
                        --  is needed.

                        JSON_Obj := Create (Encode (Value_As_String));
                     end;

                  when Enum_K    =>
                     JSON_Obj := Create (To_String (Value));
               end case;
            end if;

         when Record_K   =>
            declare
               Components    : constant GNATCOLL.JSON.JSON_Value :=
                 Create_Object;
               Discriminants : constant GNATCOLL.JSON.JSON_Value :=
                 Create_Object;
            begin
               for Elt in Value.Record_Fields.Iterate loop
                  declare
                     use Entity_To_Value_Maps;
                     Name : constant String := Raw_Source_Name (Key (Elt));
                  begin
                     case Ekind (Key (Elt)) is
                        when E_Discriminant =>
                           Set_Field
                             (Discriminants,
                              Name,
                              Serialize_Value (Value.Record_Fields (Elt).all));

                        when others         =>
                           Set_Field
                             (Components,
                              Name,
                              Serialize_Value (Value.Record_Fields (Elt).all));
                     end case;
                  end;
               end loop;
               Set_Field (JSON_Obj, "discriminants", Discriminants);
               Set_Field (JSON_Obj, "components", Components);
            end;

         when Array_K    =>
            if Value.First_Attr.Present and Value.Last_Attr.Present then
               declare
                  Aggregate  : constant GNATCOLL.JSON.JSON_Value :=
                    Create_Object;
                  Min        : constant Valid_Big_Integer :=
                    Value.First_Attr.Content;
                  Max        : constant Valid_Big_Integer :=
                    Value.Last_Attr.Content;
                  Size       : constant Valid_Big_Integer := Max - Min + 1;
                  Sizes      : GNATCOLL.JSON.JSON_Array := Empty_Array;
                  Dimension  : constant GNATCOLL.JSON.JSON_Value :=
                    Create_Object;
                  Dimensions : GNATCOLL.JSON.JSON_Array := Empty_Array;
               begin

                  Append
                    (Sizes,
                     Create (Trim (To_String (Size), Ada.Strings.Left)));
                  Set_Field (JSON_Obj, "sizes", Sizes);

                  Set_Field
                    (Dimension,
                     "First",
                     (Trim (To_String (Min), Ada.Strings.Left)));
                  Set_Field
                    (Dimension,
                     "Last",
                     (Trim (To_String (Max), Ada.Strings.Left)));
                  Append (Dimensions, Dimension);
                  Set_Field (JSON_Obj, "dimensions", Dimensions);

                  if Size >= 0 then
                     for Elt in Value.Array_Values.Iterate loop
                        declare
                           use Big_Integer_To_Value_Maps;
                        begin
                           Set_Field
                             (Aggregate,
                              Trim (To_String (Key (Elt)), Ada.Strings.Left),
                              Serialize_Value (Element (Elt).all));
                        end;
                     end loop;
                     if Value.Array_Others /= null then
                        Set_Field
                          (Aggregate,
                           "others",
                           Serialize_Value (Value.Array_Others.all));
                     end if;
                  end if;
                  Set_Field (JSON_Obj, "aggregate", Aggregate);
               end;
            end if;

         when Multidim_K =>
            JSON_Obj := Create (Value.Bounds'Image);

         when Access_K   =>
            if Value.Is_Null.Present
              and then not Value.Is_Null.Content
              and then Value.Designated_Value /= null
            then
               --  wrap the pointed object into a single field to differentiate
               --  it from non-access values
               Set_Field
                 (JSON_Obj,
                  "designated value",
                  Serialize_Value (Value.Designated_Value.all));
            end if;
      end case;
      return JSON_Obj;
   end Serialize_Value;

end CE_Pretty_Printing;
