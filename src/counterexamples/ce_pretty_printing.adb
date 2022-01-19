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

with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Ordered_Maps;
with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;
with Ada.Strings;              use Ada.Strings;
with Ada.Strings.Fixed;        use Ada.Strings.Fixed;
with Ada.Text_IO;
with Casing;                   use Casing;
with CE_Utils;                 use CE_Utils;
with Gnat2Why_Args;
with Gnat2Why.Tables;          use Gnat2Why.Tables;
with Namet;                    use Namet;
with SPARK_Atree;              use SPARK_Atree;
with SPARK_Atree.Entities;     use SPARK_Atree.Entities;
with SPARK_Util;               use SPARK_Util;
with SPARK_Util.Types;         use SPARK_Util.Types;
with Stand;                    use Stand;
with Types;                    use Types;
with Uintp;                    use Uintp;

package body CE_Pretty_Printing is

   ---------------------------------
   -- Types and Generic Instances --
   ---------------------------------

   type Component_Loc_Info is record
      Type_Ent : Entity_Id;
      Sloc     : Source_Ptr;
   end record;
   --  A location information for a component contains the type in which the
   --  component is declared first and the location of this first declaration.

   function Get_Loc_Info (Comp : Entity_Id) return Component_Loc_Info is
     ((Type_Ent => Original_Declaration (Comp),
       Sloc     =>
          Sloc
            (Search_Component_In_Type (Original_Declaration (Comp), Comp))));
   --  Construct the location information of a record component or
   --  discriminant.

   function "<" (X, Y : Component_Loc_Info) return Boolean is
     ((X.Type_Ent /= Y.Type_Ent and then Is_Ancestor (X.Type_Ent, Y.Type_Ent))
      or else (X.Type_Ent = Y.Type_Ent and then X.Sloc <= Y.Sloc));
   --  Order on location information. A component F1 is declared first than
   --  another F2 if F1 is declared in an ancestor of the type in which F2 is
   --  declared, or if they are declared in the same type and F1 occurs before
   --  in the source code.

   package Ordered_Sloc_Map is new Ada.Containers.Ordered_Maps
     (Key_Type     => Component_Loc_Info,
      Element_Type => CNT_Unbounded_String,
      "<"          => "<");
   --  Map from sloc to strings, used to output component of record values in
   --  correct order.

   type Pair_Name_Value is record
      Name  : Unbounded_String;
      Value : CNT_Unbounded_String;
   end record;
   --  Attributes are printed as a list of a name and a value

   package Name_Value_Lists is new
     Ada.Containers.Doubly_Linked_Lists
       (Element_Type => Pair_Name_Value,
        "="          => "=");

   type Value_And_Attributes is record
      Value      : CNT_Unbounded_String;
      Attributes : Name_Value_Lists.List;
   end record;
   --  Return type of the internal printing functions. It contains a string for
   --  the value parsed and a list of associations for its attributes.

   -----------------------
   -- Local_Subprograms --
   -----------------------

   function Prefix_Names
     (Elems : Name_Value_Lists.List;
      Pref  : String) return Name_Value_Lists.List;
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

   function Print_Record_Value (Value : Value_Type) return Value_And_Attributes
     with Pre => Value.K = Record_K;
   --  Print value of a record type in an aggregate like syntax. Hidden
   --  components are prefixed by the name of their enclosing type Ty.F => V.

   function Print_Scalar
     (Value    : Scalar_Value_Type;
      AST_Type : Entity_Id) return CNT_Unbounded_String;
   --  Print a scalar counterexample value. The type is used to correctly print
   --  an Integer as a Character type for example.

   function Print_Value (Value : Value_Type) return Value_And_Attributes;
   --  Print a counterexample value

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

   ------------------
   -- Prefix_Names --
   ------------------

   function Prefix_Names
     (Elems : Name_Value_Lists.List;
      Pref  : String) return Name_Value_Lists.List
   is
      Res : Name_Value_Lists.List := Elems;
   begin
      for E of Res loop
         E.Name := Pref & E.Name;
      end loop;
      return Res;
   end Prefix_Names;

   -------------------------
   -- Print_Access_Value --
   -------------------------

   function Print_Access_Value
     (Value : Value_Type) return Value_And_Attributes
   is
      Res : Value_And_Attributes;

   begin
      if Value.Is_Null.Present and then Value.Is_Null.Content then
         Res.Value :=
           Make_CNT_Unbounded_String
             (Nul => False, Str => To_Unbounded_String ("null"));

      elsif Value.Designated_Value = null then
         Res.Value := Dont_Display;

      --  Reconstruct the value

      else
         declare
            V      : constant Value_And_Attributes :=
              Print_Value (Value.Designated_Value.all);
            Elems  : S_String_List.List;
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
                   (Nul => V.Value.Nul,
                    Str => "new " & Source_Name (Des_Ty)
                      & "'(" & V.Value.Str & ")",
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

      package Sorted_Array is new Ada.Containers.Ordered_Maps
        (Key_Type     => Big_Integer,
         Element_Type => Array_Elem,
         "<"          => "<");

      procedure Add_Index
        (S_Array    : in out Sorted_Array.Map;
         Nul        : in out Boolean;
         Attributes : in out Name_Value_Lists.List;
         String_Lit : in out Boolean;
         Index      : Big_Integer;
         Index_Type : Entity_Id;
         Element    : Value_And_Attributes);
      --  Add a mapping for Index => Element in S_Array if Index corresponds
      --  to a valid value of type Index_Type and both Index and Element
      --  can be printed.

      function Is_Normal_Char (S : Unbounded_String) return Boolean is
        (Length (S) = 3)
      with Pre => Length (S) >= 3
          and then Element (S, 1) = '''
          and then Element (S, Length (S)) = ''';
      --  Return True if S is the representation of a normal character

      function Max_Exp_Others (String_Lit : Boolean) return Big_Natural is
        (if String_Lit then Big_Natural'(15) else Big_Natural'(1));
      --  Maximal number of elements for which the others value can be
      --  expanded.
      --  Decision: Only explicitly expand the others choice if it is less
      --  than 15 values for strings and 1 values for other arrays.

      function Parse_And_Print_Index
        (Index      : Big_Integer;
         Index_Type : Entity_Id) return CNT_Unbounded_String;
      --  Use the parsing and pretty printing of scalars to transform an index
      --  value as a big integer into an appropriate string representation.

      procedure Print_Elements
        (Value      : Value_Type;
         S_Array    : out Sorted_Array.Map;
         Nul        : in out Boolean;
         Complete   : out Boolean;
         String_Lit : out Boolean;
         Others_Val : out CNT_Unbounded_String;
         Attributes : out Name_Value_Lists.List);
      --  Check and export all parts of Value in an appropriate format.
      --  Individual elements are stored in S_Array, Complete is set
      --  to True iff all the elements of the array have a mapping in S_Array,
      --  and the default value for the array is stored in Others_Val if
      --  Complete is False. Nul is set to True iff all the elements of
      --  S_Array are known to be nul. String_Lit is set to False iff all the
      --  elements of S_Array are normal characters. Attributes contains the
      --  set of attributes of Value.

      ---------------
      -- Add_Index --
      ---------------

      procedure Add_Index
        (S_Array    : in out Sorted_Array.Map;
         Nul        : in out Boolean;
         Attributes : in out Name_Value_Lists.List;
         String_Lit : in out Boolean;
         Index      : Big_Integer;
         Index_Type : Entity_Id;
         Element    : Value_And_Attributes)
      is
         Ind_Printed : constant CNT_Unbounded_String :=
           Parse_And_Print_Index (Index, Index_Type);

      begin
         if Ind_Printed /= Dont_Display then
            if Element.Value /= Dont_Display then
               Nul := Nul and then Element.Value.Nul;
               S_Array.Include (Key       => Index,
                                New_Item  =>
                                  (Ind_Printed  => Ind_Printed,
                                   Elem_Printed => Element.Value));
               String_Lit := String_Lit
                 and then Is_Normal_Char (Element.Value.Str);
            end if;

            --  Store the attributes with their values

            declare
               Elmt_Attr : Name_Value_Lists.List :=
                 Prefix_Names
                   (Element.Attributes,
                    " (" & To_String (Ind_Printed.Str) & ")");
            begin
               Attributes.Splice (Name_Value_Lists.No_Element, Elmt_Attr);
            end;
         end if;
      end Add_Index;

      ---------------------------
      -- Parse_And_Print_Index --
      ---------------------------

      function Parse_And_Print_Index
        (Index      : Big_Integer;
         Index_Type : Entity_Id) return CNT_Unbounded_String
      is
         Value : Scalar_Value_Type;
      begin
         Value := Parse_Scalar_Value
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
        (Value      : Value_Type;
         S_Array    : out Sorted_Array.Map;
         Nul        : in out Boolean;
         Complete   : out Boolean;
         String_Lit : out Boolean;
         Others_Val : out CNT_Unbounded_String;
         Attributes : out Name_Value_Lists.List)
      is
         Fst_Index   : constant Node_Id := First_Index (Value.AST_Ty);
         Index_Type  : constant Entity_Id := Retysp (Etype (Fst_Index));

         Others_Elem : Value_And_Attributes;

         Attr_First  : Opt_Big_Integer := Value.First_Attr;
         Attr_Last   : Opt_Big_Integer := Value.Last_Attr;
         U_Fst       : Uint;
         U_Lst       : Uint;
         First       : Big_Integer;
         Last        : Big_Integer;

      begin
         --  Use static array type bounds or index type bounds as default

         Find_First_Static_Range (Fst_Index, U_Fst, U_Lst);
         First := From_String (UI_Image (U_Fst, Decimal));
         Last := From_String (UI_Image (U_Lst, Decimal));

         --  Update bounds from the attribute values if any. We ignore out of
         --  bound values.

         if Attr_First.Present and then Attr_First.Content >= First then
            First := Attr_First.Content;
         else
            Attr_First := (Present => False);
         end if;

         if Attr_Last.Present and then Attr_Last.Content <= Last then
            Last := Attr_Last.Content;
         else
            Attr_Last := (Present => False);
         end if;

         --  Add the first and last attributes if any

         Attributes.Clear;

         if Attr_First.Present then
            declare
               First_Str : constant CNT_Unbounded_String :=
                 Parse_And_Print_Index
                   (Attr_First.Content, Base_Type (Index_Type));
            begin
               if First_Str = Dont_Display then
                  Attr_First := (Present => False);
               else
                  Attributes.Append
                    ((To_Unbounded_String ("'First"), First_Str));
               end if;
            end;
         end if;
         if Attr_Last.Present then
            declare
               Last_Str : constant CNT_Unbounded_String :=
                 Parse_And_Print_Index
                   (Attr_Last.Content, Base_Type (Index_Type));
            begin
               if Last_Str = Dont_Display then
                  Attr_Last := (Present => False);
               else
                  Attributes.Append
                    ((To_Unbounded_String ("'Last"), Last_Str));
               end if;
            end;
         end if;

         --  Format the others choice if any

         Complete := False;

         if Value.Array_Others /= null then
            Others_Elem := Print_Value (Value.Array_Others.all);
         else
            Others_Elem.Value := Dont_Display;
         end if;

         String_Lit := Is_String_Type (Value.AST_Ty);

         for C in Value.Array_Values.Iterate loop

            --  Reorder the elements inside S_Array

            declare
               Index        : Big_Integer renames
                 Big_Integer_To_Value_Maps.Key (C);
               Elem         : Value_Access renames Value.Array_Values (C);

               Elem_Printed : constant Value_And_Attributes :=
                 Print_Value (Elem.all);
            begin
               if First <= Index and then Index <= Last then
                  Add_Index
                    (S_Array, Nul, Attributes, String_Lit,
                     Index, Index_Type, Elem_Printed);
               end if;
            end;
         end loop;

         --  No need for "others" if the array is empty or indexes already
         --  cover the full range.

         if To_Big_Integer (Integer (S_Array.Length)) >= Last - First + 1 then
            Complete := True;

         --  Replace "others" by the actual indexes if we are missing less
         --  than Max_Exp_Others values, the bounds are known, and Others_Val
         --  is supplied.

         elsif Others_Elem.Value /= Dont_Display
           and then  To_Big_Integer (Integer (S_Array.Length)) >=
             Last - First + 1 -
             Max_Exp_Others (String_Lit => String_Lit
                               and then Is_Normal_Char (Others_Elem.Value.Str))
           and then ((Attr_First.Present and then Attr_Last.Present)
                     or else Is_Static_Array_Type (Value.AST_Ty))
         then
            declare
               Index : Big_Integer := First;
            begin
               while Index <= Last loop
                  if not S_Array.Contains (Index) then
                     Add_Index
                       (S_Array, Nul, Attributes, String_Lit,
                        Index, Index_Type, Others_Elem);
                  end if;
                  Index := Index + 1;
               end loop;
            end;
            pragma Assert
              (To_Big_Integer (Integer (S_Array.Length)) = Last - First + 1);
            Complete := True;

         else
            --  DECISION: We discard the attributes on the others choice

            Others_Val := Others_Elem.Value;
         end if;
      end Print_Elements;

      --  Local variables

      S          : Unbounded_String;
      Nul        : Boolean := True;
      S_Array    : Sorted_Array.Map;
      Others_Val : CNT_Unbounded_String;
      Complete   : Boolean;
      String_Lit : Boolean;
      Count      : Natural := 0;
      Elems      : S_String_List.List;
      Res        : Value_And_Attributes;

      use S_String_List;

   --  Start of processing for Print_Array_Value

   begin
      Print_Elements
        (Value, S_Array, Nul, Complete,
         String_Lit, Others_Val, Res.Attributes);

      --  Print complete strings containing only normal characters as string
      --  literals.

      if String_Lit and then Complete then
         for C of S_Array loop
            S := S & Element (C.Elem_Printed.Str, 2);
         end loop;

         if S = "" then
            Res.Value := Dont_Display;
         else
            Res.Value := Make_CNT_Unbounded_String
              (Nul => Nul,
               Str => '"' & S & '"');
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
               C_Elems      : S_String_List.List :=
                 Prefix_Elements (Elem_Printed.Elems,
                                  To_String ('(' & Ind_Printed.Str & ')'));
            begin
               if S /= "" then
                  Append (S, ", ");
               end if;

               pragma Assert (Elem_Printed /= Dont_Display);

               Count := Count + Elem_Printed.Count;
               Append (S, Ind_Printed.Str & " => " & Elem_Printed.Str);

               Elems.Splice (Before => No_Element,
                             Source => C_Elems);
            end;
         end loop;

         --  Is the aggregate is not complete, add an association for its
         --  others case. Don't add it if the others case is unknown and there
         --  are no specific cases.

         if not Complete
           and then (S /= "" or else Others_Val /= Dont_Display)
         then
            Nul := Nul and then Others_Val.Nul;

            if S /= "" then
               Append (S, ", ");
            end if;

            --  When Others_Val is Dont_Display, still add an association to ?

            if Others_Val = Dont_Display then
               Count := Count + 1;
               Append (S, "others => ?");
            else
               Append (S, "others => " & Others_Val.Str);
               Count := Count + Others_Val.Count;
               --  Do not insert a value for "others" in Elems
            end if;
         end if;

         if S = "" then
            Res.Value := Dont_Display;
         else
            Res.Value := Make_CNT_Unbounded_String
              (Nul => Nul,
               Str => "(" & S & ")",
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
   -- Print_Record_Value --
   ------------------------

   function Print_Record_Value (Value : Value_Type) return Value_And_Attributes
   is
      Ada_Type                 : constant Entity_Id := Value.AST_Ty;
      Visibility_Map           : Component_Visibility_Maps.Map :=
        Get_Component_Visibility_Map (Ada_Type);
      Fields_Discrs_With_Value : Natural := 0;
      Attributes               : Name_Value_Lists.List;
      Ordered_Values           : Ordered_Sloc_Map.Map;
      --  Ordered map containing the values for the components of
      --  the record. They are ordered in as in the source file,
      --  inherited components coming first.

      procedure Get_Value_Of_Component
        (Comp       : Node_Id;
         Val        : Value_And_Attributes;
         Visibility : Component_Visibility);
      --  Insert value of record component or dicriminant in
      --  Ordered_Values and its attributes in Attributes.

      procedure Process_Component
        (Comp     : Entity_Id;
         Comp_Val : Value_And_Attributes);
      --  Go over counterexample values for record fields to fill
      --  the Ordered_Values map. Along the way, remove seen
      --  components from the Visibility_Map so that we can later
      --  check for unseen components.

      ----------------------------
      -- Get_Value_Of_Component --
      ----------------------------

      procedure Get_Value_Of_Component
        (Comp       : Node_Id;
         Val        : Value_And_Attributes;
         Visibility : Component_Visibility)
      is
         Comp_Name : constant String := Source_Name (Comp);
         Orig_Decl : constant Entity_Id := Original_Declaration (Comp);
         Prefix    : constant String :=
           (if Ekind (Comp) /= E_Discriminant
              and then Visibility = Duplicated
            then Source_Name (Orig_Decl) & "."
            else "");
         --  Explanation. It is empty except for duplicated
         --  components where it points to the declaration of the
         --  component.

      begin
         --  Add the value of the component to Ordered_Values

         if Val.Value /= Dont_Display then
            Ordered_Values.Insert
              (Get_Loc_Info (Comp),
               Make_CNT_Unbounded_String
                 (Nul => Val.Value.Nul,
                  Str => Prefix & Comp_Name & " => " & Val.Value.Str,
                  Cnt => Val.Value.Count,
                  Els =>
                    Prefix_Elements
                      (Val.Value.Elems, '.' & Prefix & Comp_Name)));
            Fields_Discrs_With_Value := Fields_Discrs_With_Value + 1;
         end if;

         --  Add the attributes of the component to Attributes

         declare
            Comp_Attrs : Name_Value_Lists.List :=
              Prefix_Names (Val.Attributes, '.' & Prefix & Comp_Name);
         begin
            Attributes.Splice (Name_Value_Lists.No_Element, Comp_Attrs);
         end;
      end Get_Value_Of_Component;

      -----------------------
      -- Process_Component --
      -----------------------

      procedure Process_Component
        (Comp     : Entity_Id;
         Comp_Val : Value_And_Attributes)
      is
         Visibility : Component_Visibility;
      begin
         if not Is_Type (Comp) then
            declare
               Orig_Comp : constant Entity_Id :=
                 Search_Component_In_Type
                   (Ada_Type, Comp);
            begin
               Visibility := Visibility_Map (Orig_Comp);

               --  If Comp_Val is not Dont_Display, Comp has been displayed.
               --  Remove it from the visibility map.

               if Comp_Val.Value /= Dont_Display then
                  Visibility_Map.Exclude (Orig_Comp);
               end if;
            end;

         --  Type component are not displayed as they stand
         --  for invisible components.

         else
            Visibility := Removed;
         end if;

         if Visibility /= Removed then
            pragma Assert (Comp_Val.Value.Str /= "?");
            Get_Value_Of_Component (Comp, Comp_Val, Visibility);
         end if;
      end Process_Component;

   --  Start of processing for Print_Record_Value

   begin
      --  Add the 'Constrained to attributes if present

      if Value.Constrained_Attr.Present then
         declare
            Constr_Val : constant CNT_Unbounded_String :=
              Make_CNT_Unbounded_String
                (Nul => False,
                 Str => To_Unbounded_String
                   (if Value.Constrained_Attr.Content then "True"
                    else "False"));
         begin
            Attributes.Append
              ((Name  => To_Unbounded_String ("'Constrained"),
                Value => Constr_Val));
         end;
      end if;

      --  Add discriminants to Visibility_Map. Discriminants are
      --  considered to be always visible.

      if Has_Discriminants (Ada_Type) then
         declare
            Discr : Entity_Id :=
              First_Discriminant (Ada_Type);
         begin
            while Present (Discr) loop
               Visibility_Map.Insert
                 (Root_Discriminant (Discr), Regular);
               Next_Discriminant (Discr);
            end loop;
         end;
      end if;

      for C in Value.Record_Fields.Iterate loop
         declare
            use Entity_To_Value_Maps;
            Comp : Entity_Id renames Key (C);
         begin
            Process_Component (Comp, Print_Value (Element (C).all));
         end;
      end loop;

      --  If there are no fields and discriminants of the processed
      --  value with values that can be displayed, do not display
      --  the value (this can happen if there were collected
      --  fields or discriminants, but their values should not
      --  be displayed).

      if Fields_Discrs_With_Value = 0 then
         return (Value => Dont_Display, Attributes => Attributes);
      end if;

      --  Go over the visibility map to see if there are missing
      --  components.

      declare
         Is_Before    : Boolean := False;
         Need_Others  : Boolean := False;
         --  True if there are more than one missing value or if
         --  the record contains invisible fields (component of type
         --  kind).

         First_Unseen : Entity_Id := Empty;
         --  First component for which we are missing a value

         Nul          : Boolean := True;
         Value        : Unbounded_String := To_Unbounded_String ("(");
         Count        : Natural := 0;
         Elems        : S_String_List.List;
      begin
         for C in Visibility_Map.Iterate loop
            declare
               Visibility : Component_Visibility renames
                 Component_Visibility_Maps.Element (C);
               Comp       : Entity_Id renames
                 Component_Visibility_Maps.Key (C);
            begin
               if Visibility /= Removed then
                  if Is_Type (Comp) or else Present (First_Unseen)
                  then
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
            Get_Value_Of_Component
              (First_Unseen,
               (Value      => Make_CNT_Unbounded_String
                    (Nul => True, Str => To_Unbounded_String ("?")),
                Attributes => Name_Value_Lists.Empty_List),
               Visibility_Map.Element (First_Unseen));
         end if;

         --  Construct the counterexample value by appending the
         --  components in the right order.

         for V of Ordered_Values loop
            Nul := Nul and then V.Nul;
            Append (Value,
                    (if Is_Before then ", " else "") & V.Str);
            Is_Before := True;
            Count := Count + V.Count;
            Elems.Splice (Before => S_String_List.No_Element,
                          Source => V.Elems);
         end loop;

         --  If there are more than one fields that are not
         --  mentioned in the counterexample, summarize them using
         --  the field others.

         if Need_Others then
            Append (Value,
                    (if Is_Before then ", " else "") &
                      "others => ?");
            Count := Count + 1;
         end if;
         Append (Value, ')');

         return (Value      => Make_CNT_Unbounded_String
                 (Nul => Nul,
                  Str => Value,
                  Cnt => Count,
                  Els => Elems),
                 Attributes => Attributes);
      end;
   end Print_Record_Value;

   ------------------
   -- Print_Scalar --
   ------------------

   function Print_Scalar
     (Value    : Scalar_Value_Type;
      AST_Type : Entity_Id) return CNT_Unbounded_String
   is
      function To_String
        (Value : Scalar_Value_Type; Nul : out Boolean) return String;
      --  Turn Value into a string. Set Nul to True if Value might be
      --  represented as 0.

      ---------------
      -- To_String --
      ---------------

      function To_String
        (Value : Scalar_Value_Type; Nul : out Boolean) return String
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
   end Print_Scalar;

   -----------------
   -- Print_Value --
   -----------------

   function Print_Value (Value : Value_Type) return Value_And_Attributes is
   begin
      case Value.K is
         when Scalar_K =>

            --  Don't display uninitialized values

            declare
               Attributes : Name_Value_Lists.List;
            begin
               if Value.Initialized_Attr.Present then
                  declare
                     Init_Val : constant CNT_Unbounded_String :=
                       Make_CNT_Unbounded_String
                         (Nul => False,
                          Str => To_Unbounded_String
                            (if Value.Initialized_Attr.Content then "True"
                             else "False"));
                  begin
                     Attributes.Append
                       ((Name  => To_Unbounded_String ("'Initialized"),
                         Value => Init_Val));
                  end;
               end if;

               --  Don't display scalar values if 'Initialized is False

               if Value.Scalar_Content = null
                 or else (Value.Initialized_Attr.Present
                          and then not Value.Initialized_Attr.Content)
               then
                  return (Value => Dont_Display, Attributes => Attributes);
               else
                  return
                    (Value      =>
                       Print_Scalar (Value.Scalar_Content.all, Value.AST_Ty),
                     Attributes => Attributes);
               end if;
            end;

         when Record_K =>
            return Print_Record_Value (Value);

         when Array_K =>
            return Print_Array_Value (Value);

         when Access_K =>
            return Print_Access_Value (Value);
      end case;
   end Print_Value;

   function Print_Value (Value : Value_Type) return CNT_Unbounded_String is
      Val_And_Attrs : constant Value_And_Attributes :=
        Print_Value (Value);

   begin
      return Val_And_Attrs.Value;
   end Print_Value;

   ----------------------
   -- Print_Attributes --
   ----------------------

   procedure Print_Value_And_Attributes
     (Name        : Unbounded_String;
      Value       : Value_Type;
      Pretty_Line : in out Cntexample_Elt_Lists.List)
   is
      Val_And_Attrs : constant Value_And_Attributes :=
        Print_Value (Value);

   begin
      --  Append the pretty printed value of Value

      if Val_And_Attrs.Value /= Dont_Display then
         Pretty_Line.Append
           (Cntexample_Elt'(K       => Pretty_Printed,
                            Kind    => CEE_Variable,
                            Name    => Name,
                            Val_Str => Val_And_Attrs.Value));
      end if;

      --  Add the attributes

      declare
         Val_Attr : constant Name_Value_Lists.List :=
           Prefix_Names (Val_And_Attrs.Attributes, To_String (Name));
      begin
         for Name_And_Value of Val_Attr loop
            Pretty_Line.Append
              (Cntexample_Elt'(K       => Pretty_Printed,
                               Kind    => CEE_Variable,
                               Name    => Name_And_Value.Name,
                               Val_Str => Name_And_Value.Value));
         end loop;
      end;
   end Print_Value_And_Attributes;

end CE_Pretty_Printing;
