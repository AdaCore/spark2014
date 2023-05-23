------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            C E _ P A R S I N G                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2022-2023, AdaCore                     --
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

with Ada.Containers;           use Ada.Containers;
with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;
with Ada.Strings;              use Ada.Strings;
with Ada.Strings.Fixed;        use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;
with Ada.Unchecked_Conversion;
with CE_Utils;                 use CE_Utils;
with GNAT.String_Split;        use GNAT.String_Split;
with Gnat2Why.Tables;          use Gnat2Why.Tables;
with Gnat2Why.Util;            use Gnat2Why.Util;
with Interfaces;               use Interfaces;
with SPARK_Atree;              use SPARK_Atree;
with SPARK_Util;               use SPARK_Util;
with SPARK_Util.Types;         use SPARK_Util.Types;
with Stand;                    use Stand;
with Uintp;                    use Uintp;
with Urealp;                   use Urealp;
with Why.Gen.Names;            use Why.Gen.Names;

package body CE_Parsing is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Boolean_Value (B : Boolean) return Scalar_Value_Type is
     (K           => Enum_K,
      Enum_Entity => Boolean_Literals (B));

   function Parse_Float
     (Cnt_Value : Cntexmp_Value;
      Ty        : Entity_Id) return Scalar_Value_Type
   with Pre => Cnt_Value.T = Cnt_Float;

   function Parse_Cnt_Value
     (Cnt_Labels : S_String_List.List;
      Cnt_Value : Cntexmp_Value_Ptr;
      AST_Ty : Entity_Id) return Value_Type;
   --  Parse the Why3 counterexample value Cnt_Value

   function New_Item (AST_Ty : Entity_Id) return Value_Type;
   --  New element of appropriate kind depending on Ent_Ty

   --  This package is generic so that part of the work done can be shared
   --  between 32bit, 64 bits, and extended precision float numbers.

   generic
      type T_Unsigned is mod <>;
      type T_Float is digits <>;
   package Parse_Conversion is

      Bound : constant Integer := T_Unsigned'Size;

      function StringBits_To_Floatrepr
        (Sign, Significand, Exp : String) return T_Unsigned;
      --  Transform three stringbits into a single unsigned modular number
      --  (representing a float).

      function Unsigned_To_Float (U : T_Unsigned) return T_Float;
      --  Convert an unsigned number to a floating point number

      function StringBits_To_Float
        (Sign, Significand, Exp : String) return T_Float
      is
        (Unsigned_To_Float
           (StringBits_To_Floatrepr (Sign, Significand, Exp)));

   end Parse_Conversion;

   procedure Parse_Counterexample_Line
     (Cnt_List  : Cntexample_Elt_Lists.List;
      Obj       : Entity_Id;
      Value_Map : in out Entity_To_Extended_Value_Maps.Map);
   --  Go over a list of raw Why3 counterexample values and transform them into
   --  a map of counterexample values. If Obj is not empty, then only consider
   --  values applying to Obj at the current line (with modifier None).

   procedure Set_Boolean_Flag
     (Cnt_Value : Cntexmp_Value_Ptr; Flag : in out Opt_Boolean);

   procedure Set_Integer_Flag
     (Cnt_Value : Cntexmp_Value_Ptr;
      Flag      : in out Opt_Big_Integer);

   function Size (S : String) return Integer is
     (if S (S'First + 1) = 'x'
      then 4 * (S'Length - 2)
      else (S'Length - 2));
   --  Size returns the associate binary size of a #b or #x number (to help
   --  when building an unsigned integer).

   ------------------------------
   -- Get_Counterexample_Value --
   ------------------------------

   function Get_Counterexample_Value
     (Obj      : Entity_Id;
      Cnt_List : Cntexample_Elt_Lists.List) return Opt_Value_Type
   is
      V_Map : Entity_To_Extended_Value_Maps.Map;

   begin
      Parse_Counterexample_Line (Cnt_List, Obj, V_Map);
      pragma Assert (V_Map.Length <= 1);

      if V_Map.Contains (Obj) then
         pragma Assert (V_Map (Obj) (None) /= null);
         return (True, V_Map (Obj) (None).all);
      else
         return (Present => False);
      end if;
   end Get_Counterexample_Value;

   --------------
   -- New_Item --
   --------------

   function New_Item (AST_Ty : Entity_Id) return Value_Type is
      Ty : constant Entity_Id :=
        (if Is_Class_Wide_Type (AST_Ty)
         then Retysp (Get_Specific_Type_From_Classwide (AST_Ty))
         else Retysp (AST_Ty));
   begin
      if Is_Array_Type (Ty) and then Number_Dimensions (Ty) = 1 then
         return Value_Type'(K      => Array_K,
                            AST_Ty => Ty,
                            others => <>);
      elsif Is_Array_Type (Ty) then
         return Value_Type'
           (K      => Multidim_K,
            AST_Ty => Ty,
            Bounds => (Dim => Natural (Number_Dimensions (Ty)), others => <>));
      elsif Is_Record_Type_In_Why (Ty) then
         return Value_Type'(K      => Record_K,
                            AST_Ty => Ty,
                            others => <>);
      elsif Is_Access_Type (Ty) then
         return Value_Type'(K      => Access_K,
                            AST_Ty => Ty,
                            others => <>);
      else
         pragma Assert (Is_Scalar_Type (Ty));
         return Value_Type'(K      => Scalar_K,
                            AST_Ty => Ty,
                            others => <>);
      end if;
   end New_Item;

   ---------------------
   -- Parse_Cnt_Value --
   ---------------------

   function Parse_Cnt_Value
     (Cnt_Labels : S_String_List.List;
      Cnt_Value : Cntexmp_Value_Ptr;
      AST_Ty : Entity_Id) return Value_Type
   is
      use Cntexmp_Value_Array;
      Ty  : constant Entity_Id := Retysp (AST_Ty);
      Val : Value_Type := New_Item (AST_Ty);
   begin
      case Val.K is
         when Scalar_K =>

            --  Counterexample can be a record if the object has relaxed
            --  initialization. In this case, search for the values of the
            --  'Initialized attribute and the Init_Val component.

            if Cnt_Value.T = Cnt_Record then
               declare
                  C : Cntexmp_Value_Array.Cursor := Cnt_Value.Fi.First;
               begin
                  while Has_Element (C) loop
                     declare
                        Comp_Name : String renames Key (C);

                     begin
                        if Comp_Name = "'" & Initialized_Label then
                           Set_Boolean_Flag
                             (Element (C), Val.Initialized_Attr);
                        elsif Comp_Name = "'" & Init_Val_Label then
                           Val.Scalar_Content := new Scalar_Value_Type'
                             (Parse_Scalar_Value (Element (C).all, Ty));
                        else
                           raise Parse_Error;
                        end if;
                     end;
                     Next (C);
                  end loop;
               end;

            else
               Val.Scalar_Content := new Scalar_Value_Type'
                 (Parse_Scalar_Value (Cnt_Value.all, Ty));
            end if;

         --  No counterexample values are expected for multi-dimensional arrays

         when Multidim_K =>
            raise Parse_Error;

         when Array_K =>

            --  Counterexample should be an array

            if Cnt_Value.T /= Cnt_Array then
               raise Parse_Error;
            end if;

            --  Go over the association in the Why3 counterexample. If we fail
            --  to parse an element, continue with the next.

            declare
               Comp_Ty : constant Entity_Id := Retysp (Component_Type (Ty));
               Comp    : Value_Type;
            begin
               if Cnt_Value.Array_Others /= null then
                  begin
                     Comp := Parse_Cnt_Value
                       (Cnt_Labels, Cnt_Value.Array_Others, Comp_Ty);
                     Val.Array_Others := new Value_Type'(Comp);
                  exception
                     when Parse_Error =>
                        null;
                  end;
               end if;

               declare
                  C : Cntexmp_Value_Array.Cursor :=
                    Cnt_Value.Array_Indices.First;
               begin
                  while Has_Element (C) loop
                     begin
                        Comp := Parse_Cnt_Value
                          (Cnt_Labels, Element (C), Comp_Ty);
                        Val.Array_Values.Insert
                          (From_String (Key (C)), new Value_Type'(Comp));
                     exception
                        when Parse_Error =>
                           null;
                     end;
                     Next (C);
                  end loop;
               end;

               --  If the parsed value is empty, raise Parse_Error

               if Val.Array_Others = null
                 and then Val.Array_Values.Is_Empty
               then
                  raise Parse_Error;
               end if;
            end;

         when Record_K =>

            --  Records with only one field might be simplified by Why3
            --  transformations.
            --  In those cases, a field:_:_ attribute is added to the element.
            --  Here, we first search if this "field"_:_ attribute is present:
            --  - if yes, we reconstruct the record by extracting the field
            --  name from the attribute,
            --  - if no, we expect the Why3 counterexample to be a record.

            declare
               Field_Attr_Present : Boolean := False;
            begin
               for Label of Cnt_Labels loop
                  declare
                     Label_Name : constant String :=
                       Ada.Strings.Unbounded.To_String (Label);
                     Label_Parts : Slice_Set;
                  begin
                     --  Search for an attribute of the form field:_:S
                     --  where S is the name of the field.
                     Create (S          => Label_Parts,
                             From       => Label_Name,
                             Separators => ":",
                             Mode       => Single);
                     declare
                        Nb_Slices : constant Slice_Number :=
                          Slice_Count (Label_Parts);
                     begin
                        if Nb_Slices = 3 then
                           declare
                              First_Part : constant String :=
                                Slice (Label_Parts, 1);
                              Third_Part : constant String :=
                                Slice (Label_Parts, 3);
                           begin
                              if First_Part = "field" then

                                 --  We expect only one attribute of the form
                                 --  field:_:_.
                                 if Field_Attr_Present then
                                    raise Parse_Error;
                                 end if;

                                 declare
                                    Comp_E    : constant Entity_Id :=
                                      Get_Entity_Id (True, Third_Part);
                                 begin
                                    if Comp_E /= Types.Empty then
                                       declare
                                          Comp_Ty : constant Entity_Id :=
                                            Retysp (Etype (Comp_E));
                                          Comp    : Value_Type;
                                       begin
                                          Field_Attr_Present := True;
                                          --  Recursive call to Parse_Cnt_Value
                                          --  with empty list of labels since
                                          --  we have already used the field
                                          --  attribute.
                                          Comp := Parse_Cnt_Value
                                            (S_String_List.Empty_List,
                                             Cnt_Value, Comp_Ty);
                                          Val.Record_Fields.Insert
                                            (Comp_E, new Value_Type'(Comp));
                                       end;
                                    else
                                       raise Parse_Error;
                                    end if;
                                 end;
                              end if;
                           end;
                        end if;
                     end;
                  end;
               end loop;

               if not Field_Attr_Present
               --  Counterexample should be a record
                 and then Cnt_Value.T = Cnt_Record
               then
                  --  Go over the association in the Why3 counterexample to
                  --  store the fields inside Val.Record_Fields.
                  --  If we fail to parse an element, continue with the next.

                  declare
                     C : Cntexmp_Value_Array.Cursor := Cnt_Value.Fi.First;
                  begin
                     while Has_Element (C) loop
                        declare
                           Comp_Name : String renames Key (C);
                           Comp_E    : constant Entity_Id :=
                             Get_Entity_Id (True, Comp_Name);

                        begin
                           if Comp_E /= Types.Empty then
                              declare
                                 Comp_Ty : constant Entity_Id :=
                                   Retysp (Etype (Comp_E));
                                 Comp    : Value_Type;
                              begin
                                 Comp := Parse_Cnt_Value
                                   (Cnt_Labels, Element (C), Comp_Ty);
                                 Val.Record_Fields.Insert
                                   (Comp_E, new Value_Type'(Comp));
                              exception
                                 when Parse_Error =>
                                    null;
                              end;
                           elsif Comp_Name = "'" & Constrained_Label then
                              Set_Boolean_Flag
                                (Element (C), Val.Constrained_Attr);
                           end if;
                        end;
                        Next (C);
                     end loop;
                  end;
               end if;

               --  If the parsed value is empty, raise Parse_Error

               if Val.Record_Fields.Length = 0
                 and then not Val.Constrained_Attr.Present
               then
                  raise Parse_Error;
               end if;
            end;

         when Access_K =>

            --  Counterexample should be a record

            if Cnt_Value.T /= Cnt_Record then
               raise Parse_Error;
            end if;

            --  Go over the association in the Why3 counterexample to store the
            --  fields inside Val.Record_Fields. If we fail to parse an
            --  element, continue with the next.

            declare
               C : Cntexmp_Value_Array.Cursor := Cnt_Value.Fi.First;
            begin
               while Has_Element (C) loop
                  declare
                     Comp_Name : String renames Key (C);
                     Cnt_Elt   : Cntexmp_Value_Ptr renames Element (C);

                  begin
                     if Comp_Name = "'" & All_Label then
                        declare
                           Des_Ty : constant Entity_Id :=
                             Retysp (Directly_Designated_Type (Ty));
                        begin
                           Val.Designated_Value :=
                             new Value_Type'
                               (Parse_Cnt_Value (Cnt_Labels, Cnt_Elt, Des_Ty));
                        exception
                           when Parse_Error =>
                              null;
                        end;
                     elsif Comp_Name = "'" & Is_Null_Label then
                        Set_Boolean_Flag (Cnt_Elt, Val.Is_Null);
                     end if;
                  end;
                  Next (C);
               end loop;
            end;
      end case;

      return Val;
   end Parse_Cnt_Value;

   ----------------------
   -- Parse_Conversion --
   ----------------------

   package body Parse_Conversion is

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

      function StringBits_To_Floatrepr
        (Sign, Significand, Exp : String) return T_Unsigned
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

      -----------------------
      -- Unsigned_To_Float --
      -----------------------

      function Unsigned_To_Float (U : T_Unsigned) return T_Float is
         function Convert is new Ada.Unchecked_Conversion
           (Source => T_Unsigned,
            Target => T_Float);

      begin
         if Convert (U)'Valid then

            --  Unchecked conversion
            return Convert (U);
         else
            raise Parse_Error;
         end if;
      end Unsigned_To_Float;

   end Parse_Conversion;

   -------------------------------
   -- Parse_Counterexample_Line --
   -------------------------------

   procedure Parse_Counterexample_Line
     (Cnt_List  : Cntexample_Elt_Lists.List;
      Obj       : Entity_Id;
      Value_Map : in out Entity_To_Extended_Value_Maps.Map)
   is

      function Is_Multidim_Label (Label, Attr_Label : String) return Boolean is
         (for some Dim in 1 .. 4 =>
             Label = Attr_Label & " (" & Trim (Dim'Image, Left) & ")");

   begin
      for Elt of Cnt_List loop
         declare
            Elt_Name   : constant String :=
              Ada.Strings.Unbounded.To_String (Elt.Name);
            Name_Parts : Slice_Set;

         begin
            --  Ignore error messages

            if Elt.Kind = CEE_Error_Msg then
               raise Parse_Error;
            end if;

            --  Split Name into sequence of parts

            Create (S          => Name_Parts,
                    From       => Elt_Name,
                    Separators => ".'",
                    Mode       => Single);

            declare
               Nb_Slices : constant Slice_Number := Slice_Count (Name_Parts);
               Var       : constant Entity_Id :=
                 Get_Entity_Id (False, Slice (Name_Parts, 1));
               --  The first part is the entity to which the counterexample
               --  applies.

               Var_Modifier  : Modifier :=
                 (case Elt.Kind is
                     when CEE_Old    => Old,
                     when CEE_Result => Result,
                     when others     => None);
               Is_Attribute  : Boolean := False;
               Current_Slice : Slice_Number := 2;
               Current_Ty    : Entity_Id;
               Current_Val   : Value_Access;

            begin
               --  The first part shall be an entity

               if Var = Empty then
                  raise Parse_Error;
               end if;

               Current_Ty := Retysp (Etype (Var));

               --  Attributes 'Old, 'Loop_Entry, 'Index, 'Discriminants, and
               --  'Fields can only occur at top-level. We handle them here.

               if Nb_Slices > 1 then
                  declare
                     Top_Level_Attr : constant String :=
                       Slice (Name_Parts, 2);

                  begin
                     if Top_Level_Attr = Old_Label then
                        Var_Modifier := Old;
                        Current_Slice := 3;
                     elsif Top_Level_Attr = Loop_Entry_Label then
                        Var_Modifier := Loop_Entry;
                        Current_Slice := 3;

                     --  Go to the enclosing quantified expression to find
                     --  the Why3 type on which the quantification is done.
                     --  It is the first index type for an array and the
                     --  ultimate cursor type for a container.
                     --  ??? What about multidim arrays?

                     elsif Top_Level_Attr = Index_Label then
                        Var_Modifier := Index;

                        declare
                           function Is_Quantified_Expr
                             (N : Node_Id) return Boolean
                           is
                             (Nkind (N) = N_Quantified_Expression);
                           function Enclosing_Quantified_Expr is new
                             First_Parent_With_Property (Is_Quantified_Expr);

                           Container : constant Entity_Id :=
                             Get_Container_In_Iterator_Specification
                               (Iterator_Specification
                                  (Enclosing_Quantified_Expr (Var)));
                           pragma Assert (Present (Container));

                           Container_Typ : constant Entity_Id :=
                             Retysp (Etype (Container));
                        begin
                           if Is_Array_Type (Container_Typ) then
                              Current_Ty := Retysp
                                (Etype (First_Index (Container_Typ)));
                           else
                              Current_Ty :=
                                Ultimate_Cursor_Type (Container_Typ);
                           end if;
                        end;
                        Current_Slice := 3;

                     --  Fields and discriminants are collapsed in a single
                     --  object.

                     elsif Top_Level_Attr in Discr_Label | Field_Label then
                        Current_Slice := 3;
                     end if;
                  end;
               end if;

               --  If Obj is set, skip the value if it does not apply to Obj or
               --  if the modifier is not None.

               if Present (Obj)
                 and then (Var /= Obj or else Var_Modifier /= None)
               then
                  raise Parse_Error;
               end if;

               --  Search for the variable Ent in Value_Map. If we already have
               --  an association for the Var_Modifier modifier for it,
               --  retrieve it. Otherwise, create a new one.

               declare
                  use Entity_To_Extended_Value_Maps;
                  Position : Cursor := Value_Map.Find (Var);
                  Inserted : Boolean;
                  Arr      : Extended_Value_Access;

               begin
                  if Position = No_Element then
                     Arr (Var_Modifier) :=
                       new Value_Type'(New_Item (Current_Ty));
                     Value_Map.Insert
                       (Key      => Var,
                        New_Item => Arr,
                        Position => Position,
                        Inserted => Inserted);
                     pragma Assert (Inserted);

                  elsif Value_Map (Position) (Var_Modifier) = null then
                     Value_Map (Position) (Var_Modifier) :=
                       new Value_Type'(New_Item (Current_Ty));
                  end if;

                  Current_Val := Value_Map (Position) (Var_Modifier);
               end;

               --  Now handle record fields and normal attributes

               while Current_Slice <= Nb_Slices loop
                  declare
                     Label  : constant String :=
                       Slice (Name_Parts, Current_Slice);
                     Comp_E : constant Entity_Id :=
                       Get_Entity_Id (False, Label);
                  begin
                     --  If Label does not cast into an entity_id it is treated
                     --  as an attribute.

                     Is_Attribute := No (Comp_E);

                     --  Fields of access types do not have node ids, they are
                     --  hanlded as special strings.

                     if Label = All_Label then
                        if Current_Val.K /= Access_K then
                           raise Parse_Error;
                        else
                           Current_Ty := Retysp
                             (Directly_Designated_Type (Current_Ty));

                           if Current_Val.Designated_Value = null then
                              Current_Val.Designated_Value :=
                                new Value_Type'(New_Item (Current_Ty));
                           end if;
                           Current_Val := Current_Val.Designated_Value;
                           Is_Attribute := False;
                        end if;
                     elsif Label = Is_Null_Label then
                        if Current_Val.K /= Access_K then
                           raise Parse_Error;
                        else
                           Set_Boolean_Flag
                             (Elt.Value, Current_Val.Is_Null);
                        end if;

                     --  Regular attributes

                     elsif Label = First_Label then
                        if Current_Val.K /= Array_K then
                           raise Parse_Error;
                        else
                           Set_Integer_Flag
                             (Elt.Value, Current_Val.First_Attr);
                        end if;

                     elsif Label = Last_Label then
                        if Current_Val.K /= Array_K then
                           raise Parse_Error;
                        else
                           Set_Integer_Flag
                             (Elt.Value, Current_Val.Last_Attr);
                        end if;

                     elsif Is_Multidim_Label (Label, First_Label) then
                        declare
                           Dim : constant Natural :=
                             Natural'Value
                               (Label (Label'Last - 1 .. Label'Last - 1));
                        begin
                           if Current_Val.K /= Multidim_K
                             or else Dim > Current_Val.Bounds.Dim
                           then
                              raise Parse_Error;
                           else
                              Set_Integer_Flag
                                (Elt.Value,
                                 Current_Val.Bounds.Content (Dim).First);
                           end if;
                        end;

                     elsif Is_Multidim_Label (Label, Last_Label) then
                        declare
                           Dim : constant Natural :=
                             Natural'Value
                               (Label (Label'Last - 1 .. Label'Last - 1));
                        begin
                           if Current_Val.K /= Multidim_K
                             or else Dim > Current_Val.Bounds.Dim
                           then
                              raise Parse_Error;
                           else
                              Set_Integer_Flag
                                (Elt.Value,
                                 Current_Val.Bounds.Content (Dim).Last);
                           end if;
                        end;

                     elsif Label = Constrained_Label then
                        if Current_Val.K /= Record_K then
                           raise Parse_Error;
                        else
                           Set_Boolean_Flag
                             (Elt.Value, Current_Val.Constrained_Attr);
                        end if;

                     elsif Label = Initialized_Label then
                        if Current_Val.K /= Scalar_K then
                           raise Parse_Error;
                        else
                           Set_Boolean_Flag
                             (Elt.Value, Current_Val.Initialized_Attr);
                        end if;

                     --  Regular record field

                     else
                        pragma Assert (not Is_Attribute);

                        if Current_Val.K /= Record_K
                          or else No
                            (Search_Component_In_Type (Current_Ty, Comp_E))
                        then
                           raise Parse_Error;
                        elsif not Current_Val.Record_Fields.Contains (Comp_E)
                        then
                           Current_Val.Record_Fields.Insert
                             (Comp_E,
                              new Value_Type'(New_Item (Etype (Comp_E))));
                        end if;

                        Current_Val := Current_Val.Record_Fields.Element
                          (Comp_E);
                        Current_Ty := Current_Val.AST_Ty;
                     end if;
                  end;

                  --  If we have reached an attribute, iteration should be over

                  pragma Assert
                    (if Is_Attribute then Current_Slice = Nb_Slices);
                  Current_Slice := Current_Slice + 1;
               end loop;

               --  If we do not have an attribute, we can now parse the Why3
               --  counterexample value to merge it inside Val.
               --  The later values in counterexample are considered to be
               --  better values (in loop they correspond to the preservation
               --  part which is often the complex one). So we override
               --  existing values if there are some. A notable exception to
               --  this rule are attributes which are only overriden when
               --  present and record fields which are merged.

               if not Is_Attribute then
                  declare
                     use Entity_To_Value_Maps;
                     New_Val : constant Value_Type :=
                       Parse_Cnt_Value (Elt.Labels, Elt.Value, Current_Ty);
                  begin
                     pragma Assert (Current_Val.K = New_Val.K);
                     pragma Assert (Current_Val.AST_Ty = New_Val.AST_Ty);

                     case Current_Val.K is
                        when Scalar_K =>
                           Current_Val.Scalar_Content :=
                             New_Val.Scalar_Content;

                           if New_Val.Initialized_Attr.Present then
                              Current_Val.Initialized_Attr :=
                                New_Val.Initialized_Attr;
                           end if;

                        when Multidim_K =>
                           pragma Assert
                             (Current_Val.Bounds.Dim = New_Val.Bounds.Dim);

                           for I in Current_Val.Bounds.Content'Range loop
                              if New_Val.Bounds.Content (I).First.Present then
                                 Current_Val.Bounds.Content (I).First :=
                                   New_Val.Bounds.Content (I).First;
                              end if;
                              if New_Val.Bounds.Content (I).Last.Present then
                                 Current_Val.Bounds.Content (I).Last :=
                                   New_Val.Bounds.Content (I).Last;
                              end if;
                           end loop;

                        when Array_K =>
                           Current_Val.Array_Values := New_Val.Array_Values;
                           Current_Val.Array_Others := New_Val.Array_Others;

                           if New_Val.First_Attr.Present then
                              Current_Val.First_Attr := New_Val.First_Attr;
                           end if;
                           if New_Val.Last_Attr.Present then
                              Current_Val.Last_Attr := New_Val.Last_Attr;
                           end if;

                        when Record_K =>
                           for Pos in New_Val.Record_Fields.Iterate loop
                              Current_Val.Record_Fields.Include
                                (Key (Pos), Element (Pos));
                           end loop;

                           if New_Val.Constrained_Attr.Present then
                              Current_Val.Constrained_Attr :=
                                New_Val.Constrained_Attr;
                           end if;

                        when Access_K =>
                           Current_Val.Designated_Value :=
                             New_Val.Designated_Value;

                           if New_Val.Is_Null.Present then
                              Current_Val.Is_Null := New_Val.Is_Null;
                           end if;
                     end case;
                  end;
               end if;
            end;
         exception
            when Parse_Error => null;
         end;
      end loop;
   end Parse_Counterexample_Line;

   procedure Parse_Counterexample_Line
     (Cnt_List  : Cntexample_Elt_Lists.List;
      Value_Map : in out Entity_To_Extended_Value_Maps.Map)
   is
   begin
      Parse_Counterexample_Line (Cnt_List, Empty, Value_Map);
   end Parse_Counterexample_Line;

   -----------------
   -- Parse_Float --
   -----------------

   function Parse_Float
     (Cnt_Value : Cntexmp_Value;
      Ty        : Entity_Id) return Scalar_Value_Type
   is
      use Ada.Strings.Unbounded;
      F : VC_Kinds.Float_Value renames Cnt_Value.F.all;
   begin
      case F.F_Type is
         when Float_Plus_Infinity | Float_Minus_Infinity | Float_NaN =>

            --  Decision: we don't handle infinities or Nan
            raise Parse_Error;

         when Float_Plus_Zero | Float_Minus_Zero =>
            if Is_Single_Precision_Floating_Point_Type (Ty) then
               return (Float_K, (Float_32_K, 0.0));
            elsif Is_Double_Precision_Floating_Point_Type (Ty) then
               return (Float_K, (Float_64_K, 0.0));
            elsif Is_Extended_Precision_Floating_Point_Type (Ty) then
               return (Float_K, (Extended_K, 0.0));
            else
               raise Program_Error;
            end if;

         when Float_Val =>
            declare
               Sign        : constant String := To_String (F.F_Sign);
               Significand : constant String := To_String (F.F_Significand);
               Exp         : constant String := To_String (F.F_Exponent);
            begin
               pragma Assert (Size (Sign) = 1);
               if Is_Single_Precision_Floating_Point_Type (Ty) then
                  pragma Assert (Size (Exp) = 8);
                  pragma Assert (Size (Significand) = 23);
                  declare
                     package P is new Parse_Conversion (Unsigned_32, Float);
                     F : constant Float :=
                       P.StringBits_To_Float (Sign, Significand, Exp);
                  begin
                     return (Float_K, (Float_32_K, F));
                  end;
               elsif Is_Double_Precision_Floating_Point_Type (Ty) then
                  pragma Assert (Size (Exp) = 11);
                  pragma Assert (Size (Significand) = 52);
                  declare
                     package P is new Parse_Conversion
                       (Interfaces.Unsigned_64, Long_Float);
                     F : constant Long_Float :=
                       P.StringBits_To_Float (Sign, Significand, Exp);
                  begin
                     return (Float_K, (Float_64_K, F));
                  end;
               elsif Is_Extended_Precision_Floating_Point_Type (Ty) then
                  pragma Assert (Size (Exp) = 15);
                  pragma Assert (Size (Significand) = 63);
                  declare
                     package P is new Parse_Conversion
                       (Interfaces.Unsigned_128, Long_Long_Float);
                     F : constant Long_Long_Float :=
                       P.StringBits_To_Float (Sign, Significand, Exp);
                  begin
                     return (Float_K, (Extended_K, F));
                  end;
               else
                  raise Program_Error;
               end if;
            end;
      end case;
   end Parse_Float;

   ------------------------
   -- Parse_Scalar_Value --
   ------------------------

   function Parse_Scalar_Value
     (Cnt_Value : Cntexmp_Value;
      AST_Type  : Entity_Id) return Scalar_Value_Type
   is
      use Ada.Strings.Unbounded;
      Why3_Type : constant Cntexmp_Type := Cnt_Value.T;
   begin
      case Why3_Type is
         when Cnt_Integer =>

            --  Necessary for some types that makes boolean be translated to
            --  integers like: "subype only_true := True .. True".

            if Is_Boolean_Type (AST_Type) then
               return Boolean_Value
                 (From_String (To_String (Cnt_Value.I)) /= Big_Integer'(0));

            elsif Is_Enumeration_Type (AST_Type) then
               declare
                  Value : constant Uint := UI_From_String
                    (To_String (Cnt_Value.I));

                  --  Call Get_Enum_Lit_From_Pos to get a corresponding
                  --  enumeration entity.

                  Lit : Node_Id;

               begin
                  --  Initialization of Enum can raise Constraint_Error if
                  --  there is no literal value for the position.

                  Lit := Get_Enum_Lit_From_Pos (AST_Type, Value);
                  return
                    (K           => Enum_K,
                     Enum_Entity =>
                       (if Nkind (Lit) = N_Character_Literal then Lit
                        else Entity (Lit)));

               --  An exception is raised by Get_Enum_Lit_From_Pos if the
               --  position Value is outside the bounds of the enumeration.
               --  In such a case, return the raw integer returned by the
               --  prover.

               exception
                  when Constraint_Error =>
                     raise Parse_Error;
               end;

            --  Cvc4 returns Floating_point value with integer type. We
            --  don't want to consider those.

            elsif Is_Floating_Point_Type (AST_Type) then
               raise Parse_Error;

            elsif Is_Fixed_Point_Type (AST_Type) then
               declare
                  Small : constant Ureal := Small_Value (AST_Type);
                  Num   : constant Big_Integer :=
                    From_String (UI_Image (Norm_Num (Small), Decimal));
                  Den   : constant Big_Integer :=
                    From_String (UI_Image (Norm_Den (Small), Decimal));
                  Val    : Big_Integer;

               begin
                  Val := From_String (To_String (Cnt_Value.I));
                  return (Fixed_K, Val, Num / Den);

               exception
                  when Constraint_Error =>
                     raise Parse_Error;
               end;

            --  Only integer types are expected in that last case

            else
               pragma Assert (Has_Integer_Type (AST_Type));

               declare
                  Val : Big_Integer;

               begin
                  Val := From_String (To_String (Cnt_Value.I));
                  return (Integer_K, Val);

               exception
                  when Constraint_Error =>
                     raise Parse_Error;
               end;
            end if;

         when Cnt_Boolean =>
               return Boolean_Value (Cnt_Value.Bo);

         when Cnt_Bitvector =>

            --  Boolean are translated into bitvector of size 1 for CVC4
            --  because it fails to produce a model when booleans are used
            --  inside translated arrays_of_records.

            if Is_Boolean_Type (AST_Type) then
               return Boolean_Value (Cnt_Value.B = "0");
            end if;

            declare
               Val : Big_Integer;

            begin
               Val := From_String (To_String (Cnt_Value.B));
               return (Integer_K, Val);

            exception
               when Constraint_Error =>
                  raise Parse_Error;
            end;

         when Cnt_Decimal =>
            pragma Assert (Is_Floating_Point_Type (AST_Type));

            begin
               if Is_Single_Precision_Floating_Point_Type (AST_Type) then
                  return
                    (Float_K,
                     (Float_32_K, Float'Value (To_String (Cnt_Value.B))));
               elsif Is_Double_Precision_Floating_Point_Type (AST_Type) then
                  return
                    (Float_K,
                     (Float_64_K, Long_Float'Value (To_String (Cnt_Value.B))));
               elsif Is_Extended_Precision_Floating_Point_Type (AST_Type) then
                  return
                    (Float_K,
                     (Extended_K,
                      Long_Long_Float'Value (To_String (Cnt_Value.B))));
               else
                  raise Program_Error;
               end if;
            exception
               when Constraint_Error =>
                  raise Parse_Error;
            end;

         when Cnt_Float =>
            pragma Assert (Is_Floating_Point_Type (AST_Type));

            return Parse_Float (Cnt_Value, AST_Type);

         when Cnt_Invalid
            | Cnt_Projection
            | Cnt_Record
            | Cnt_Array
          =>
            raise Parse_Error;
      end case;
   end Parse_Scalar_Value;

   ----------------------
   -- Set_Boolean_Flag --
   ----------------------

   procedure Set_Boolean_Flag
     (Cnt_Value : Cntexmp_Value_Ptr; Flag : in out Opt_Boolean)
   is
      Comp : Scalar_Value_Type;
   begin
      Comp := Parse_Scalar_Value (Cnt_Value.all, Standard_Boolean);
      Flag := (True, Comp.Enum_Entity = Standard_True);
   exception
      when Parse_Error =>
         null;
   end Set_Boolean_Flag;

   ----------------------
   -- Set_Integer_Flag --
   ----------------------

   procedure Set_Integer_Flag
     (Cnt_Value : Cntexmp_Value_Ptr;
      Flag      : in out Opt_Big_Integer)
   is
      Comp : Big_Integer;
   begin
      case Cnt_Value.T is
         when Cnt_Integer =>
            Comp := From_String
              (Ada.Strings.Unbounded.To_String (Cnt_Value.I));
         when Cnt_Bitvector =>
            Comp := From_String
              (Ada.Strings.Unbounded.To_String (Cnt_Value.B));
         when others =>
            raise Parse_Error;
      end case;
      Flag := (True, Comp);
   exception
      when Parse_Error =>
         null;
   end Set_Integer_Flag;

end CE_Parsing;
