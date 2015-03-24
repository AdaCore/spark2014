------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with GNATCOLL.Utils;      use GNATCOLL.Utils;
with Stand;               use Stand;
with SPARK_Definition;    use SPARK_Definition;
with SPARK_Util;          use SPARK_Util;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Types;           use Why.Types;
with Why.Inter;           use Why.Inter;

package body Why.Gen.Names is

   function Uint_To_Positive (U : Uint) return Positive;
   --  Limited version of conversion that only works for 1 to 4

   function Get_Modular_Converter
     (From, To : W_Type_Id) return W_Identifier_Id;
   --  @param From the BV type to convert from
   --  @param To the BV type to convert to
   --  @return the conversion function from BV From to BV To

   Pre_Computed_Idents : array (Why_Name_Enum) of W_Identifier_Id :=
     (others => Why_Empty);
   --  This array is used to precompute all fixed idents.

   ----------------------
   -- Append_Num --
   ----------------------

   function Append_Num (S : String; Count : Positive) return String is
   begin
      return (if Count = 1 then S else S & "_" & Image (Count, 1));
   end Append_Num;

   function Append_Num (S : String; Count : Uint) return String is
   begin
      return Append_Num (S, Uint_To_Positive (Count));
   end Append_Num;

   function Append_Num (S        : String;
                        Count    : Positive;
                        Module   : W_Module_Id := Why_Empty;
                        Typ      : W_Type_Id := Why.Types.Why_Empty;
                        Ada_Node : Node_Id := Empty)
                        return W_Identifier_Id is
   begin
      return New_Identifier
        (Domain => EW_Term,
         Name     => Append_Num (S, Count),
         Module  =>  Module,
         Ada_Node => Ada_Node,
         Typ      => Typ);
   end Append_Num;

   function Append_Num (W : Why_Name_Enum; Count : Positive)
                        return W_Identifier_Id
   is
   begin
      return Append_Num (To_String (W), Count);
   end Append_Num;

   function Append_Num (W : Why_Name_Enum; Count : Uint)
                        return W_Identifier_Id
   is
   begin
      return Append_Num (W, Uint_To_Positive (Count));
   end Append_Num;

   function Append_Num (P, W : Why_Name_Enum; Count : Positive)
                        return W_Identifier_Id
   is
   begin
      return Append_Num (To_String (P) & "." & To_String (W), Count);
   end Append_Num;

   -----------------
   -- Attr_Append --
   -----------------

   function Attr_Append (Base     : String;
                         A        : Attribute_Id;
                         Count    : Positive;
                         Typ      : W_Type_Id;
                         Module   : W_Module_Id := Why.Types.Why_Empty;
                         Ada_Node : Node_Id := Empty) return W_Identifier_Id is
   begin
      return
        Append_Num (S        => Base & "__" & To_String (Attr_To_Why_Name (A)),
                    Count    => Count,
                    Typ      => Typ,
                    Module  => Module,
                    Ada_Node => Ada_Node);
   end Attr_Append;

   function Attr_Append (Base  : W_Identifier_Id;
                         A     : Attribute_Id;
                         Count : Positive;
                         Typ   : W_Type_Id) return W_Identifier_Id is
   begin
      return
        Attr_Append
          (Get_Name_String (Get_Symbol (+Base)),
           A,
           Count,
           Typ,
           Get_Module (Base),
           Get_Ada_Node (+Base));
   end Attr_Append;

   ----------------------
   -- Attr_To_Why_Name --
   ----------------------

   function Attr_To_Why_Name (A : Attribute_Id) return Why_Name_Enum is
   begin
      case A is
         when Attribute_Constrained => return WNE_Attr_Constrained;
         when Attribute_First       => return WNE_Attr_First;
         when Attribute_Image       => return WNE_Attr_Image;
         when Attribute_Last        => return WNE_Attr_Last;
         when Attribute_Modulus     => return WNE_Attr_Modulus;
         when Attribute_Length      => return WNE_Attr_Length;
         when Attribute_Value       => return WNE_Attr_Value;
         when Attribute_Small       => return WNE_Attr_Small;
         when Attribute_Size        => return WNE_Attr_Size;
         when Attribute_Tag         => return WNE_Attr_Tag;
         when others =>
            raise Program_Error;
      end case;
   end Attr_To_Why_Name;

   ---------------------
   -- Conversion_Name --
   ---------------------

   function Conversion_Name
      (From : W_Type_Id;
       To   : W_Type_Id) return W_Identifier_Id
   is
      From_Kind : constant EW_Type := Get_Type_Kind (From);
      To_Kind   : constant EW_Type := Get_Type_Kind (To);
   begin
      case From_Kind is
         when EW_Builtin =>
            case To_Kind is
               when EW_Builtin =>

                  --  Only certain conversions are OK

                  if From = EW_Int_Type and then To = EW_Real_Type then
                     return M_Floating.Real_Of_Int;

                  --  Conversions from real to int in Ada round to the nearest
                  --  integer, and away from zero in case of tie, exactly like
                  --  'Rounding attribute.

                  elsif From = EW_Real_Type and then To = EW_Int_Type then
                     return M_Floating.Round;
                  elsif From = EW_Bool_Type and then To = EW_Int_Type then
                     return M_Boolean.To_Int;
                  elsif From = EW_Int_Type and then To = EW_Bool_Type then
                     return M_Boolean.Of_Int;
                  elsif Why_Type_Is_BitVector (From) and then
                    To = EW_Int_Type
                  then
                     return MF_BVs (From).To_Int;
                  elsif From = EW_Int_Type and then
                    Why_Type_Is_BitVector (To)
                  then
                     return MF_BVs (To).Of_Int;
                  elsif Why_Type_Is_BitVector (From) and then
                    Why_Type_Is_BitVector (To)
                  then
                     return Get_Modular_Converter (From, To);
                  --  Either the two objects are of the same type
                  --  (in which case the conversion is useless) or
                  --  they are of incompatible types
                  --  In both cases, it is an error.

                  else
                     raise Program_Error;
                  end if;

               when EW_Abstract | EW_Split =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+To);
                  begin
                     if Base_Why_Type (To) = From and then
                       (From = EW_Int_Type or else
                        Why_Type_Is_BitVector (From))
                     then
                        --  if we're converting from the representation type
                        --  of a discrete kind
                        return Prefix (Ada_Node => A,
                                       M => E_Module (A),
                                       W => WNE_Of_Rep);
                     else
                        return
                          Prefix (Ada_Node => A,
                                  M        => E_Module (A),
                                  W        => Convert_From (From));
                     end if;
                  end;
            end case;

         when EW_Abstract | EW_Split =>
            case To_Kind is
               when EW_Builtin =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+From);
                  begin
                     if Base_Why_Type (From) = To and then
                       (To = EW_Int_Type or else
                        Why_Type_Is_BitVector (To))
                     then
                        --  if we're converting to the representation type
                        --  of a discrete kind
                        return Prefix (Ada_Node => A,
                                       M => E_Module (A),
                                       W => WNE_To_Rep);
                     else
                        return
                          Prefix (Ada_Node => A,
                                  M        => E_Module (A),
                                  W => Convert_To (To));
                     end if;
                  end;

               --  Case of a conversion between two record or private types

               when EW_Abstract | EW_Split =>
                  declare
                     From_Node : constant Node_Id := Get_Ada_Node (+From);
                     To_Node   : constant Node_Id := Get_Ada_Node (+To);
                     From_Base : constant Node_Id :=
                       (if Fullview_Not_In_SPARK (From_Node) then
                             Get_First_Ancestor_In_SPARK (From_Node)
                        else Root_Record_Type (From_Node));
                  begin
                     if From_Base = From_Node then
                        return
                          Prefix (Ada_Node => To_Node,
                                  M        => E_Module (To_Node),
                                  W        => WNE_Of_Base);
                     else
                        return
                          Prefix (Ada_Node => From_Node,
                                  M        => E_Module (From_Node),
                                  W        => WNE_To_Base);
                     end if;
                  end;
            end case;
      end case;
   end Conversion_Name;

   ------------------
   -- Convert_From --
   ------------------

   function Convert_From (Kind : W_Type_Id) return Why_Name_Enum is
   begin
      if Kind = EW_Int_Type then
         return WNE_Of_Int;
      elsif Kind = EW_Fixed_Type then
         return WNE_Of_Fixed;
      elsif Kind = EW_Real_Type then
         return WNE_Of_Real;
      elsif Why_Type_Is_BitVector (Kind) then
         return WNE_Of_BitVector;
      else
         raise Why.Not_Implemented;
      end if;
   end Convert_From;

   ----------------
   -- Convert_To --
   ----------------

   function Convert_To (Kind : W_Type_Id) return Why_Name_Enum is
   begin
      if Kind = EW_Int_Type then
         return WNE_To_Int;
      elsif Kind = EW_Fixed_Type then
         return WNE_To_Fixed;
      elsif Kind = EW_Real_Type then
         return WNE_To_Real;
      elsif Why_Type_Is_BitVector (Kind) then
         return WNE_To_BitVector;
      else
         raise Why.Not_Implemented;
      end if;
   end Convert_To;

   ------------------
   -- Discr_Append --
   ------------------

   function Discr_Append (Base  : W_Identifier_Id;
                          Typ   : W_Type_Id) return W_Identifier_Id is
   begin
      return
        Append_Num
          (S        => Get_Name_String (Get_Symbol (+Base))
           & To_String (WNE_Rec_Split_Discrs),
           Count    => 1,
           Typ      => Typ,
           Module   => Get_Module (Base),
           Ada_Node => Get_Ada_Node (+Base));
   end Discr_Append;

   -----------------------
   -- Dynamic_Prop_Name --
   -----------------------

   function Dynamic_Prop_Name (Ty : Entity_Id) return W_Identifier_Id
   is
   begin
      if Is_Standard_Boolean_Type (Ty) then
         return Prefix (Ada_Node => Standard_Boolean,
                        M        => M_Boolean.Module,
                        W        => WNE_Dynamic_Property);
      else
         return Prefix (Ada_Node => Ty,
                        M        => E_Module (Ty),
                        W        => WNE_Dynamic_Property);
      end if;
   end Dynamic_Prop_Name;

   ------------------
   -- Field_Append --
   ------------------

   function Field_Append (Base  : W_Identifier_Id;
                          Typ   : W_Type_Id) return W_Identifier_Id is
   begin
      return
        Append_Num
          (S        => Get_Name_String (Get_Symbol (+Base))
           & To_String (WNE_Rec_Split_Fields),
           Count    => 1,
           Typ      => Typ,
           Module   => Get_Module (Base),
           Ada_Node => Get_Ada_Node (+Base));
   end Field_Append;

   ----------------------
   -- Float_Round_Name --
   ----------------------

   function Float_Round_Name (Ty : Entity_Id) return W_Identifier_Id is
   begin
      return Prefix (Ada_Node => Ty,
                     M        => E_Module (Ty),
                     W        => WNE_Float_Round);
   end Float_Round_Name;

   ---------------------------
   -- Get_Modular_Converter --
   ---------------------------

   function Get_Modular_Converter
     (From, To : W_Type_Id) return W_Identifier_Id is
   begin
      if From = EW_BitVector_8_Type then

         if To = EW_BitVector_16_Type then
            return M_BV_Conv_8_16.To_Big;
         elsif To = EW_BitVector_32_Type then
            return M_BV_Conv_8_32.To_Big;
         elsif To = EW_BitVector_64_Type then
            return M_BV_Conv_8_64.To_Big;
         else
            raise Program_Error;
         end if;

      elsif From = EW_BitVector_16_Type then

         if To = EW_BitVector_8_Type then
            return M_BV_Conv_8_16.To_Small;
         elsif To = EW_BitVector_32_Type then
            return M_BV_Conv_16_32.To_Big;
         elsif To = EW_BitVector_64_Type then
            return M_BV_Conv_16_64.To_Big;
         else
            raise Program_Error;
         end if;

      elsif From = EW_BitVector_32_Type then

         if To = EW_BitVector_8_Type then
            return M_BV_Conv_8_32.To_Small;
         elsif To = EW_BitVector_16_Type then
            return M_BV_Conv_16_32.To_Small;
         elsif To = EW_BitVector_64_Type then
            return M_BV_Conv_32_64.To_Big;
         else
            raise Program_Error;
         end if;

      elsif From = EW_BitVector_64_Type then

         if To = EW_BitVector_8_Type then
            return M_BV_Conv_8_64.To_Small;
         elsif To = EW_BitVector_16_Type then
            return M_BV_Conv_16_64.To_Small;
         elsif To = EW_BitVector_32_Type then
            return M_BV_Conv_32_64.To_Small;
         else
            raise Program_Error;
         end if;

      else
         raise Program_Error;
      end if;
   end Get_Modular_Converter;

   function Get_Modular_Converter_Range_Check
     (From, To : W_Type_Id) return W_Identifier_Id is
   begin
      if From = EW_BitVector_16_Type then
         return M_BV_Conv_8_16.Range_Check;
      elsif From = EW_BitVector_32_Type then
         if To = EW_BitVector_8_Type then
            return M_BV_Conv_8_32.Range_Check;
         else
            return M_BV_Conv_16_32.Range_Check;
         end if;
      else
         if To = EW_BitVector_8_Type then
            return M_BV_Conv_8_64.Range_Check;
         elsif To = EW_BitVector_16_Type then
            return M_BV_Conv_16_64.Range_Check;
         else
            return M_BV_Conv_32_64.Range_Check;
         end if;
      end if;
   end Get_Modular_Converter_Range_Check;

   -------------
   -- New_Abs --
   -------------

   function New_Abs (Kind : W_Type_Id) return W_Identifier_Id is
   begin
      if Kind = EW_Real_Type then
         return M_Floating.Abs_Real;
      elsif Kind = EW_Int_Type or else Kind = EW_Fixed_Type then
         return M_Int_Abs.Abs_Id;
      elsif Why_Type_Is_BitVector (Kind) then
         return MF_BVs (Kind).BV_Abs;
      else
         raise Not_Implemented;
      end if;
   end New_Abs;

   ------------------
   -- New_Division --
   ------------------

   function New_Division (Kind : W_Type_Id) return W_Identifier_Id is
   begin
      if Kind = EW_Real_Type then
         return M_Floating.Div_Real;
      elsif Kind = EW_Int_Type then
         return M_Int_Div.Div;
      elsif Why_Type_Is_BitVector (Kind) then
         return MF_BVs (Kind).Udiv;
      elsif Kind = EW_Fixed_Type then
         raise Program_Error;
      else
         raise Not_Implemented;
      end if;
   end New_Division;

   -------------
   -- New_Exp --
   -------------

   function New_Exp (Kind : W_Type_Id) return W_Identifier_Id is
   begin
      if Kind = EW_Real_Type then
         return M_Floating.Power;
      elsif Kind = EW_Int_Type then
         return M_Int_Power.Power;
      elsif Why_Type_Is_BitVector (Kind) then
         return MF_BVs (Kind).Power;
      elsif Kind = EW_Fixed_Type then
         raise Program_Error;
      else
         raise Program_Error;
      end if;
   end New_Exp;

   --------------------
   -- New_Identifier --
   --------------------

   function New_Identifier (Ada_Node : Node_Id := Empty;
                            Name     : String;
                            Typ      : W_Type_Id := Why_Empty)
                            return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node, EW_Term, Name, Typ);
   end New_Identifier;

   function New_Identifier
     (Ada_Node  : Node_Id := Empty;
      Name      : String;
      Namespace : Name_Id := No_Name;
      Module    : W_Module_Id;
      Typ       : W_Type_Id := Why_Empty) return W_Identifier_Id is
   begin
      return New_Identifier
        (Ada_Node, EW_Term, Name, Namespace, Module, Typ);
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String;
      Typ      : W_Type_Id := Why_Empty)
     return W_Identifier_Id is
   begin
      return
        New_Identifier
          (Ada_Node => Ada_Node,
           Domain   => Domain,
           Symbol   => NID (Name),
           Typ      => Typ);
   end New_Identifier;

   function New_Identifier
     (Ada_Node  : Node_Id := Empty;
      Domain    : EW_Domain;
      Name      : String;
      Namespace : Name_Id := No_Name;
      Module    : W_Module_Id;
      Typ       : W_Type_Id := Why_Empty)
     return W_Identifier_Id is
   begin
      return
        New_Identifier (Ada_Node  => Ada_Node,
                        Domain    => Domain,
                        Symbol    => NID (Name),
                        Namespace => Namespace,
                        Module    => Module,
                        Typ       => Typ);
   end New_Identifier;

   function New_Identifier (Name : W_Name_Id) return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Get_Ada_Node (+Name),
                             Domain   => EW_Term,
                             Symbol   => Get_Symbol (Name),
                             Module   => Get_Module (Name));
   end New_Identifier;

   ---------
   -- NID --
   ---------

   function NID (Name : String) return Name_Id is
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Name);
      return Name_Find;
   end NID;

   -------------------------
   -- New_Temp_Identifier --
   -------------------------

   New_Temp_Identifier_Counter : Natural := 0;

   function New_Temp_Identifier  return String is
      Counter_Img : constant String :=
                      Natural'Image (New_Temp_Identifier_Counter);
   begin
      New_Temp_Identifier_Counter := New_Temp_Identifier_Counter + 1;
      return
        "temp___" & To_String (New_Temp_Identifier_Suffix) & "_"
        & Counter_Img (Counter_Img'First + 1 .. Counter_Img'Last);
   end New_Temp_Identifier;

   function New_Temp_Identifier
     (Ada_Node : Node_Id := Empty;
      Typ      : W_Type_Id := Why_Empty)
      return W_Identifier_Id is
   begin
      return
        New_Identifier
          (Ada_Node => Ada_Node,
           Name     => New_Temp_Identifier,
           Typ      => Typ);
   end New_Temp_Identifier;

   --------------------------
   -- New_Temp_Identifiers --
   --------------------------

   function New_Temp_Identifiers
     (Num : Positive;
      Typ : W_Type_Id) return W_Identifier_Array
   is
      Result : constant W_Identifier_Array (1 .. Num) :=
                 (others => +New_Temp_Identifier (Typ => Typ));
   begin
      return Result;
   end New_Temp_Identifiers;

   function New_Result_Ident (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return New_Identifier (Name => "result", Typ => Typ);
   end New_Result_Ident;

   -------------------
   -- Remove_Prefix --
   -------------------

   function Remove_Prefix (I : W_Identifier_Id) return W_Identifier_Id is
   begin
      return New_Identifier
        (Ada_Node => Get_Ada_Node (+I),
         Domain   => EW_Term,
         Symbol   => Get_Symbol (I),
         Module   => Why.Types.Why_Empty,
         Typ      => Get_Typ (I));
   end Remove_Prefix;

   --------------
   -- To_Exprs --
   --------------

   function To_Exprs (Ids : W_Identifier_Array) return W_Expr_Array is
      Result : W_Expr_Array (Ids'Range);
   begin
      for J in Result'Range loop
         Result (J) := +Ids (J);
      end loop;

      return Result;
   end To_Exprs;

   ---------------
   -- To_String --
   ---------------

   function To_String (W : Why_Name_Enum) return String
   is
   begin
      case W is
         when WNE_Range_Pred           => return "in_range";
         when WNE_Range_Pred_BV_Int    => return "in_range_int";
         when WNE_Dynamic_Property     => return "dynamic_property";
         when WNE_Dynamic_Property_BV_Int => return "dynamic_property_int";
         when WNE_Index_Dynamic_Property  => return "index_dynamic_property";
         when WNE_To_Int               => return "to_int";
         when WNE_Of_Int               => return "of_int";
         when WNE_To_Fixed             => return "to_fixed";
         when WNE_Of_Fixed             => return "of_fixed";
         when WNE_To_Real              => return "to_real";
         when WNE_Of_Real              => return "of_real";
         when WNE_To_BitVector         => return "to_int";
         when WNE_Of_BitVector         => return "of_int";
         when WNE_To_Array             => return "to_array";
         when WNE_Of_Array             => return "of_array";
         when WNE_To_Base              => return "to_base";
         when WNE_Of_Base              => return "of_base";
         when WNE_To_Rep               => return "to_rep";
         when WNE_Of_Rep               => return "of_rep";
         when WNE_Range_Check_Fun      => return "range_check_";
         when WNE_Range_Check_Fun_BV_Int => return "range_check_int_";
         when WNE_Fixed_Point_Div      => return "fxp_div";
         when WNE_Fixed_Point_Mult     => return "fxp_mult";
         when WNE_Fixed_Point_Div_Int  => return "fxp_div_int";
         when WNE_Fixed_Point_Mult_Int => return "fxp_mult_int";
         when WNE_Float_Round          => return "round_real";
         when WNE_Float_Round_Tmp      => return "round_real_tmp";
         when WNE_Float_Pred           => return "prev_representable";
         when WNE_Float_Succ           => return "next_representable";
         when WNE_Base_Type            => return "base_type";
         when WNE_Array_Elts           => return "elts";
         when WNE_Array_Base_Range_Pred => return "in_range_base";
         when WNE_Array_Component_Type => return "component_type";
         when WNE_Array_Type           => return "__t";
         when WNE_To_String            => return "to_string";
         when WNE_Of_String            => return "from_string";
         when WNE_Bool_Eq              => return "bool_eq";
         when WNE_Dummy                => return "dummy";
         when WNE_Check_Not_First      => return "check_not_first";
         when WNE_Check_Not_Last       => return "check_not_last";
         when WNE_Attr_Constrained     => return "attr__constrained";
         when WNE_Attr_First           => return "first";
         when WNE_Attr_Last            => return "last";
         when WNE_Attr_Length          => return "length";
         when WNE_Attr_Image           =>
            return "attr__" & Attribute_Id'Image (Attribute_Image);
         when WNE_Attr_Modulus         =>
            return "attr__" & Attribute_Id'Image (Attribute_Modulus);
         when WNE_Attr_Small           => return "inv_small";
         when WNE_Attr_Value           =>
            return "attr__" & Attribute_Id'Image (Attribute_Value);
         when WNE_Rec_Split_Discrs     => return "__split_discrs";
         when WNE_Rec_Split_Fields     => return "__split_fields";
         when WNE_Attr_Tag             => return "attr__tag";
         when WNE_Rec_Extension        => return "rec__ext__";
         when WNE_Rec_Extension_Suffix => return "ext__";
         when WNE_Rec_Ancestor_Suffix  => return "anc__";
         when WNE_Rec_Ancestor         => return "rec__anc__";
         when WNE_Rec_Comp_Prefix      => return "rec__";
         when WNE_Extract_Prefix       => return "extract__";
         when WNE_Ancestor_Prefix      => return "extract_anc__";
         when WNE_Hide_Extension       => return "hide_ext__";
         when WNE_Hide_Ancestor        => return "hide_anc__";
         when WNE_Dispatch_Module      => return "Dispatch";
         when WNE_Refine_Module        => return "Refine";
         when WNE_Logic_Fun_Suffix     => return "__logic";
         when WNE_Tag                  => return "__tag";
         when WNE_Attr_Size            => return "attr__size";
      end case;
   end To_String;

   --------------
   -- To_Ident --
   --------------

   function To_Ident (W        : Why_Name_Enum;
                      Ada_Node : Node_Id := Empty)
                      return W_Identifier_Id
   is
   begin
      if No (Ada_Node) then
         if Pre_Computed_Idents (W) /= Why_Empty then
            return Pre_Computed_Idents (W);
         else
            declare
               Id : constant W_Identifier_Id :=
                 New_Identifier (Name => To_String (W));
            begin
               Pre_Computed_Idents (W) := Id;
               return Id;
            end;
         end if;
      else
         return New_Identifier (Ada_Node => Ada_Node, Name => To_String (W));
      end if;
   end To_Ident;

   -------------
   -- To_Name --
   -------------

   function To_Name (W : Why_Name_Enum) return W_Name_Id is
   begin
      return New_Name (Symbol => NID (To_String (W)));
   end To_Name;

   function To_Name (I : W_Identifier_Id) return W_Name_Id is
   begin
      return New_Name
        (Symbol => Get_Symbol (I),
         Ada_Node => Get_Ada_Node (+I),
         Module   => Get_Module (I));
   end To_Name;

   ------------
   -- Prefix --
   ------------

   function Prefix (M        : W_Module_Id;
                    W        : Why_Name_Enum;
                    Ada_Node : Node_Id := Empty;
                    Typ      : W_Type_Id := Why_Empty) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Module   => M,
         Name     => To_String (W),
         Ada_Node => Ada_Node,
         Typ      => Typ);
   end Prefix;

   function Prefix (M        : W_Module_Id;
                    N        : String;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Module => M,
         Name     => N,
         Ada_Node => Ada_Node);
   end Prefix;

   ----------------------
   -- Range_Check_Name --
   ----------------------

   function Range_Check_Name
     (Ty : Entity_Id;
      R  : Range_Check_Kind) return W_Identifier_Id
   is
   begin
      if Is_Standard_Boolean_Type (Ty) then
         case R is
            when RCK_Range_Not_First | RCK_Overflow_Not_First =>
               return M_Boolean.Check_Not_First;
            when RCK_Range_Not_Last | RCK_Overflow_Not_Last =>
               return M_Boolean.Check_Not_First;
            when others =>
               return M_Boolean.Range_Check;
         end case;
      else
         declare
            Name : constant Why_Name_Enum :=
              (case R is
                  when RCK_Range_Not_First | RCK_Overflow_Not_First =>
                     WNE_Check_Not_First,
                  when RCK_Range_Not_Last | RCK_Overflow_Not_Last =>
                     WNE_Check_Not_Last,
                  when others        => WNE_Range_Check_Fun);

         begin
            return Prefix (Ada_Node => Ty,
                           M        => E_Module (Ty),
                           W        => Name);
         end;
      end if;
   end Range_Check_Name;

   ---------------------
   -- Range_Pred_Name --
   ---------------------

   function Range_Pred_Name (Ty : Entity_Id) return W_Identifier_Id
   is
   begin
      if Is_Standard_Boolean_Type (Ty) then
         return Prefix (Ada_Node => Standard_Boolean,
                        M        => M_Boolean.Module,
                        W        => WNE_Range_Pred);
      else
         return Prefix (Ada_Node => Ty,
                        M        => E_Module (Ty),
                        W        => WNE_Range_Pred);
      end if;
   end Range_Pred_Name;

   ----------------------
   -- To_Program_Space --
   ----------------------

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id is
      Suffix : constant String := "_";
      N_Id   : constant Name_Id := Get_Symbol (Name);
      Img    : constant String := Get_Name_String (N_Id);
   begin
      return New_Identifier
        (Get_Ada_Node (+Name), EW_Prog, Img & Suffix,
         Module => Get_Module (Name));
   end To_Program_Space;

   ----------------------
   -- Uint_To_Positive --
   ----------------------

   function Uint_To_Positive (U : Uint) return Positive
   is
   begin
      if U = Uint_1 then
         return 1;
      elsif U = Uint_2 then
         return 2;
      elsif U = Uint_3 then
         return 3;
      elsif U = Uint_4 then
         return 4;
      else
         raise Program_Error;
      end if;
   end Uint_To_Positive;

end Why.Gen.Names;
