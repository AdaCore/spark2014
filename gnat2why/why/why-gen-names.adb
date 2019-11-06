------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

with Ada.Strings.Fixed;   use Ada.Strings.Fixed;
with GNATCOLL.Utils;      use GNATCOLL.Utils;
with Gnat2Why.Util;       use Gnat2Why.Util;
with SPARK_Atree;         use SPARK_Atree;
with SPARK_Util.Types;    use SPARK_Util.Types;
with String_Utils;        use String_Utils;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Images;          use Why.Images;
with Why.Inter;           use Why.Inter;
with Why.Gen.Arrays;      use Why.Gen.Arrays;
with Why.Gen.Scalars;     use Why.Gen.Scalars;

package body Why.Gen.Names is

   Why3_Symbol_Alloc : Symbol_Table_Access;

   function Get_Modular_Converter
     (From, To : W_Type_Id) return W_Identifier_Id;
   --  @param From the BV type to convert from
   --  @param To the BV type to convert to
   --  @return the conversion function from BV From to BV To

   Pre_Computed_Idents : array (Why_Name_Enum) of W_Identifier_Id :=
     (others => Why_Empty);
   --  This array is used to precompute all fixed idents

   function Append_Num (S         : String;
                        Count     : Positive;
                        Namespace : Symbol := No_Symbol;
                        Module    : W_Module_Id := Why.Types.Why_Empty;
                        Typ       : W_Type_Id := Why.Types.Why_Empty;
                        Ada_Node  : Node_Id := Empty)
                        return W_Identifier_Id;

   function Append_Num (S : String; Count : Positive) return String;

   function Convert_From (Kind : W_Type_Id) return Why_Name_Enum;

   --------------------
   -- Address_Append --
   --------------------

   function Address_Append (Base : W_Identifier_Id;
                            Typ  : W_Type_Id) return W_Identifier_Id
   is
      Name : constant W_Name_Id := Get_Name (Base);
   begin
      return
        Append_Num
          (S        => Img (Get_Symb (Name)) & To_String (WNE_Pointer_Address),
           Count    => 1,
           Typ      => Typ,
           Module   => Get_Module (Name),
           Ada_Node => Get_Ada_Node (+Name));
   end Address_Append;

   ----------------
   -- Append_Num --
   ----------------

   function Append_Num (S : String; Count : Positive) return String is
   begin
      return (if Count = 1 then S else S & "_" & Image (Count, 1));
   end Append_Num;

   function Append_Num
     (S         : String;
      Count     : Positive;
      Namespace : Symbol := No_Symbol;
      Module    : W_Module_Id := Why.Types.Why_Empty;
      Typ       : W_Type_Id := Why.Types.Why_Empty;
      Ada_Node  : Node_Id := Empty) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Domain    => EW_Term,
         Name      => Append_Num (S, Count),
         Module    => Module,
         Namespace => Namespace,
         Ada_Node  => Ada_Node,
         Typ       => Typ);
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
                    Module   => Module,
                    Ada_Node => Ada_Node);
   end Attr_Append;

   function Attr_Append (Base  : W_Identifier_Id;
                         A     : Attribute_Id;
                         Count : Positive;
                         Typ   : W_Type_Id) return W_Identifier_Id
   is
      Name : constant W_Name_Id := Get_Name (Base);
   begin
      return
        Attr_Append
          (Img (Get_Symb (Name)),
           A,
           Count,
           Typ,
           Get_Module (Name),
           Get_Ada_Node (+Base));
   end Attr_Append;

   ----------------------
   -- Attr_To_Why_Name --
   ----------------------

   function Attr_To_Why_Name (A : Attribute_Id) return Why_Name_Enum is
     (case A is
         when Attribute_Constrained => WNE_Attr_Constrained,
         when Attribute_First       => WNE_Attr_First,
         when Attribute_Last        => WNE_Attr_Last,
         when Attribute_Tag         => WNE_Attr_Tag,
         when others                => raise Program_Error);

   --------------------
   -- Content_Append --
   --------------------

   function Content_Append (Base : W_Name_Id;
                            Typ  : W_Type_Id) return W_Identifier_Id
   is
   begin
      return
        Append_Num
          (S        => Img (Get_Symb (Base)) & To_String (WNE_Content),
           Count    => 1,
           Typ      => Typ,
           Module   => Get_Module (Base),
           Ada_Node => Get_Ada_Node (+Base));
   end Content_Append;

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
         when EW_Wrapper => raise Program_Error;
         when EW_Builtin =>
            case To_Kind is
               when EW_Wrapper => raise Program_Error;
               when EW_Builtin =>

                  --  Only certain conversions are OK

                  if From = EW_Int_Type and then Why_Type_Is_Float (To) then
                     return MF_Floats (To).Of_Int;

                  --  Conversions from real to int in Ada round to the nearest
                  --  integer, and away from zero in case of tie, exactly like
                  --  'Rounding attribute.

                  elsif Why_Type_Is_Float (From) then
                     return (if To = EW_Int_Type then
                                MF_Floats (From).To_Int
                             elsif To = EW_BitVector_8_Type then
                                MF_Floats (From).To_BV8
                             elsif To = EW_BitVector_16_Type then
                                MF_Floats (From).To_BV16
                             elsif To = EW_BitVector_32_Type then
                                MF_Floats (From).To_BV32
                             elsif To = EW_BitVector_64_Type then
                                MF_Floats (From).To_BV64
                             elsif To = EW_Float_32_Type then
                                M_Floating_Conv.To_Float32
                             elsif To = EW_Float_64_Type then
                                M_Floating_Conv.To_Float64
                             else
                                raise Program_Error);
                  elsif From = EW_Bool_Type and then To = EW_Int_Type then
                     return M_Boolean.To_Int;
                  elsif From = EW_Int_Type and then To = EW_Bool_Type then
                     return M_Boolean.Of_Int;
                  elsif Why_Type_Is_BitVector (From)
                    and then To = EW_Int_Type
                  then
                     return MF_BVs (From).To_Int;

                  elsif Why_Type_Is_BitVector (From) and then
                    Why_Type_Is_Float (To)
                  then
                     return (if From = EW_BitVector_8_Type then
                                MF_Floats (To).Of_BV8
                             elsif From = EW_BitVector_16_Type then
                                MF_Floats (To).Of_BV16
                             elsif From = EW_BitVector_32_Type then
                                MF_Floats (To).Of_BV32
                             elsif From = EW_BitVector_64_Type then
                                MF_Floats (To).Of_BV64
                             else raise Program_Error);

                  elsif From = EW_Int_Type
                    and then Why_Type_Is_BitVector (To)
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

                  --  For fixed point types, get the underlying fixed point
                  --  theory.

                  elsif Why_Type_Is_Fixed (From) and then To = EW_Int_Type then
                     return
                       Get_Fixed_Point_Theory (Get_Ada_Node (+From)).To_Int;
                  elsif From = EW_Int_Type and then Why_Type_Is_Fixed (To) then
                     return
                       Get_Fixed_Point_Theory (Get_Ada_Node (+To)).Of_Int;
                  else
                     raise Program_Error;
                  end if;

               when EW_Abstract
                  | EW_Split
               =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+To);
                  begin
                     if Base_Why_Type (To) = From and then
                       (From = EW_Int_Type
                        or else Why_Type_Is_BitVector (From)
                        or else Why_Type_Is_Float (From)
                        or else Why_Type_Is_Fixed (From))
                     then
                        --  if we're converting from the representation type
                        --  of a scalar kind
                        return E_Symb (A, WNE_Of_Rep);
                     else
                        return E_Symb (A, Convert_From (From));
                     end if;
                  end;
            end case;

         when EW_Abstract
            | EW_Split
         =>
            case To_Kind is
               when EW_Wrapper => raise Program_Error;
               when EW_Builtin =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+From);
                  begin
                     if Base_Why_Type (From) = To and then
                       (To = EW_Int_Type
                        or else Why_Type_Is_BitVector (To)
                        or else Why_Type_Is_Float (To)
                        or else Why_Type_Is_Fixed (To))
                     then
                        --  if we're converting to the representation type
                        --  of a discrete/float kind
                        return E_Symb (A, WNE_To_Rep);
                     else
                        if To = EW_Int_Type then
                           return E_Symb (A, WNE_To_Int);
                        elsif Why_Type_Is_Fixed (To) then
                           return E_Symb (A, WNE_To_Fixed);
                        elsif To = EW_Float_32_Type then
                           return E_Symb (A, WNE_To_Float32);
                        elsif To = EW_Float_64_Type then
                           return E_Symb (A, WNE_To_Float64);
                        elsif Why_Type_Is_BitVector (To) then
                           return E_Symb (A, WNE_To_BitVector);
                        else
                           raise Program_Error;
                        end if;
                     end if;
                  end;

               --  Case of a conversion between two record or array types

               when EW_Abstract
                  | EW_Split
               =>
                  declare
                     From_Node : constant Node_Id := Get_Ada_Node (+From);
                     To_Node   : constant Node_Id := Get_Ada_Node (+To);

                  begin
                     --  Conversions on record types go through the root type

                     if Is_Record_Type_In_Why (From_Node) then
                        pragma Assert (Is_Record_Type_In_Why (To_Node));
                        declare
                           From_Base : constant Node_Id :=
                             Root_Retysp (From_Node);
                        begin
                           if From_Base = From_Node then
                              return E_Symb (To_Node, WNE_Of_Base);
                           else
                              return E_Symb (From_Node, WNE_To_Base);
                           end if;
                        end;

                     --  Conversions on array types use predefined functions

                     else
                        pragma Assert (Has_Array_Type (From_Node)
                                       and Has_Array_Type (To_Node));
                        return Get_Array_Conversion_Name (From_Node, To_Node);
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
      elsif Why_Type_Is_Fixed (Kind) then
         return WNE_Of_Fixed;
      elsif Kind = EW_Float_32_Type then
         return WNE_Of_Float32;
      elsif Kind = EW_Float_64_Type then
         return WNE_Of_Float64;
      elsif Why_Type_Is_BitVector (Kind) then
         return WNE_Of_BitVector;
      elsif Kind = EW_Real_Type then
         return WNE_Of_Real;
      else
         raise Why.Not_Implemented;
      end if;
   end Convert_From;

   ------------------
   -- Discr_Append --
   ------------------

   function Discr_Append (Base  : W_Identifier_Id;
                          Typ   : W_Type_Id) return W_Identifier_Id
   is
      Name : constant W_Name_Id := Get_Name (Base);
   begin
      return
        Append_Num
          (S        => Img (Get_Symb (Name)) &
             To_String (WNE_Rec_Split_Discrs),
           Count    => 1,
           Typ      => Typ,
           Module   => Get_Module (Name),
           Ada_Node => Get_Ada_Node (+Name));
   end Discr_Append;

   -----------------------
   -- Dynamic_Prop_Name --
   -----------------------

   function Dynamic_Prop_Name (Ty : Entity_Id) return W_Identifier_Id
   is
   begin
      if Is_Standard_Boolean_Type (Ty) then
         return M_Boolean.Dynamic_Prop;
      else
         return E_Symb (Ty, WNE_Dynamic_Property);
      end if;
   end Dynamic_Prop_Name;

   ------------------
   -- Field_Append --
   ------------------

   function Field_Append (Base  : W_Identifier_Id;
                          Typ   : W_Type_Id) return W_Identifier_Id
   is
      Name : constant W_Name_Id := Get_Name (Base);
   begin
      return
        Append_Num
          (S        => Img (Get_Symb (Name))
           & To_String (WNE_Rec_Split_Fields),
           Count    => 1,
           Typ      => Typ,
           Module   => Get_Module (Name),
           Ada_Node => Get_Ada_Node (+Name));
   end Field_Append;

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

   ---------------------------------------
   -- Get_Modular_Converter_Range_Check --
   ---------------------------------------

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

   ------------------
   -- Havoc_Append --
   ------------------

   function Havoc_Append (Base : W_Name_Id) return W_Identifier_Id
   is
   begin
      return
        Append_Num
          (S        => Img (Get_Symb (Base)) & To_String (WNE_Havoc),
           Count    => 1,
           Typ      => Why_Empty,
           Module   => Get_Module (Base),
           Ada_Node => Get_Ada_Node (+Base));
   end Havoc_Append;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin
      Why3_Symbol_Alloc := Allocate;
   end Initialize;

   -----------------
   -- Init_Append --
   -----------------

   function Init_Append (Base : W_Identifier_Id) return W_Identifier_Id is
      Name : constant W_Name_Id := Get_Name (Base);
   begin
      return
        Append_Num
          (S        => Img (Get_Symb (Name)) & To_String (WNE_Attr_Init),
           Count    => 1,
           Typ      => EW_Bool_Type,
           Module   => Get_Module (Name),
           Ada_Node => Get_Ada_Node (+Name));
   end Init_Append;

   --------------------
   -- Is_Null_Append --
   --------------------

   function Is_Null_Append (Base : W_Identifier_Id;
                            Typ  : W_Type_Id) return W_Identifier_Id
   is
      Name : constant W_Name_Id := Get_Name (Base);
   begin
      return
        Append_Num
          (S        => Img (Get_Symb (Name)) & To_String (WNE_Is_Null_Pointer),
           Count    => 1,
           Typ      => Typ,
           Module   => Get_Module (Name),
           Ada_Node => Get_Ada_Node (+Name));
   end Is_Null_Append;

   -------------
   -- New_Abs --
   -------------

   function New_Abs (Kind : W_Type_Id) return W_Identifier_Id is
   begin
      if Why_Type_Is_Float (Kind) then
         return MF_Floats (Kind).Abs_Float;
      elsif Kind = EW_Int_Type or else Why_Type_Is_Fixed (Kind) then
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
      if Why_Type_Is_Float (Kind) then
         return MF_Floats (Kind).Div;
      elsif Kind = EW_Int_Type then
         return M_Int_Div.Div;
      elsif Why_Type_Is_BitVector (Kind) then
         return MF_BVs (Kind).Udiv;
      elsif Why_Type_Is_Fixed (Kind) then
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
      if Why_Type_Is_Float (Kind) then
         return MF_Floats (Kind).Power;
      elsif Kind = EW_Int_Type then
         return M_Int_Power.Power;
      elsif Why_Type_Is_BitVector (Kind) then
         return MF_BVs (Kind).Power;
      elsif Why_Type_Is_Fixed (Kind) then
         raise Program_Error;
      else
         raise Program_Error;
      end if;
   end New_Exp;

   --------------------
   -- New_Identifier --
   --------------------

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Name     : String;
      Typ      : W_Type_Id := Why.Types.Why_Empty;
      Attrs    : Common_Containers.String_Sets.Set :=
        Common_Containers.String_Sets.Empty_Set)
      return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node, EW_Term, Name, Typ, Attrs);
   end New_Identifier;

   function New_Identifier
     (Ada_Node  : Node_Id := Empty;
      Name      : String;
      Namespace : Symbol := No_Symbol;
      Module    : W_Module_Id;
      Typ       : W_Type_Id := Why_Empty;
      Attrs     : Common_Containers.String_Sets.Set :=
        Common_Containers.String_Sets.Empty_Set)
      return W_Identifier_Id is
   begin
      return New_Identifier
        (Ada_Node, EW_Term, Name, Namespace, Module, Typ, Attrs);
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String;
      Typ      : W_Type_Id := Why_Empty;
      Attrs    : Common_Containers.String_Sets.Set :=
        Common_Containers.String_Sets.Empty_Set)
      return W_Identifier_Id is
   begin
      return
        New_Identifier
          (Ada_Node => Ada_Node,
           Domain   => Domain,
           Symb     => NID (Name),
           Typ      => Typ,
           Attrs    => Attrs);
   end New_Identifier;

   function New_Identifier
     (Ada_Node  : Node_Id := Empty;
      Domain    : EW_Domain;
      Name      : String;
      Namespace : Symbol := No_Symbol;
      Module    : W_Module_Id;
      Typ       : W_Type_Id := Why_Empty;
      Attrs     : Common_Containers.String_Sets.Set :=
        Common_Containers.String_Sets.Empty_Set)
      return W_Identifier_Id is
   begin
      return
        New_Identifier (Ada_Node  => Ada_Node,
                        Domain    => Domain,
                        Symb      => NID (Name),
                        Namespace => Namespace,
                        Module    => Module,
                        Typ       => Typ,
                        Attrs     => Attrs);
   end New_Identifier;

   function New_Identifier (Name : W_Name_Id) return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Get_Ada_Node (+Name),
                             Domain   => EW_Term,
                             Symb     => Get_Symb (Name),
                             Module   => Get_Module (Name));
   end New_Identifier;

   function New_Identifier
     (Ada_Node  : Node_Id := Empty;
      Domain    : EW_Domain;
      Symb      : Symbol;
      Namespace : Symbol := No_Symbol;
      Typ       : W_Type_Id := Why.Types.Why_Empty;
      Module    : W_Module_Id := Why.Types.Why_Empty;
      Infix     : Boolean := False;
      Attrs     : Common_Containers.String_Sets.Set :=
        Common_Containers.String_Sets.Empty_Set)
      return W_Identifier_Id is
   begin
      return
        New_Identifier (Ada_Node => Ada_Node,
                        Domain   => Domain,
                        Name     => New_Name (Ada_Node  => Ada_Node,
                                              Symb      => Symb,
                                              Namespace => Namespace,
                                              Infix     => Infix,
                                              Module    => Module),
                        Typ      => Typ,
                        Labels   => Attrs);
   end New_Identifier;

   ---------
   -- NID --
   ---------

   function NID (Name : String) return Symbol is
   begin
      return Find (Why3_Symbol_Alloc, Name);
   end NID;

   ----------------
   -- New_Module --
   ----------------

   function New_Module
     (Ada_Node : Node_Id := Empty;
      File     : Symbol;
      Name     : String)
      return W_Module_Id
   is
      S : constant Symbol := NID (Capitalize_First (Name));
   begin
      return New_Module (Ada_Node, File, S);
   end New_Module;

   -------------------------
   -- New_Temp_Identifier --
   -------------------------

   New_Temp_Identifier_Counter : Natural := 0;

   function New_Temp_Identifier (Base_Name : String := "") return String is
      Counter_Img : constant String :=
        Natural'Image (New_Temp_Identifier_Counter);
      Use_Base_Name : constant String :=
        (if Base_Name = "" then "" else Base_Name & "_");
   begin
      New_Temp_Identifier_Counter := New_Temp_Identifier_Counter + 1;
      return "temp___" & Use_Base_Name & Trim (Counter_Img, Ada.Strings.Left);
   end New_Temp_Identifier;

   function New_Temp_Identifier
     (Ada_Node  : Node_Id   := Empty;
      Typ       : W_Type_Id := Why_Empty;
      Base_Name : String    := "") return W_Identifier_Id is

      Temp_Labels : Common_Containers.String_Sets.Set :=
        Common_Containers.String_Sets.Empty_Set;
   begin
      Common_Containers.String_Sets.Insert (Container => Temp_Labels,
                                            New_Item  => "mlw:proxy_symbol");
      Common_Containers.String_Sets.Insert (Temp_Labels, "introduced");
      return New_Identifier (Ada_Node => Ada_Node,
                             Name     => New_Temp_Identifier (Base_Name),
                             Typ      => Typ,
                             Attrs    => Temp_Labels);
   end New_Temp_Identifier;

   function New_Generated_Identifier
     (Ada_Node  : Node_Id   := Empty;
      Typ       : W_Type_Id := Why_Empty;
      Base_Name : String    := "";
      Attrs     : Common_Containers.String_Sets.Set) return W_Identifier_Id is

   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Name     => New_Temp_Identifier (Base_Name),
                             Typ      => Typ,
                             Attrs    => Attrs);
   end New_Generated_Identifier;

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

   ----------------------
   -- New_Result_Ident --
   ----------------------

   function New_Result_Ident (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return New_Identifier (Name => "result", Typ => Typ);
   end New_Result_Ident;

   ----------------
   -- Ref_Append --
   ----------------

   function Ref_Append (Base : W_Name_Id) return W_Name_Id is
   begin
      return
        New_Name
          (Ada_Node => Get_Ada_Node (+Base),
           Symb     => NID (Img (Get_Symb (Base)) & To_String (WNE_Ref)),
           Module   => Get_Module (Base));
   end Ref_Append;

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

   function To_String (W : Why_Name_Enum) return String is
     (case W is
         when WNE_Aggregate_Def_Suffix       => "__aggregate_def",
         when WNE_Array_Component_Type       => "component_type",
         when WNE_Array_Type                 => "__t",
         when WNE_Array_BV_Suffix            => "_BV",
         when WNE_Array_Comparison_Suffix    => "_Comp",
         when WNE_Array_Concatenation_Suffix => "__Concat",
         when WNE_Array_Int_Suffix           => "_Int",
         when WNE_Array_Logical_Op_Suffix    => "__Bool_Op",
         when WNE_Array_Prefix               => "Array_",

         when WNE_Attr_Constrained           => "attr__constrained",
         when WNE_Attr_First                 => "first",
         when WNE_Attr_Last                  => "last",
         when WNE_Attr_Tag                   => "attr__tag",
         when WNE_Axiom_Suffix               => "___axiom",
         when WNE_Content                    => "__content",
         when WNE_Dispatch_Module            => "Dispatch",
         when WNE_Extract_Prefix             => "extract__",
         when WNE_Fixed_Point_Prefix         => "Fixed_Point",
         when WNE_Fixed_Point_Mult_Div_Prefix => "Fixed_Point_Mult_Div",
         when WNE_Havoc                      => "__havoc",
         when WNE_Hide_Extension             => "hide_ext__",
         when WNE_No_Return_Module           => "No_Return",
         when WNE_Rec_Rep                    => "__rep",
         when WNE_Rec_Comp_Prefix            => "rec__",
         when WNE_Rec_Extension_Suffix       => "ext__",
         when WNE_Refine_Module              => "Refine",
         when WNE_Ref                        => "__ref",

         --  these are used both by E_Symb function and by To_String

         when WNE_Attr_Init          => "__attr__init",
         when WNE_Rec_Split_Discrs   => "__split_discrs",
         when WNE_Rec_Split_Fields   => "__split_fields",
         when WNE_Null_Exclusion_Val => "__null_exclusion_val",
         when WNE_Null_Pointer       => "__null_pointer",
         when WNE_Is_Null_Pointer    => "__is_null_pointer",
         when WNE_Pointer_Address    => "__pointer_address",
         when WNE_Pointer_Value      => "__pointer_value",
         when WNE_Init_Allocator     => "__new_initialized_allocator",
         when WNE_Uninit_Allocator   => "__new_uninitialized_allocator",

         --  please use these only in conjunction with E_Symb function

         when WNE_Array_Base_Range_Pred
            | WNE_Array_Base_Range_Pred_2
            | WNE_Array_Base_Range_Pred_3
            | WNE_Array_Base_Range_Pred_4
            | WNE_Array_Elts
            | WNE_Assign_Null_Check
            | WNE_Attr_Address
            | WNE_Attr_Alignment
            | WNE_Attr_Component_Size
            | WNE_Attr_First_2
            | WNE_Attr_First_3
            | WNE_Attr_First_4
            | WNE_Attr_First_Bit
            | WNE_Attr_Image
            | WNE_Attr_Last_2
            | WNE_Attr_Last_3
            | WNE_Attr_Last_4
            | WNE_Attr_Last_Bit
            | WNE_Attr_Length
            | WNE_Attr_Length_2
            | WNE_Attr_Length_3
            | WNE_Attr_Length_4
            | WNE_Attr_Modulus
            | WNE_Attr_Object_Size
            | WNE_Attr_Position
            | WNE_Attr_Value
            | WNE_Attr_Value_Size
            | WNE_Bool_Eq
            | WNE_Check_Invariants_On_Call
            | WNE_Check_Not_First
            | WNE_Check_Not_Last
            | WNE_Default_Init
            | WNE_Dispatch_Eq
            | WNE_Dispatch_Func_Guard
            | WNE_Dummy
            | WNE_Dynamic_Invariant
            | WNE_Dynamic_Predicate
            | WNE_Dynamic_Property
            | WNE_Dynamic_Property_BV_Int
            | WNE_Fixed_Point_Div
            | WNE_Fixed_Point_Div_Int
            | WNE_Fixed_Point_Mult
            | WNE_Fixed_Point_Mult_Int
            | WNE_Func_Guard
            | WNE_Index_Dynamic_Property
            | WNE_Index_Dynamic_Property_2
            | WNE_Index_Dynamic_Property_3
            | WNE_Index_Dynamic_Property_4
            | WNE_Init_Value
            | WNE_Int_Proj
            | WNE_Of_Array
            | WNE_Of_Base
            | WNE_Of_BitVector
            | WNE_Of_Fixed
            | WNE_Of_Float32
            | WNE_Of_Float64
            | WNE_Of_Int
            | WNE_Of_Real
            | WNE_Of_Rep
            | WNE_Private_Eq
            | WNE_Private_Type
            | WNE_Pointer_Close
            | WNE_Pointer_Open
            | WNE_Pointer_Value_Abstr
            | WNE_Pos_To_Rep
            | WNE_Refined_Func_Guard
            | WNE_Range_Check_Fun
            | WNE_Range_Check_Fun_BV_Int
            | WNE_Range_Pred
            | WNE_Range_Pred_BV_Int
            | WNE_Rec_Extension
            | WNE_Small_Den
            | WNE_Small_Num
            | WNE_Specific_Post
            | WNE_Tag
            | WNE_To_Array
            | WNE_To_Base
            | WNE_To_BitVector
            | WNE_To_Fixed
            | WNE_To_Float32
            | WNE_To_Float64
            | WNE_To_Int
            | WNE_To_Int_2
            | WNE_To_Int_3
            | WNE_To_Int_4
            | WNE_To_Rep
            | WNE_Type_Invariant
            | WNE_Empty
         =>
            raise Program_Error);

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

   --------------
   -- To_Local --
   --------------

   function To_Local (Name : W_Identifier_Id) return W_Name_Id
   is
      W_Name : constant W_Name_Id := Get_Name (Name);
   begin
      return New_Name (Ada_Node => Get_Ada_Node (+W_Name),
                       Symb     => Get_Symb (W_Name),
                       Module   => Why_Empty);
   end To_Local;

   function To_Local (Name : W_Identifier_Id) return W_Identifier_Id
   is
      W_Name : constant W_Name_Id := Get_Name (Name);
   begin
      return
        New_Identifier
          (Ada_Node  => Get_Ada_Node (+W_Name),
           Symb      => Get_Symb (W_Name),
           Namespace => Get_Namespace (W_Name),
           Domain    => Get_Domain (+Name),
           Module    => Why_Empty,
           Typ       => Get_Typ (Name),
           Attrs     => Get_Labels (Name));
   end To_Local;

   function To_Local (Name : W_Name_Id) return W_Name_Id is
   begin
      return New_Name (Ada_Node => Get_Ada_Node (+Name),
                       Symb     => Get_Symb (Name),
                       Module   => Why_Empty);
   end To_Local;

   -------------
   -- To_Name --
   -------------

   function To_Name (W : Why_Name_Enum) return W_Name_Id is
   begin
      return New_Name (Symb => NID (To_String (W)));
   end To_Name;

   ----------------------
   -- Range_Check_Name --
   ----------------------

   function Range_Check_Name
     (Ty : Entity_Id; R : Scalar_Check_Kind) return W_Identifier_Id
   is
   begin
      if Is_Standard_Boolean_Type (Ty) then
         case R is
            when RCK_Range_Not_First
               | RCK_Overflow_Not_First
            =>
               return M_Boolean.Check_Not_First;

            when RCK_Range_Not_Last
               | RCK_Overflow_Not_Last
            =>
               return M_Boolean.Check_Not_Last;

            when others =>
               return M_Boolean.Range_Check;
         end case;
      else
         declare
            Name : constant Why_Name_Enum :=
              (case R is
                  when RCK_Range_Not_First
                     | RCK_Overflow_Not_First
                  =>
                     WNE_Check_Not_First,
                  when RCK_Range_Not_Last
                     | RCK_Overflow_Not_Last
                  =>
                     WNE_Check_Not_Last,
                  when others =>
                     WNE_Range_Check_Fun);

         begin
            return E_Symb (Ty, Name);
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
         return M_Boolean.Range_Pred;
      else
         return E_Symb (Ty, WNE_Range_Pred);
      end if;
   end Range_Pred_Name;

   ----------------------
   -- To_Program_Space --
   ----------------------

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id is
      Suffix : constant String := "_";
      N_Id   : constant Symbol := Get_Symb (Get_Name (Name));
      Img    : String renames Get (N_Id).all;
   begin
      return New_Identifier
        (Get_Ada_Node (+Name), EW_Prog, Img & Suffix,
         Module => Get_Module (Get_Name (Name)));
   end To_Program_Space;

   ----------------------
   -- Value_Append --
   ----------------------

   function Value_Append (Base : W_Identifier_Id;
                          Typ  : W_Type_Id) return W_Identifier_Id
   is
      Name : constant W_Name_Id := Get_Name (Base);
   begin
      return
        Append_Num
          (S        => Img (Get_Symb (Name))
           & To_String (WNE_Pointer_Value),
           Count    => 1,
           Typ      => Typ,
           Module   => Get_Module (Name),
           Ada_Node => Get_Ada_Node (+Name));
   end Value_Append;

   -------------------------------
   -- WNE_Array_Base_Range_Pred --
   -------------------------------

   function WNE_Array_Base_Range_Pred (I : Integer) return Why_Name_Enum is
     (case I is
         when 1 => WNE_Array_Base_Range_Pred,
         when 2 => WNE_Array_Base_Range_Pred_2,
         when 3 => WNE_Array_Base_Range_Pred_3,
         when 4 => WNE_Array_Base_Range_Pred_4,
         when others => raise Program_Error);

   --------------------
   -- WNE_Attr_First --
   --------------------

   function WNE_Attr_First (I : Integer) return Why_Name_Enum is
     (case I is
         when 1 => WNE_Attr_First,
         when 2 => WNE_Attr_First_2,
         when 3 => WNE_Attr_First_3,
         when 4 => WNE_Attr_First_4,
         when others => raise Program_Error);

   -------------------
   -- WNE_Attr_Last --
   -------------------

   function WNE_Attr_Last (I : Integer) return Why_Name_Enum is
     (case I is
         when 1 => WNE_Attr_Last,
         when 2 => WNE_Attr_Last_2,
         when 3 => WNE_Attr_Last_3,
         when 4 => WNE_Attr_Last_4,
         when others => raise Program_Error);

   ---------------------
   -- WNE_Attr_Length --
   ---------------------

   function WNE_Attr_Length (I : Integer) return Why_Name_Enum is
     (case I is
         when 1 => WNE_Attr_Length,
         when 2 => WNE_Attr_Length_2,
         when 3 => WNE_Attr_Length_3,
         when 4 => WNE_Attr_Length_4,
         when others => raise Program_Error);

   --------------------------------
   -- WNE_Index_Dynamic_Property --
   --------------------------------

   function WNE_Index_Dynamic_Property (I : Integer) return Why_Name_Enum is
     (case I is
         when 1 => WNE_Index_Dynamic_Property,
         when 2 => WNE_Index_Dynamic_Property_2,
         when 3 => WNE_Index_Dynamic_Property_3,
         when 4 => WNE_Index_Dynamic_Property_4,
         when others => raise Program_Error);

   ----------------
   -- WNE_To_Int --
   ----------------

   function WNE_To_Int (I : Integer) return Why_Name_Enum is
     (case I is
         when 1 => WNE_To_Int,
         when 2 => WNE_To_Int_2,
         when 3 => WNE_To_Int_3,
         when 4 => WNE_To_Int_4,
         when others => raise Program_Error);

end Why.Gen.Names;
