------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Ada.Containers.Hashed_Maps;
with Ada.Strings.Unbounded.Hash;

with Atree;              use Atree;
with Lib;                use Lib;
with Sinput;             use Sinput;
with Stand;              use Stand;
with String_Utils;       use String_Utils;

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Conversions;    use Why.Conversions;
with Why.Inter;          use Why.Inter;
with Why.Types;          use Why.Types;

package body Why.Gen.Names is

   package String_Int_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Unbounded_String,
        Element_Type    => Positive,
        Equivalent_Keys => "=",
        "="             => "=",
        Hash            => Ada.Strings.Unbounded.Hash);

   function Source_Ptr_Hash (X : Source_Ptr) return Ada.Containers.Hash_Type;

   ---------------------
   -- Source_Ptr_Hash --
   ---------------------

   function Source_Ptr_Hash (X : Source_Ptr) return Ada.Containers.Hash_Type is
   begin
      return Ada.Containers.Hash_Type (X);
   end Source_Ptr_Hash;

   package Loc_String_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Source_Ptr,
        Element_Type    => Unbounded_String,
        Equivalent_Keys => "=",
        Hash            => Source_Ptr_Hash,
        "="             => "=");

   Unit_Loc_Map : String_Int_Maps.Map := String_Int_Maps.Empty_Map;
   File_Loc_Map : Loc_String_Maps.Map := Loc_String_Maps.Empty_Map;

   function Uint_To_Positive (U : Uint) return Positive;
   --  Limited version of conversion that only works for 1 and 2

   Pre_Computed_Idents : array (Why_Name_Enum) of W_Identifier_Id :=
     (others => Why_Empty);
   --  This array is used to precompute all fixed idents.

   --------------------
   -- Ada_Array_Name --
   --------------------

   function Ada_Array_Name (Dimension : Pos) return Why_Name_Enum
   is
   begin
      case Dimension is
         when 1 => return WNE_Array_1;
         when 2 => return WNE_Array_2;
         when others => raise Program_Error;
      end case;
   end Ada_Array_Name;

   ----------------------
   -- Append_Num --
   ----------------------

   function Append_Num (S : String; Count : Positive) return W_Identifier_Id
   is
   begin
      if Count = 1 then
         return New_Identifier (Name => S);
      else
         return New_Identifier (Name => S & "_" & Int_Image (Count));
      end if;
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

   ----------------------
   -- Attr_To_Why_Name --
   ----------------------

   function Attr_To_Why_Name (A : Attribute_Id) return Why_Name_Enum
   is
   begin
      case A is
         when Attribute_First   => return WNE_Attr_First;
         when Attribute_Image   => return WNE_Attr_Image;
         when Attribute_Last    => return WNE_Attr_Last;
         when Attribute_Modulus => return WNE_Attr_Modulus;
         when Attribute_Length  => return WNE_Attr_Length;
         when Attribute_Value   => return WNE_Attr_Value;
         when others =>
            raise Program_Error;
      end case;
   end Attr_To_Why_Name;

   function Attr_To_Why_Name (A     : Attribute_Id;
                              Dim   : Pos;
                              Count : Positive) return W_Identifier_Id
   is
      Attr_Name : constant String :=
        (if Count = 1 then To_String (Attr_To_Why_Name (A))
         else To_String (Attr_To_Why_Name (A)) & "_" & Int_Image (Count));
   begin
      return
        New_Identifier (Name =>
                          To_String (Ada_Array_Name (Dim)) & "." & Attr_Name);
   end Attr_To_Why_Name;

   function Attr_To_Why_Name (A     : Attribute_Id;
                              Dim   : Pos;
                              Count : Uint) return W_Identifier_Id is
      C : constant Positive := Uint_To_Positive (Count);
   begin
      return Attr_To_Why_Name (A, Dim, C);
   end Attr_To_Why_Name;

   ---------------------
   -- Conversion_Name --
   ---------------------

   function Conversion_Name
      (From : W_Base_Type_Id;
       To   : W_Base_Type_Id) return W_Identifier_Id
   is
      From_Kind : constant EW_Type := Get_Base_Type (From);
      To_Kind   : constant EW_Type := Get_Base_Type (To);
   begin
      case From_Kind is
         when EW_Unit | EW_Prop | EW_Private =>
            raise Not_Implemented;

         when EW_Scalar =>
            case To_Kind is
               when EW_Unit | EW_Prop | EW_Array | EW_Private =>
                  raise Not_Implemented;

               when EW_Scalar =>

                  --  Only certain conversions are OK

                  if From_Kind = EW_Int and then To_Kind = EW_Real then
                     return To_Ident (WNE_Real_Of_Int);

                  --  Conversions from int to real in Ada round to the nearest
                  --  integer, and away from zero in case of tie, exactly like
                  --  'Rounding attribute.

                  elsif From_Kind = EW_Real and then To_Kind = EW_Int then
                     return To_Ident (WNE_Real_Round);
                  elsif From_Kind = EW_Bool and then To_Kind = EW_Int then
                     return Prefix (Ada_Node => Standard_Boolean,
                                    S        => "Boolean",
                                    W        => WNE_To_Int);
                  elsif From_Kind = EW_Int and then To_Kind = EW_Bool then
                     return Prefix (Ada_Node => Standard_Boolean,
                                    S        => "Boolean",
                                    W        => WNE_Of_Int);

                  --  Either the two objects are of the same type
                  --  (in which case the conversion is useless) or
                  --  they are of incompatible types
                  --  In both cases, it is an error.

                  else
                     raise Program_Error;
                  end if;

               when EW_Abstract =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+To);
                  begin
                     return
                       Prefix (Ada_Node => A,
                               S        => Full_Name (A),
                               W        => Convert_From (From_Kind));
                  end;
            end case;

         when EW_Array =>
            pragma Assert (To_Kind = EW_Abstract);
            declare
               A : constant Node_Id := Get_Ada_Node (+To);
            begin
               return
                 Prefix (Ada_Node => A, S => Full_Name (A), W => WNE_Of_Array);
            end;

         when EW_Abstract =>
            case To_Kind is
               when EW_Unit | EW_Prop | EW_Private =>
                  raise Not_Implemented;

               when EW_Scalar =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+From);
                  begin
                     return
                       Prefix (Ada_Node => A,
                               S => Full_Name (A),
                               W => Convert_To (To_Kind));
                  end;
               when EW_Array =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+From);
                  begin
                     return
                       Prefix (Ada_Node => A,
                               S        => Full_Name (A),
                               W        => WNE_To_Array);
                  end;

               when EW_Abstract =>
                  raise Program_Error
                     with "Conversion between arbitrary types attempted";
            end case;
      end case;
   end Conversion_Name;

   ------------------
   -- Convert_From --
   ------------------

   function Convert_From (Kind : EW_Basic_Type) return Why_Name_Enum
   is
   begin
      case Kind is
         when EW_Int => return WNE_Of_Int;
         when EW_Real => return WNE_Of_Real;
         when others =>
            raise Program_Error;
      end case;
   end Convert_From;

   ----------------
   -- Convert_To --
   ----------------

   function Convert_To (Kind : EW_Basic_Type) return Why_Name_Enum
   is
   begin
      case Kind is
         when EW_Int => return WNE_To_Int;
         when EW_Real => return WNE_To_Real;
         when others =>
            raise Program_Error;
      end case;
   end Convert_To;

   -----------------------
   -- EW_Base_Type_Name --
   -----------------------

   function EW_Base_Type_Name (Kind : EW_Basic_Type) return String is
   begin
      case Kind is
         when EW_Unit =>
            return "unit";
         when EW_Prop =>
            return "prop";
         when EW_Real =>
            return "real";
         when EW_Int =>
            return "int";
         when EW_Bool =>
            return "bool";
      end case;
   end EW_Base_Type_Name;

   -------------
   -- New_Abs --
   -------------

   function New_Abs (Kind : EW_Numeric) return W_Identifier_Id is
   begin
      case Kind is
         when EW_Real =>
            return To_Ident (WNE_Real_Abs);
         when EW_Int =>
            return To_Ident (WNE_Integer_Abs);
      end case;
   end New_Abs;

   ------------------
   -- New_Bool_Cmp --
   ------------------

   function New_Bool_Cmp
     (Rel       : EW_Relation;
      Arg_Types : W_Base_Type_Id) return W_Identifier_Id
   is
      Kind : constant EW_Type := Get_Base_Type (Arg_Types);
      A    : constant Node_Id :=
        (if Kind = EW_Abstract then Get_Ada_Node (+Arg_Types)
         else Empty);
      R : constant Why_Name_Enum :=
        (case Rel is
         when EW_Eq   => WNE_Bool_Eq,
         when EW_Ne   => WNE_Bool_Ne,
         when EW_Le   => WNE_Bool_Le,
         when EW_Lt   => WNE_Bool_Lt,
         when EW_Gt   => WNE_Bool_Gt,
         when EW_Ge   => WNE_Bool_Ge,
         when EW_None => WNE_Bool_Eq
        );
      S : constant String :=
        (case Kind is
         when EW_Int  => "Integer",
         when EW_Real => "Floating",
         when EW_Bool => "Boolean",
         when EW_Unit .. EW_Prop | EW_Array | EW_Private => "Main",
         when EW_Abstract => Full_Name (Get_Ada_Node (+Arg_Types)));
   begin
      return Prefix (Ada_Node => A,
                     S        => S,
                     W        => R);
   end New_Bool_Cmp;

   ------------------
   -- New_Division --
   ------------------

   function New_Division (Kind : EW_Numeric) return W_Identifier_Id is
   begin
      case Kind is
         when EW_Real =>
            return To_Ident (WNE_Real_Div);
         when EW_Int =>
            return To_Ident (WNE_Integer_Div);
      end case;
   end New_Division;

   -------------
   -- New_Exp --
   -------------

   function New_Exp (Kind : EW_Numeric) return W_Identifier_Id is
   begin
      case Kind is
         when EW_Real =>
            return To_Ident (WNE_Real_Exp);
         when EW_Int =>
            return To_Ident (WNE_Integer_Exp);
      end case;
   end New_Exp;

   --------------------
   -- New_Identifier --
   --------------------

   function New_Identifier (Ada_Node : Node_Id := Empty; Name : String)
                            return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node, EW_Term, Name);
   end New_Identifier;

   function New_Identifier (Ada_Node : Node_Id := Empty;
                            Name    : String;
                            Context : String)
                            return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node, EW_Term, Name, Context);
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String)
     return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Domain => Domain,
                             Symbol => NID (Name));
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String;
      Context  : String)
     return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Domain   => Domain,
                             Symbol   => NID (Name),
                             Context  => NID (Capitalize_First (Context)));
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String;
      Context  : Name_Id)
     return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Domain   => Domain,
                             Symbol   => NID (Name),
                             Context  => Context);
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Symbol   : Name_Id)
     return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Domain   => Domain,
                             Symbol   => Symbol,
                             Context  => No_Name);
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

   function New_Temp_Identifier return W_Identifier_Id is
      Counter_Img : constant String :=
                      Natural'Image (New_Temp_Identifier_Counter);
   begin
      New_Temp_Identifier_Counter := New_Temp_Identifier_Counter + 1;
      return New_Identifier
        (Name => "_temp_" & To_String (New_Temp_Identifier_Suffix) & "_"
         & Counter_Img (Counter_Img'First + 1 .. Counter_Img'Last));
   end New_Temp_Identifier;

   --------------------------
   -- New_Temp_Identifiers --
   --------------------------

   function New_Temp_Identifiers (Num : Positive) return W_Identifier_Array is
      Result : constant W_Identifier_Array (1 .. Num) :=
                 (others => +New_Temp_Identifier);
   begin
      return Result;
   end New_Temp_Identifiers;

   -----------------------
   -- New_Str_Lit_Ident --
   -----------------------

   function New_Str_Lit_Ident (N : Node_Id) return String is
      Loc     : constant Source_Ptr := Sloc (N);
      C1      : constant Loc_String_Maps.Cursor :=
        File_Loc_Map.Find (Loc);

      function Register (Key : Source_Ptr; Value : String) return String;

      function Loc_To_String (Loc : Source_Ptr) return Unbounded_String;

      -------------------
      -- Loc_To_String --
      -------------------

      function Loc_To_String (Loc : Source_Ptr) return Unbounded_String
      is
         Buf : Unbounded_String;
         Ptr : Source_Ptr := Loc;
      begin
         loop
            Append (Buf, Full_Name (Cunit_Entity (Get_Source_Unit (Ptr))));
            Append (Buf, "__");
            Append (Buf, Int_Image (Integer (Get_Physical_Line_Number (Ptr))));
            Append (Buf, "__");
            Append (Buf, Int_Image (Integer (Get_Column_Number (Ptr))));
            Ptr := Instantiation_Location (Ptr);
            exit when Ptr = No_Location;
            Append (Buf, "__");
         end loop;
         return Buf;
      end Loc_To_String;

      --------------
      -- Register --
      --------------

      function Register (Key : Source_Ptr; Value : String) return String
      is
      begin
         File_Loc_Map.Insert (Key,
                              To_Unbounded_String (Value));
         return Value;
      end Register;

   begin

      --  For a given location, we always generate the same name

      if Loc_String_Maps.Has_Element (C1) then
         return To_String (Loc_String_Maps.Element (C1));
      else

         --  We have not yet seen this particular aggregate; we generate a new
         --  name. If we have already generated the given name, we add a suffix
         --  which is incremented each time.

         declare
            Unb    : constant Unbounded_String := Loc_To_String (Loc);
            Full_S : constant String := To_String (Unb);
            C2     : constant String_Int_Maps.Cursor :=
              Unit_Loc_Map.Find (Unb);
         begin
            if String_Int_Maps.Has_Element (C2) then
               declare
                  V : constant Positive := String_Int_Maps.Element (C2) + 1;
               begin
                  Unit_Loc_Map.Replace_Element (C2, V);
                  return Register (Loc, Full_S & "__" & Int_Image (V));
               end;
            else
               Unit_Loc_Map.Insert (Unb, 1);
               return Register (Loc, Full_S);
            end if;
         end;
      end if;
   end New_Str_Lit_Ident;

   function New_Str_Lit_Ident (N : Node_Id) return W_Identifier_Id is
   begin
      return New_Identifier (Name => New_Str_Lit_Ident (N));
   end New_Str_Lit_Ident;

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
         when WNE_Range_Pred   => return "in_range";
         when WNE_To_Int       => return "to_int";
         when WNE_Of_Int       => return "of_int";
         when WNE_To_Real      => return "to_real";
         when WNE_Of_Real      => return "of_real";
         when WNE_To_Array     => return "to_array";
         when WNE_Of_Array     => return "of_array";
         when WNE_Type         => return "t";
         when WNE_Ignore       => return "___ignore";
         when WNE_Result       => return "result";
         when WNE_Result_Exc   => return "_result_exc";
         when WNE_Overflow     => return "overflow_check_";
         when WNE_Eq           => return "eq";
         when WNE_Range_Axiom  => return "range_axiom";
         when WNE_Unicity      => return "unicity_axiom";
         when WNE_Coerce       => return "coerce_axiom";
         when WNE_Bool_And     => return "andb";
         when WNE_Bool_Or      => return "orb";
         when WNE_Bool_Xor     => return "xorb";
         when WNE_Integer_Div  => return "Integer.computer_div";
         when WNE_Integer_Exp  => return "Integer.power";
         when WNE_Integer_Rem  => return "Integer.computer_mod";
         when WNE_Integer_Mod  => return "Integer.math_mod";
         when WNE_Integer_Max  => return "Integer.int_max";
         when WNE_Integer_Min  => return "Integer.int_min";
         when WNE_Real_Div     => return "Floating.div_real";
         when WNE_Integer_Abs  => return "Integer.abs";
         when WNE_Real_Abs     => return "Floating.AbsReal.abs";
         when WNE_Real_Ceil    => return "Floating.ceil";
         when WNE_Real_Exp     => return "Floating.power";
         when WNE_Real_Floor   => return "Floating.floor";
         when WNE_Real_Of_Int  => return "Floating.real_of_int";
         when WNE_Real_Round   => return "Floating.round";
         when WNE_Real_Truncate => return "Floating.truncate";
         when WNE_Array_1      => return "Array__1";
         when WNE_Array_2      => return "Array__2";
         when WNE_First_Static => return "first_static";
         when WNE_Last_Static  => return "last_static";
         when WNE_Array_Access => return "access";
         when WNE_Array_Elts   => return "elts";
         when WNE_Array_First_Field => return "first";
         when WNE_Array_Last_Field => return "last";
         when WNE_Array_Offset => return "offset";
         when WNE_Array_Update => return "update";
         when WNE_Bool_Eq      => return "bool_eq";
         when WNE_Bool_Ne      => return "bool_ne";
         when WNE_Bool_Lt      => return "bool_lt";
         when WNE_Bool_Le      => return "bool_le";
         when WNE_Bool_Gt      => return "bool_gt";
         when WNE_Bool_Ge      => return "bool_ge";
         when WNE_Def          => return "def";
         when WNE_Pre_Check    => return "pre_check";
         when WNE_Def_Axiom    => return "def_axiom";
         when WNE_Obj          => return "obj";
         when WNE_Dummy        => return "dummy";
         when WNE_Log          => return "log";
         when WNE_Func         => return "func";
         when WNE_Sandbox      => return "sandbox";
         when WNE_Range_Field  => return "rt";
         when WNE_Range_Type   => return "range_type";
         when WNE_String       => return "__string";
         when WNE_Char_Type    => return "__character";
         when WNE_Private      => return "__private";
         when WNE_AutoGen      => return """autogenerated""";
         when WNE_Keep_On_Simp => return """keep_on_simp""";
         when WNE_Conversion_Label =>
            return """GP_Kind:Conversion""";

         when WNE_Attr_First   =>
            return "attr__" & Attribute_Id'Image (Attribute_First);
         when WNE_Attr_Image   =>
            return "attr__" & Attribute_Id'Image (Attribute_Image);
         when WNE_Attr_Last    =>
            return "attr__" & Attribute_Id'Image (Attribute_Last);
         when WNE_Attr_Length  =>
            return "attr__" & Attribute_Id'Image (Attribute_Length);
         when WNE_Attr_Modulus =>
            return "attr__" & Attribute_Id'Image (Attribute_Modulus);
         when WNE_Attr_Value   =>
            return "attr__" & Attribute_Id'Image (Attribute_Value);
         when WNE_Attr_Value_Pre_Check =>
            return "attr__" & Attribute_Id'Image (Attribute_Value)
              & "__pre_check";

      end case;
   end To_String;

   --------------
   -- To_Ident --
   --------------

   function To_Ident (W        : Why_Name_Enum;
                      Ada_Node : Node_Id := Empty) return W_Identifier_Id
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

   ------------
   -- Prefix --
   ------------

   function Prefix (S        : String;
                    W        : Why_Name_Enum;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Context => S,
         Name    => To_String (W),
         Ada_Node => Ada_Node);
   end Prefix;

   function Prefix (P        : String;
                    N        : String;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Context => P,
         Name     => N,
         Ada_Node => Ada_Node);
   end Prefix;

   function Prefix (S        : Why_Name_Enum;
                    W        : Why_Name_Enum;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Context => To_String (S),
         Name    => To_String (W),
         Ada_Node => Ada_Node);
   end Prefix;

   ----------------------
   -- To_Program_Space --
   ----------------------

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id is
      Suffix : constant String := "_";
      N_Id   : constant Name_Id := Get_Symbol (Name);
      Img    : constant String := Get_Name_String (N_Id);
      Context : constant Name_Id := Get_Context (Name);
   begin
      return New_Identifier
        (Get_Ada_Node (+Name), EW_Prog, Img & Suffix, Context);
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
      else
         raise Program_Error;
      end if;
   end Uint_To_Positive;

   --------------------------
   -- Why_Scalar_Type_Name --
   --------------------------

   function Why_Scalar_Type_Name (Kind : EW_Scalar) return String is
   begin
      case Kind is
         when EW_Bool =>
            return "bool";
         when EW_Int =>
            return "int";
         when EW_Real =>
            return "real";
      end case;
   end Why_Scalar_Type_Name;

end Why.Gen.Names;
