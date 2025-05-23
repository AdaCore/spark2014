------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--            G N A T 2 W H Y - U N C H E C K E D _ C O N V E R S I O N     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2025, AdaCore                          --
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
with Errout_Wrapper;              use Errout_Wrapper;
with Gnat2Why.Data_Decomposition; use Gnat2Why.Data_Decomposition;
with Gnat2Why.Tables;             use Gnat2Why.Tables;
with Snames;                      use Snames;
with SPARK_Atree;                 use SPARK_Atree;
with SPARK_Definition;            use SPARK_Definition;
with SPARK_Definition.Annotate;   use SPARK_Definition.Annotate;
with SPARK_Util.Subprograms;      use SPARK_Util.Subprograms;
with SPARK_Util.Types;            use SPARK_Util.Types;
with Ttypes;
with Why.Atree.Builders;          use Why.Atree.Builders;
with Why.Atree.Modules;           use Why.Atree.Modules;
with Why.Conversions;             use Why.Conversions;
with Why.Gen.Arrays;              use Why.Gen.Arrays;
with Why.Gen.Expr;                use Why.Gen.Expr;
with Why.Gen.Names;               use Why.Gen.Names;
with Why.Gen.Records;             use Why.Gen.Records;
with Why.Gen.Terms;               use Why.Gen.Terms;
with Why.Inter;                   use Why.Inter;
with Why.Sinfo;                   use Why.Sinfo;

package body Gnat2Why.Unchecked_Conversion is

   function Type_Name_For_Explanation (Typ : Type_Kind_Id) return String
     is (if Is_Itype (Typ) then "anonymous type"
         else "type " & Source_Name (Typ))
     with Pre => Is_Type (Typ);
   --  This function computes a user-visible string to represent the type in
   --  argument.

   procedure Compute_Size_Of_Components
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Size        : out Uint;
      Explanation : out Unbounded_String);
   --  Computes the sum of the sizes of subcomponents of Typ and store it in
   --  Size. If the size cannot be computed, Result is set to False and
   --  Explanation contains a string explaining why the size cannot be
   --  computed. This is used to check that a type has no holes.

   -----------------------------
   -- Have_Same_Known_RM_Size --
   -----------------------------

   procedure Have_Same_Known_RM_Size
     (A, B        :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
      A_RM_Size, B_RM_Size : Uint;
   begin
      Check_Known_RM_Size (A, A_RM_Size, Explanation);
      if No (A_RM_Size) then
         Result := False;
         return;
      end if;
      Check_Known_RM_Size (B, B_RM_Size, Explanation);
      if No (B_RM_Size) then
         Result := False;
         return;
      end if;
      if A_RM_Size /= B_RM_Size then
         Result := False;
         Explanation :=
           To_Unbounded_String ("Size of " & Type_Name_For_Explanation (A)
                                & " and " & Type_Name_For_Explanation (B)
                                & " differ");
         return;
      end if;
      Result := True;
      Explanation := Null_Unbounded_String;
   end Have_Same_Known_RM_Size;

   -----------------------------------
   -- Is_UC_With_Precise_Definition --
   -----------------------------------

   function Is_UC_With_Precise_Definition
     (E : Entity_Id)
      return True_Or_Explain
   is
      Source, Target                         : Node_Id;
      Source_Type, Target_Type               : Entity_Id;
      Valid_Source, Valid_Target, Valid_Size : Boolean;
      Explanation                            : Unbounded_String;
      Check                                  : True_Or_Explain;

   begin
      Get_Unchecked_Conversion_Args (E, Source, Target);
      Source_Type := Retysp (Entity (Source));
      Target_Type := Retysp (Entity (Target));

      --  Check that types are suitable for UC.

      Suitable_For_UC_Source (Source_Type, Valid_Source, Explanation);
      if not Valid_Source then
         --  Override explanation to avoid special characters
         return False_With_Explain
           ("type is unsuitable as source for unchecked conversion");
      end if;

      Suitable_For_UC_Target_UC_Wrap (Target_Type, Valid_Target, Explanation);
      if not Valid_Target then
         --  Override explanation to avoid special characters
         return False_With_Explain
           ("type is unsuitable as target for unchecked conversion");
      end if;

      Have_Same_Known_RM_Size
        (Source_Type, Target_Type, Valid_Size, Explanation);
      if not Valid_Size then
         --  Override explanation to avoid special characters
         return False_With_Explain
           ("types in unchecked conversion do not have the same size");
      end if;

      --  Only support types with size up to 128 bits, to use one of the
      --  available bitvector types with conversions from other bitvector
      --  sizes.

      if Get_Attribute_Value (Source_Type, Attribute_Size) > 128 then
         return False_With_Explain ("type size larger than 128 bits");
      end if;

      --  Only generate a definition for UC between integer types, and
      --  composites of integer types.

      Check := Suitable_For_Precise_UC (Source_Type);
      if not Check.Ok then
         return Check;
      end if;

      Check := Suitable_For_Precise_UC (Target_Type);
      if not Check.Ok then
         return Check;
      end if;

      return (Ok => True);
   end Is_UC_With_Precise_Definition;

   ----------------------------
   -- Objects_Have_Same_Size --
   ----------------------------

   procedure Objects_Have_Same_Size
     (A, B        : Node_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
      A_Size, B_Size         : Uint;
      A_Size_Str, B_Size_Str : Unbounded_String;
   begin
      Check_Known_Size_For_Object (A, A_Size, Explanation, A_Size_Str);
      if No (A_Size) then
         Result := False;
         return;
      end if;
      Check_Known_Size_For_Object (B, B_Size, Explanation, B_Size_Str);
      if No (B_Size) then
         Result := False;
         return;
      end if;
      if A_Size /= B_Size then
         Result := False;
         Explanation :=
           To_Unbounded_String
             ("sizes of overlaid objects differ: "
              & To_String (A_Size_Str) & " " & Escape (UI_Image (A_Size))
              & ", while "
              & To_String (B_Size_Str) & " " & Escape (UI_Image (B_Size)));
         return;
      end if;
      Result := True;
      Explanation := Null_Unbounded_String;
   end Objects_Have_Same_Size;
   --------------------------
   -- Precise_Composite_UC --
   --------------------------

   function Precise_Composite_UC
     (Arg         : W_Term_Id;
      Source_Type : Type_Kind_Id;
      Target_Type : Type_Kind_Id)
      return W_Term_Id
   is
      --  Representation of a subcomponent of Source
      type Source_Element is record
         Typ    : Type_Kind_Id;
         Offset : Uint;
         Size   : Uint;
         Expr   : W_Term_Id;
      end record;

      package Source_Elements is new
        Ada.Containers.Doubly_Linked_Lists (Source_Element);
      use Source_Elements;

      --  Local subprograms

      function Contribute_Value
        (Base   : W_Type_Id;
         Expr   : W_Expr_Id;
         Offset : Uint;
         Size   : Uint;
         Typ    : Type_Kind_Id)
                     return W_Expr_Id;
      --  Given a scalar expression Expr of type Typ, return its
      --  contribution to a modular value of type Base, when its
      --  bit representation takes Size bits at a given Offset in
      --  Base.

      function Expr_Index
        (Typ : Type_Kind_Id;
         Idx : Uint)
                     return W_Expr_Id;
      --  Return the expression for indexing into array of type Typ

      function Extract_Value
        (Base   : W_Type_Id;
         Bits   : W_Expr_Id;
         Offset : Uint;
         Size   : Uint;
         Typ    : Type_Kind_Id)
                     return W_Expr_Id;
      --  Return (Bits and (2**(Offset+Size)-1)) / 2**(Offset) as
      --  a value of type Typ, to extract the value of an element
      --  from its bit representation.

      procedure Get_Source_Elements
        (Typ      : Type_Kind_Id;
         Offset   : Uint;
         Size     : Uint;
         Expr     : W_Term_Id;
         Elements : in out List);
      --  Retrieve the list of scalar elements from an object Expr
      --  of type Typ located at a given Offset and of a given
      --  Size, and append these to Elements.

      function Reconstruct_Value
        (Base   : W_Type_Id;
         Bits   : W_Expr_Id;
         Offset : Uint;
         Size   : Uint;
         Typ    : Type_Kind_Id)
                     return W_Expr_Id;
      --  Given the representation Bits of modular type Base for
      --  the complete object, reconstruct the element of type Typ
      --  of a given Size at a given Offset.

      ----------------------
      -- Contribute_Value --
      ----------------------

      function Contribute_Value
        (Base   : W_Type_Id;
         Expr   : W_Expr_Id;
         Offset : Uint;
         Size   : Uint;
         Typ    : Type_Kind_Id)
                     return W_Expr_Id
      is
         Value : W_Expr_Id;
      begin
         --  Special case for Boolean
         if Is_Standard_Boolean_Type (Typ) then
            Value :=
              New_Conditional
                (Domain    => EW_Term,
                 Condition => Expr,
                 Then_Part =>
                   New_Modular_Constant
                     (Value => Uint_1,
                      Typ   => Base),
                 Else_Part =>
                   New_Modular_Constant
                     (Value => Uint_0,
                      Typ   => Base),
                 Typ       => Base);

            --  If the value is from a modular type, or from a signed
            --  type with no negative value, then simply convert it to
            --  Base.
         elsif Is_Unsigned_Type (Typ) then
            Value := Insert_Scalar_Conversion
              (Domain => EW_Term,
               Expr   => Expr,
               To     => Base);

            --  Otherwise, we need to consider the bit representation
            --  of that (possibly negative) signed value as Base, and
            --  extract the low Size bits with the expression
            --  (uc_of_int Expr) and (2**Size - 1)
         else
            Value :=
              New_Call
                (Domain   => EW_Term,
                 Name     => MF_BVs (Base).BW_And,
                 Typ      => Base,
                 Args     =>
                   (1 =>
                          New_Call
                      (Domain => EW_Term,
                       Name   => MF_BVs (Base).UC_Of_Int,
                       Args   =>
                         (1 =>
                              Insert_Scalar_Conversion
                            (Domain => EW_Term,
                             Expr   => Expr,
                             To     => EW_Int_Type)),
                       Typ    => Base),
                    2 =>
                      New_Modular_Constant
                        (Value => Uint_2 ** Size - Uint_1,
                         Typ   => Base)));
         end if;

         --  Multiply this value by 2**Offset to get its
         --  contribution to the overall value.
         return
           New_Call
             (Domain   => EW_Term,
              Name     => MF_BVs (Base).Mult,
              Typ      => Base,
              Args     =>
                (1 =>
                       New_Modular_Constant
                   (Value => Uint_2 ** Offset,
                    Typ   => Base),
                 2 => Value));
      end Contribute_Value;

      ----------------
      -- Expr_Index --
      ----------------

      function Expr_Index
        (Typ : Type_Kind_Id;
         Idx : Uint)
                     return W_Expr_Id
      is
         Index_Typ : constant Type_Kind_Id :=
           Etype (First_Index (Typ));
      begin
         if Is_Modular_Integer_Type (Index_Typ) then
            return
              New_Modular_Constant
                (Value => Idx,
                 Typ   => Base_Why_Type_No_Bool (Index_Typ));
         else
            return New_Integer_Constant (Value => Idx);
         end if;
      end Expr_Index;

      -------------------
      -- Extract_Value --
      -------------------

      function Extract_Value
        (Base   : W_Type_Id;
         Bits   : W_Expr_Id;
         Offset : Uint;
         Size   : Uint;
         Typ    : Type_Kind_Id)
                     return W_Expr_Id
      is
         Mask    : constant W_Expr_Id :=
           New_Modular_Constant
             (Value => Uint_2 ** (Offset + Size) - Uint_1,
              Typ   => Base);
         Divisor : constant W_Expr_Id :=
           New_Modular_Constant
             (Value => Uint_2 ** Offset,
              Typ   => Base);
         --  Value is (Bits and (2**(Offset+Size)-1)) / 2**(Offset)
         Value   : constant W_Expr_Id :=
           New_Call
             (Domain => EW_Term,
              Name   => MF_BVs (Base).Udiv,
              Typ    => Base,
              Args   =>
                (1 =>
                       New_Call
                   (Domain => EW_Term,
                    Name   => MF_BVs (Base).BW_And,
                    Typ    => Base,
                    Args   =>
                      (1 => Bits,
                       2 => Mask)),
                 2 => Divisor));
      begin
         --  Special case for Boolean
         if Is_Standard_Boolean_Type (Typ) then
            return
              New_Conditional
                (Domain    => EW_Term,
                 Condition =>
                   New_Comparison
                     (Domain => EW_Term,
                      Symbol => Why_Eq,
                      Left   => Value,
                      Right  =>
                        New_Modular_Constant
                          (Value => Uint_1,
                           Typ   => Base)),
                 Then_Part => +True_Term,
                 Else_Part => +False_Term,
                 Typ       => EW_Bool_Type);

            --  If the value is to a modular type, or an enumeration
            --  with default 0-based representation, or to a signed
            --  type with no negative value, then simply convert it
            --  to Typ.
         elsif Is_Unsigned_Type (Typ) then
            return Insert_Scalar_Conversion
              (Domain => EW_Term,
               Expr   => Value,
               To     => EW_Abstract (Typ));

            --  Otherwise, we need to consider the bit representation
            --  of that (possibly negative) signed value, to see
            --  if the high bit is 1, in which case the value is
            --  negative. So we generate the value
            --  if Value >= 2**(Size-1) then Value-2**Size else Value
         else
            declare
               Top_Bit        : constant W_Expr_Id :=
                 New_Modular_Constant
                   (Value => Uint_2 ** (Size - Uint_1),
                    Typ   => Base);
               Negative_Value : constant W_Expr_Id :=
                 New_Call
                   (Domain => EW_Term,
                    Name   => Int_Infix_Subtr,
                    Typ    => EW_Int_Type,
                    Args   =>
                      (1 =>
                             Insert_Scalar_Conversion
                         (Domain => EW_Term,
                          Expr   => Value,
                          To     => EW_Int_Type),
                       2 =>
                         New_Integer_Constant
                           (Value => 2 ** Size)));
            begin
               return New_Conditional
                 (Domain    => EW_Term,
                  Condition =>
                    New_Comparison
                      (Domain => EW_Term,
                       Symbol => MF_BVs (Base).Uge,
                       Left   => Value,
                       Right  => Top_Bit),
                  Then_Part =>
                    Insert_Scalar_Conversion
                      (Domain => EW_Term,
                       Expr   => Negative_Value,
                       To     => EW_Abstract (Typ)),
                  Else_Part =>
                    Insert_Scalar_Conversion
                      (Domain => EW_Term,
                       Expr   => Value,
                       To     => EW_Abstract (Typ)),
                  Typ       => EW_Abstract (Typ));
            end;
         end if;
      end Extract_Value;

      --------------------------
      -- Get_Type_Offset_List --
      --------------------------

      procedure Get_Source_Elements
        (Typ      : Type_Kind_Id;
         Offset   : Uint;
         Size     : Uint;
         Expr     : W_Term_Id;
         Elements : in out List)
      is
      begin
         if Is_Scalar_Type (Typ) then
            Elements.Append
              (Source_Element'(Typ    => Typ,
                               Offset => Offset,
                               Size   => Size,
                               Expr   => Expr));

         elsif Is_Record_Type (Typ) then
            declare
               Comp : Node_Id := First_Component (Typ);
            begin
               while Present (Comp) loop
                  Get_Source_Elements
                    (Typ      => Retysp (Etype (Comp)),
                     Offset   =>
                       Offset + Component_Bit_Offset (Comp),
                     Size     => Esize (Comp),
                     Expr     => New_Ada_Record_Access
                       (Ada_Node => Types.Empty,
                        Name     => +Expr,
                        Ty       => Typ,
                        Field    => Comp),
                     Elements => Elements);
                  Next_Component (Comp);
               end loop;
            end;

         elsif Is_Array_Type (Typ) then
            declare
               Index : constant Node_Id := First_Index (Typ);
               Rng   : constant Node_Id := Get_Range (Index);
               Low   : constant Uint :=
                 Expr_Value (Low_Bound (Rng));
               High  : constant Uint :=
                 Expr_Value (High_Bound (Rng));
               Cur   : Uint;
            begin
               if Low <= High then
                  Cur := Low;
                  while Cur <= High loop
                     Get_Source_Elements
                       (Typ      => Retysp (Component_Type (Typ)),
                        Offset   =>
                          (Cur - Low) * Component_Size (Typ),
                        Size     => Component_Size (Typ),
                        Expr     =>
                          New_Array_Access
                            (Ar    => Expr,
                             Index =>
                               (1 => Expr_Index (Typ, Cur))),
                        Elements => Elements);
                     Cur := Cur + Uint_1;
                  end loop;
               end if;
            end;

         else
            raise Program_Error;
         end if;
      end Get_Source_Elements;

      -----------------------
      -- Reconstruct_Value --
      -----------------------

      function Reconstruct_Value
        (Base   : W_Type_Id;
         Bits   : W_Expr_Id;
         Offset : Uint;
         Size   : Uint;
         Typ    : Type_Kind_Id)
                     return W_Expr_Id
      is
      begin
         if Is_Scalar_Type (Typ) then
            return Extract_Value
              (Base   => Base,
               Bits   => Bits,
               Offset => Offset,
               Size   => Size,
               Typ    => Typ);

         elsif Is_Record_Type (Typ) then
            declare
               Comps  : constant Component_Sets.Set :=
                 Get_Component_Set (Typ);
               Assocs : W_Field_Association_Array
                 (1 .. Integer (Comps.Length));
               Index  : Positive := 1;
            begin
               for Comp of Comps loop
                  Assocs (Index) :=
                    New_Field_Association
                      (Domain => EW_Term,
                       Field  =>
                         To_Why_Id
                           (Comp, Local => False, Rec => Typ),
                       Value  =>
                         Reconstruct_Value
                           (Base   => Base,
                            Bits   => Bits,
                            Offset =>
                              Offset + Component_Bit_Offset (Comp),
                            Size   => Esize (Comp),
                            Typ    => Retysp (Etype (Comp))));
                  Index := Index + 1;
               end loop;

               return New_Record_Aggregate
                 (Associations =>
                    (1 => New_Field_Association
                         (Domain => EW_Term,
                          Field  =>
                            E_Symb (Typ, WNE_Rec_Split_Fields),
                          Value  =>
                            New_Record_Aggregate
                              (Associations => Assocs))),
                  Typ          => EW_Abstract (Typ));
            end;

         elsif Is_Array_Type (Typ) then
            declare
               Index : constant Node_Id := First_Index (Typ);
               Rng   : constant Node_Id := Get_Range (Index);
               Low   : constant Uint :=
                 Expr_Value (Low_Bound (Rng));
               High  : constant Uint :=
                 Expr_Value (High_Bound (Rng));
               Cur   : Uint;
               Ar    : W_Expr_Id := +E_Symb (Typ, WNE_Dummy);
            begin
               if Low <= High then
                  Cur := Low;
                  while Cur <= High loop
                     Ar := New_Array_Update
                       (Ada_Node => Types.Empty,
                        Ar       => Ar,
                        Index    => (1 => Expr_Index (Typ, Cur)),
                        Value    =>
                          Reconstruct_Value
                            (Base   => Base,
                             Bits   => Bits,
                             Offset =>
                               Offset +
                                 (Cur - Low) * Component_Size (Typ),
                             Size   =>
                               Component_Size (Typ),
                             Typ    =>
                               Retysp (Component_Type (Typ))),
                        Domain   => EW_Term);
                     Cur := Cur + 1;
                  end loop;
               end if;

               return Ar;
            end;

         else
            raise Program_Error;
         end if;
      end Reconstruct_Value;

      --  Local variables

      Conv         : W_Term_Id;
      Source_Elems : List;
      Target_Size  : constant Uint :=
        Get_Attribute_Value (Target_Type, Attribute_Size);
      Base         : constant W_Type_Id :=
        (if    Target_Size <=   Uint_8 then EW_BitVector_8_Type
         elsif Target_Size <=  Uint_16 then EW_BitVector_16_Type
         elsif Target_Size <=  Uint_32 then EW_BitVector_32_Type
         elsif Target_Size <=  Uint_64 then EW_BitVector_64_Type
         elsif Target_Size <= Uint_128 then EW_BitVector_128_Type
         else raise Program_Error);
      Def          : W_Term_Id;

   begin
      --  1. Convert the argument to a value of modular type Base

      --  1.a Conversion from a scalar type should be identity or
      --  call to uc_of_int.

      if Is_Scalar_Type (Source_Type) then
         Conv :=
           Precise_Integer_UC
             (Arg           => +Arg,
              Size          => No_Uint,
              Source_Type   => EW_Abstract (Source_Type),
              Target_Type   => Base,
              Source_Status => Get_Scalar_Status (Source_Type),
              Target_Status => Modular);

         --  1.b Otherwise extract all scalar subcomponents from the
         --  composite value and sum up their contributions to the
         --  value of type Base.

      else
         Get_Source_Elements
           (Source_Type, Uint_0, Uint_0, +Arg, Source_Elems);
         Conv :=
           New_Modular_Constant (Value => Uint_0, Typ => Base);

         for Elem of Source_Elems loop
            Conv :=
              New_Call
                (Name     => MF_BVs (Base).Add,
                 Typ      => Base,
                 Args     =>
                   (1 => +Conv,
                    2 => Contribute_Value
                      (Base   => Base,
                       Expr   => +Elem.Expr,
                       Offset => Elem.Offset,
                       Size   => Elem.Size,
                       Typ    => Elem.Typ)));
         end loop;
      end if;

      --  2. Convert the converted argument to a value of the
      --  target type.

      --  2.a Conversion to a scalar type should be identity or
      --  call to uc_to_int.

      if Is_Scalar_Type (Target_Type) then
         Def :=
           Precise_Integer_UC
             (Arg           => Conv,
              Size          => No_Uint,
              Source_Type   => Base,
              Target_Type   => Base_Why_Type_No_Bool (Target_Type),
              Source_Status => Modular,
              Target_Status => Get_Scalar_Status (Target_Type));

         --  2.b Otherwise recursively reconstruct all scalar
         --  subcomponents from the value of type Base.

      else
         Def :=
           +Reconstruct_Value
           (Base   => Base,
            Bits   => +Conv,
            Offset => Uint_0,
            Size   =>
              Get_Attribute_Value (Target_Type, Attribute_Size),
            Typ    => Target_Type);
      end if;
      return Def;
   end Precise_Composite_UC;

   ------------------------
   -- Precise_Integer_UC --
   ------------------------

   function Precise_Integer_UC
     (Arg           : W_Term_Id;
      Size          : Uint;
      Source_Type   : W_Type_Id;
      Target_Type   : W_Type_Id;
      Source_Status : Scalar_Status;
      Target_Status : Scalar_Status)
      return W_Term_Id
   is
      Source_Base_Type : constant W_Type_Id :=
        Base_Why_Type_No_Bool (Source_Type);
      Target_Base_Type : constant W_Type_Id :=
        Base_Why_Type_No_Bool (Target_Type);
      Conv             : W_Term_Id;
   begin
      Conv :=
        Insert_Simple_Conversion (Expr => Arg, To => Source_Base_Type);

      if Source_Status = Target_Status then
         null;  --  Trivial case of UC between identical types

      elsif Source_Status = Unsigned
        and then Target_Status = Modular
      then
         null;  --  Unsigned value can be directly converted to modular

      elsif Source_Status = Modular
        and then Target_Status = Unsigned
      then
         null;  --  Modular value can be directly converted to unsigned

         --  Apply the appropriate UC function for conversions between Modular
         --  and Signed.

      elsif Source_Status = Modular
        and then Target_Status = Signed
      then
         Conv := New_Call
           (Name => MF_BVs (Source_Base_Type).UC_To_Int,
            Args => (1 => +Conv),
            Typ  => EW_Int_Type);

      elsif Source_Status = Signed
        and then Target_Status = Modular
      then
         Conv := New_Call
           (Name => MF_BVs (Target_Base_Type).UC_Of_Int,
            Args => (1 => +Conv),
            Typ  => Target_Base_Type);

         --  Otherwise, this is a conversion between Unsigned and Signed.
         --  We need to consider the bit representation of that (possibly
         --  negative) signed value, to see if the high bit is 1, in which
         --  case the Signed value is negative.

      elsif Source_Status = Unsigned
        and then Target_Status = Signed
      then
         --  Generate the value
         --  if Conv >= 2**(Size-1) then Conv-2**Size else Conv
         declare
            Top_Bit        : constant W_Term_Id :=
              New_Integer_Constant
                (Value => Uint_2 ** (Size - Uint_1));
            Negative_Value : constant W_Term_Id :=
              New_Call
                (Name   => Int_Infix_Subtr,
                 Typ    => EW_Int_Type,
                 Args   =>
                   (1 => +Conv,
                    2 => New_Integer_Constant (Value => 2 ** Size)));
         begin
            Conv := New_Conditional
              (Condition =>
                 New_Comparison
                   (Symbol => Int_Infix_Ge,
                    Left   => Conv,
                    Right  => Top_Bit),
               Then_Part => Negative_Value,
               Else_Part => Conv,
               Typ       => EW_Int_Type);
         end;

      else
         pragma Assert (Source_Status = Signed);
         pragma Assert (Target_Status = Unsigned);

         --  Generate the value
         --  if Conv < 0 then Conv+2**Size else Conv
         declare
            Large_Value : constant W_Term_Id :=
              New_Call
                (Name   => Int_Infix_Add,
                 Typ    => EW_Int_Type,
                 Args   =>
                   (1 => +Conv,
                    2 => New_Integer_Constant (Value => 2 ** Size)));
         begin
            Conv := New_Conditional
              (Condition =>
                 New_Comparison
                   (Symbol => Int_Infix_Lt,
                    Left   => Conv,
                    Right  => New_Integer_Constant (Value => Uint_0)),
               Then_Part => Large_Value,
               Else_Part => Conv,
               Typ       => EW_Int_Type);
         end;
      end if;

      return Insert_Simple_Conversion (Expr => Conv, To => Target_Type);
   end Precise_Integer_UC;

   -----------------------------
   -- Suitable_For_Precise_UC --
   -----------------------------

   function Suitable_For_Precise_UC
     (Arg_Typ : Type_Kind_Id)
      return True_Or_Explain
   is
      Typ : constant Type_Kind_Id := Retysp (Arg_Typ);
   begin
      case Ekind (Typ) is
         when Integer_Kind =>
            if Has_Biased_Representation (Typ) then
               return False_With_Explain
                 ("type with biased representation");

            elsif Has_Modular_Integer_Type (Typ)
              and then Has_No_Bitwise_Operations_Annotation (Typ)
            then
               return False_With_Explain
                 ("type with No_Bitwise_Operations annotation");
            end if;

         when Enumeration_Kind =>
            if Has_Enumeration_Rep_Clause (Typ)
              and then Enumeration_Rep (First_Literal (Typ)) /= Uint_0
            then
               return False_With_Explain
                 ("enumeration with non-default representation");
            end if;

         when Record_Kind =>

            --  Tagged types and discriminants are not supported in UC

            if Is_Tagged_Type (Typ) then
               pragma Assert (False);

            elsif Has_Discriminants (Typ) then
               pragma Assert (False);

            elsif Reverse_Storage_Order (Base_Retysp (Typ)) then
               return False_With_Explain
                 ("type has reverse storage order");
            end if;

            declare
               Comp : Entity_Id := First_Component (Typ);
            begin
               while Present (Comp) loop
                  if No (Component_Bit_Offset (Comp)) then
                     return False_With_Explain
                       ("component offset not known");
                  end if;

                  declare
                     Check : constant True_Or_Explain :=
                       Suitable_For_Precise_UC (Etype (Comp));
                  begin
                     if not Check.Ok then
                        return Check;
                     end if;
                  end;
                  Next_Component (Comp);
               end loop;
            end;

         when Array_Kind =>
            declare
               Check : constant True_Or_Explain :=
                 Suitable_For_Precise_UC (Component_Type (Typ));
            begin
               if not Check.Ok then
                  return Check;
               end if;
            end;

            if Number_Dimensions (Typ) > Uint_1 then
               return False_With_Explain
                 ("array has multiple dimensions");

            elsif Reverse_Storage_Order (Base_Retysp (Typ)) then
               return False_With_Explain
                 ("type has reverse storage order");
            end if;

         when others =>
            return False_With_Explain ("elementary non-integer type");
      end case;

      return True_Or_Explain'(Ok => True);
   end Suitable_For_Precise_UC;

   --------------------------------
   -- Compute_Size_Of_Components --
   --------------------------------

   procedure Compute_Size_Of_Components
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Size        : out Uint;
      Explanation : out Unbounded_String)
   is
      Typ_Name : constant String := Type_Name_For_Explanation (Typ);

   begin
      --  Default initialization for GNAT SAS
      Size := Uint_0;

      if Is_Array_Type (Typ) then

         --  Unconstarined types are not allowed as source or target of UC

         pragma Assert (Is_Constrained (Typ));

         declare
            Comp_Typ  : constant Type_Kind_Id :=
              Retysp (Component_Type (Typ));
            Comp_Size : Uint;
            Index     : Node_Id;

         begin
            Compute_Size_Of_Components
              (Comp_Typ, Result, Comp_Size, Explanation);
            if not Result then
               return;
            end if;

            Size := Comp_Size;
            Index := First_Index (Typ);
            while Present (Index) loop
               declare
                  Rng : constant Node_Id := Get_Range (Index);
               begin
                  --  Size cannot be known for variable length type

                  if not Compile_Time_Known_Value (Low_Bound (Rng))
                    or else not Compile_Time_Known_Value (High_Bound (Rng))
                  then
                     raise Program_Error;
                  end if;

                  Size :=
                    Size *
                      (Expr_Value (High_Bound (Rng)) -
                         Expr_Value (Low_Bound (Rng)) + 1);
                  Next_Index (Index);
               end;
            end loop;
         end;

      elsif Is_Record_Type (Typ) then
         if Has_Discriminants (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String
                (Typ_Name & " has discriminants");
            return;
         end if;

         for Comp of Get_Component_Set (Typ) loop
            declare
               Comp_Ty   : constant Type_Kind_Id :=
                 Retysp (Etype (Comp));
               Comp_Size : Uint;
            begin
               Compute_Size_Of_Components
                 (Comp_Ty, Result, Comp_Size, Explanation);

               if not Result then
                  return;
               end if;
               Size := Size + Comp_Size;
            end;
         end loop;

      else
         pragma Assert (Is_Scalar_Type (Typ));

         --  The size of scalar types is always known statically
         pragma Assert (Known_RM_Size (Typ));
         Size := RM_Size (Typ);
      end if;

      Result      := True;
      Explanation := Null_Unbounded_String;
   end Compute_Size_Of_Components;

   ---------------------
   -- Suitable_For_UC --
   ---------------------

   procedure Suitable_For_UC
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is

      function Type_Unsuitable_For_UC (Typ : Type_Kind_Id) return Test_Result;
      --  Function to check the properties enforced on all subcomponents of a
      --  type "suitable for unchecked conversion" of SPARK RM 13.9.

      --------------------------
      -- Type_Suitable_For_UC --
      --------------------------

      function Type_Unsuitable_For_UC (Typ : Type_Kind_Id) return Test_Result
      is
         Typ_Name : constant String := Type_Name_For_Explanation (Typ);

      begin
         --  We exclude types with tags, private types, access types, and
         --  concurrent types.

         if Is_Tagged_Type (Typ) then
            Explanation := To_Unbounded_String
              (Typ_Name & " is a tagged type");
            return Pass;

         elsif Full_View_Not_In_SPARK (Typ) then
            Explanation := To_Unbounded_String
              (Typ_Name & " is not entirely visible in SPARK");
            return Pass;

         elsif Is_Concurrent_Type (Typ) then
            pragma Annotate
              (Xcov, Exempt_On, "The frontend crashes on UC on tasks and "
               & "rejectes UC on protected types");
            Explanation := To_Unbounded_String
              (Typ_Name & " is a concurrent type");
            return Pass;
            pragma Annotate (Xcov, Exempt_Off);

         elsif Is_Access_Type (Typ) then
            Explanation := To_Unbounded_String
              (Typ_Name & " is an access type");
            return Pass;

         --  GNAT only guarantees to zero-out extra bits when writing in a
         --  scalar component if its size is not larger than the largest
         --  floating-point type (for floats) or the largest integer type (for
         --  other scalar types) on the target.

         elsif Is_Floating_Point_Type (Typ)
           and then Get_Attribute_Value (Typ, Attribute_Size)
           > Ttypes.Standard_Long_Long_Float_Size
         then
            Explanation := To_Unbounded_String
              ("too large value of Size for " & Typ_Name);
            return Pass;

         elsif Is_Scalar_Type (Typ)
           and then Get_Attribute_Value (Typ, Attribute_Size)
           > Ttypes.Standard_Long_Long_Long_Integer_Size
         then
            Explanation := To_Unbounded_String
              ("too large value of Size for " & Typ_Name);
            return Pass;

         else
            return Continue;
         end if;
      end Type_Unsuitable_For_UC;

      function Has_Unsuitable_Component is new Traverse_Subcomponents
        (Type_Unsuitable_For_UC);

   begin
      Result := not Has_Unsuitable_Component (Typ);
   end Suitable_For_UC;

   ----------------------------
   -- Suitable_For_UC_Source --
   ----------------------------

   procedure Suitable_For_UC_Source
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
      Typ_Name   : constant String := Type_Name_For_Explanation (Typ);
      Common_Exp : constant String :=
        "; " & Typ_Name &
        " might have unused bits that are not modelled in SPARK";
      Size       : Uint;
      Sum_Comp   : Uint;

   begin
      Suitable_For_UC (Typ, Result, Explanation);
      if not Result then
         return;
      end if;

      --  Check that there is no holes

      Check_Known_RM_Size (Typ, Size, Explanation);
      if No (Size) then
         Result := False;
         Append (Explanation, Common_Exp);
         return;
      end if;

      Compute_Size_Of_Components (Typ, Result, Sum_Comp, Explanation);

      if not Result then
         Append (Explanation, Common_Exp);
         return;
      elsif Size = Sum_Comp then
         Result := True;
      else
         Result := False;
         Explanation :=
           To_Unbounded_String
             (Typ_Name & " has minimal size " & UI_Image (Sum_Comp)
              & ", but Size was declared as "
              & UI_Image (Size) &  Common_Exp);
      end if;
   end Suitable_For_UC_Source;

   ----------------------------
   -- Suitable_For_UC_Target --
   ----------------------------

   procedure Suitable_For_UC_Target
     (Typ         :     Type_Kind_Id;
      Size        :     Uint;
      Size_Str    :     String;
      For_UC      :     Boolean;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
   begin
      Suitable_For_UC (Typ, Result, Explanation);

      --  Check for invalid values

      if Result then
         declare
            Res          : True_Or_Explain := (Ok => True);
            Continuation : constant String :=
              (if For_UC
               then "; invalid values could result from the unchecked "
               & "conversion [SPARK RM 13.9]"
               else "; aliased object could have invalid values "
               & "[SPARK RM 13.7]");
         begin
            Res := Type_Has_Only_Valid_Values (Typ, Size, Size_Str);

            Result := Res.Ok;
            if not Result then
               Explanation := Res.Explanation & Continuation;
            end if;
         end;
      end if;
   end Suitable_For_UC_Target;

   -----------------------------------------
   -- Suitable_For_UC_Target_Overlay_Wrap --
   -----------------------------------------

   procedure Suitable_For_UC_Target_Overlay_Wrap
     (Typ         :     Type_Kind_Id;
      Obj         :     Node_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
      Size     : Uint := Uint_0;
      Size_Str : Unbounded_String;
   begin
      if Is_Scalar_Type (Typ) then
         Check_Known_Size_For_Object (Obj, Size, Explanation, Size_Str);
         if No (Size) then
            Result := False;
            return;
         end if;
      end if;
      Suitable_For_UC_Target
        (Typ,
         Size,
         To_String (Size_Str),
         False,
         Result,
         Explanation);
   end Suitable_For_UC_Target_Overlay_Wrap;

   ------------------------------------
   -- Suitable_For_UC_Target_UC_Wrap --
   ------------------------------------

   procedure Suitable_For_UC_Target_UC_Wrap
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
      Size : Uint := Uint_0;
   begin
      if Is_Scalar_Type (Typ) then
         --  ARM K.2 226
         Check_Known_RM_Size (Typ, Size, Explanation);
         pragma Assert (not No (Size));
      end if;
      Suitable_For_UC_Target
        (Typ, Size, "Size", True, Result, Explanation);
   end Suitable_For_UC_Target_UC_Wrap;

end Gnat2Why.Unchecked_Conversion;
