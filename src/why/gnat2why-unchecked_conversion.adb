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
with Common_Containers;           use Common_Containers;
with GNAT.Source_Info;
with Gnat2Why.Expr;               use Gnat2Why.Expr;
with GNATCOLL.Symbols;            use GNATCOLL.Symbols;
with Gnat2Why.Data_Decomposition; use Gnat2Why.Data_Decomposition;
with Gnat2Why.Tables;             use Gnat2Why.Tables;
with Gnat2Why.Util;               use Gnat2Why.Util;
with Namet;                       use Namet;
with Sinput;                      use Sinput;
with Snames;                      use Snames;
with SPARK_Definition;            use SPARK_Definition;
with SPARK_Definition.Annotate;   use SPARK_Definition.Annotate;
with SPARK_Util.Types;            use SPARK_Util.Types;
with String_Utils;                use String_Utils;
with Ttypes;
with Why.Atree.Accessors;         use Why.Atree.Accessors;
with Why.Atree.Builders;          use Why.Atree.Builders;
with Why.Atree.Modules;           use Why.Atree.Modules;
with Why.Conversions;             use Why.Conversions;
with Why.Gen.Arrays;              use Why.Gen.Arrays;
with Why.Gen.Binders;             use Why.Gen.Binders;
with Why.Gen.Decl;                use Why.Gen.Decl;
with Why.Gen.Expr;                use Why.Gen.Expr;
with Why.Gen.Names;               use Why.Gen.Names;
with Why.Gen.Records;             use Why.Gen.Records;
with Why.Gen.Terms;               use Why.Gen.Terms;
with Why.Images;                  use Why.Images;
with Why.Inter;                   use Why.Inter;
with Why.Sinfo;                   use Why.Sinfo;
with Why.Types;                   use Why.Types;

package body Gnat2Why.Unchecked_Conversion is

   function Type_Name_For_Explanation (Typ : Type_Kind_Id) return String
   is (if Is_Itype (Typ)
       then "anonymous type"
       else "type " & Source_Name (Typ))
   with Pre => Is_Type (Typ);
   --  This function computes a user-visible string to represent the type in
   --  argument.

   procedure Compute_Size_Of_Components
     (Typ         : Type_Kind_Id;
      Result      : out Boolean;
      Size        : out Uint;
      Explanation : out Unbounded_String);
   --  Computes the sum of the sizes of subcomponents of Typ and store it in
   --  Size. If the size cannot be computed, Result is set to False and
   --  Explanation contains a string explaining why the size cannot be
   --  computed. This is used to check that a type has no holes.
   --  Note: This procedure is currently only suitable for checks related to
   --  Unchecked_Conversion, in particular for "suitable as a source of an
   --  unchecked conversion".

   function Is_Valid_Scalar
     (Range_Ty : Type_Kind_Id; Value : W_Term_Id) return W_Term_Id
   is (if Is_Standard_Boolean_Type (Range_Ty)
       then
         New_Call
           (Name => M_Boolean.Range_Pred,
            Args => (1 => +Value),
            Typ  => EW_Bool_Type)
       elsif Type_Is_Modeled_As_Base (Range_Ty)
       then
         +New_Dynamic_Property
            (Domain => EW_Term, Ty => Range_Ty, Expr => Value)
       else
         New_Call
           (Name => E_Symb (Range_Ty, WNE_Range_Pred),
            Args => (1 => +Value),
            Typ  => EW_Bool_Type));
   --  Return a term checking whether Value is in Range_Ty

   function Get_UC_Theory_Name
     (Source_Type, Target_Type : Type_Kind_Id; Potentially_Invalid : Boolean)
      return Symbol;
   --  Return a name of the form
   --  "Uc___Source_Type___Target_Type(___potentially_invalid)?"
   --  for the theory for unchecked conversions from Source_Type to
   --  Target_Type.

   type Scalar_Status is
     (Signed,    --  Signed integer type
      Unsigned,  --  Unsigned integer type = signed with no negative value,
      --  also used for enumerations with default representation
      --  clauses.
      Modular);  --  Modular integer type

   function Get_Scalar_Status (Typ : Type_Kind_Id) return Scalar_Status
   is (if Is_Modular_Integer_Type (Typ)
       then Modular
       elsif Is_Enumeration_Type (Typ)
       then Unsigned
       elsif Is_Unsigned_Type (Typ)
       then Unsigned
       elsif Is_Signed_Integer_Type (Typ)
       then Signed
       else raise Program_Error);

   function Precise_Integer_UC
     (Arg                 : W_Term_Id;
      Size                : Uint;
      Source_Type         : W_Type_Id;
      Target_Type         : W_Type_Id;
      Source_Status       : Scalar_Status;
      Target_Status       : Scalar_Status;
      Potentially_Invalid : Boolean := False;
      Ada_Target          : Type_Kind_Id := Empty) return W_Term_Id
   with Pre => (if Potentially_Invalid then Present (Ada_Target));
   --  Return Arg of Source_Type converted to Target_Type, when both are of
   --  scalar types. Size is the shared size of both types, when arguments of
   --  the UC are integer types, which is used for conversion from an
   --  Unsigned type to a Signed one. Otherwise it is No_Uint.
   --  If Potentially_Invalid is True, wrap the result in a validity wrapper.
   --  The validity flag is set to True iff the return value is in the bounds
   --  of the return type of Ada_Target.

   function Precise_Composite_UC
     (Arg                 : W_Term_Id;
      Source_Type         : Type_Kind_Id;
      Target_Type         : Type_Kind_Id;
      Potentially_Invalid : Boolean) return W_Term_Id;
   --  Return Arg of Source_Type converted to Target_Type, when at least one
   --  is a composite type made up of integers. Convert Arg to a large-enough
   --  modular type, and convert that value to Target. If all types involved
   --  are modular, then this benefits from bitvector support in provers.
   --  If Potentially_Invalid is True, wrap it in a validity wrapper. The
   --  validity flag is set to True iff all scalar subcomponents of the return
   --  value are in the bounds of their subtype.

   ------------------------
   -- Get_UC_Theory_Name --
   ------------------------

   function Get_UC_Function
     (Source_Type, Target_Type : Type_Kind_Id; Potentially_Invalid : Boolean)
      return W_Identifier_Id
   is (M_UCs
         (Get_UC_Theory_Name (Source_Type, Target_Type, Potentially_Invalid))
         .UC_Id);

   ------------------------
   -- Get_UC_Theory_Name --
   ------------------------

   function Get_UC_Theory_Name
     (Source_Type, Target_Type : Type_Kind_Id; Potentially_Invalid : Boolean)
      return Symbol
   is
      Name : Unbounded_String :=
        To_Unbounded_String (To_String (WNE_UC_Prefix));
   begin
      Name :=
        Name & "___" & Capitalize_First (Full_Name (Retysp (Source_Type)));
      Name :=
        Name & "___" & Capitalize_First (Full_Name (Retysp (Target_Type)));

      if Potentially_Invalid then
         Name := Name & To_String (WNE_Potentially_Invalid_Suffix);
      end if;

      return NID (To_String (Name));
   end Get_UC_Theory_Name;

   -----------------------------
   -- Have_Same_Known_RM_Size --
   -----------------------------

   procedure Have_Same_Known_RM_Size
     (A, B        : Type_Kind_Id;
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
           To_Unbounded_String
             ("Size of "
              & Type_Name_For_Explanation (A)
              & " and "
              & Type_Name_For_Explanation (B)
              & " differ");
         return;
      end if;
      Result := True;
      Explanation := Null_Unbounded_String;
   end Have_Same_Known_RM_Size;

   ------------------------------
   -- Is_Overlay_Handled_As_UC --
   ------------------------------

   function Is_Overlay_Handled_As_UC
     (Obj : Object_Kind_Id) return True_Or_Explain is

   begin
      --  Constant objects are always translated using UC

      if Is_Constant_In_SPARK (Obj) then
         return (Ok => True);
      end if;

      --  Variable objects are only translated using UC if they overlay the
      --  whole object for now.

      declare
         Current : Object_Kind_Id := Obj;
      begin
         while Present (Overlaid_Entity (Current)) loop
            declare
               Decl    : constant Node_Id := Enclosing_Declaration (Current);
               Address : constant Node_Id := Get_Address_Expr (Decl);
            begin
               if Nkind (Prefix (Address)) in N_Identifier | N_Expanded_Name
               then
                  Current := Entity (Prefix (Address));
               else
                  return
                    False_With_Explain
                      ("mutable overlay of a subcomponent of an object");
               end if;
            end;
         end loop;
      end;

      return (Ok => True);
   end Is_Overlay_Handled_As_UC;

   -----------------------------------
   -- Is_UC_With_Precise_Definition --
   -----------------------------------

   function Is_UC_With_Precise_Definition
     (Source_Type, Target_Type : Type_Kind_Id; Potentially_Invalid : Boolean)
      return True_Or_Explain
   is
      Valid_Source, Valid_Target, Valid_Size : Boolean;
      Explanation                            : Unbounded_String;
      Check                                  : True_Or_Explain;

   begin
      --  Check that types are suitable for UC.

      Suitable_For_UC_Source (Source_Type, Valid_Source, Explanation);
      if not Valid_Source then
         --  Override explanation to avoid special characters
         return
           False_With_Explain
             ("type is unsuitable as source for unchecked conversion");
      end if;

      Suitable_For_UC_Target_UC_Wrap
        (Target_Type,
         Valid_Target,
         Explanation,
         Check_Validity => not Potentially_Invalid);

      if not Valid_Target then
         --  Override explanation to avoid special characters
         return
           False_With_Explain
             ("type is unsuitable as target for unchecked conversion");
      end if;

      Have_Same_Known_RM_Size
        (Source_Type, Target_Type, Valid_Size, Explanation);
      if not Valid_Size then
         --  Override explanation to avoid special characters
         return
           False_With_Explain
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

   -----------------------------------
   -- Object_Suitable_For_UC_Source --
   -----------------------------------

   procedure Object_Suitable_For_UC_Source
     (Obj : Node_Id; Result : out Boolean; Explanation : out Unbounded_String)
   is
      Common_Exp : constant String :=
        "; "
        & (if Nkind (Obj)
              in N_Defining_Identifier | N_Identifier | N_Expanded_Name
           then Source_Name (Obj)
           else "object")
        & " might have unused bits that are not modelled in SPARK";
      Typ        : constant Type_Kind_Id := Retysp (Etype (Obj));
      Obj_Size   : Uint;
      RM_Size    : Uint;
      Size_Str   : Unbounded_String;
   begin
      --  Check the absence of holes in the type's representation

      Suitable_For_UC_Source (Typ, Result, Explanation);

      --  As per ARM 13.1(7/5): If the size of an object is greater than that
      --  of its subtype, the additional bits are padding bits. For an
      --  elementary object, these padding bits are normally read and updated
      --  along with the others. For a composite object, it is unspecified
      --  whether padding bits are read or updated in any given composite
      --  operation.
      --  GNAT effectively reads and updates padding bits along with the others
      --  for discrete and fixed-point objects, but not floating-point objects.
      --  We rely on this behavior and do not consider padding bits as unused
      --  for these types. For floating-point types and composite types, we
      --  are conservative and don't assume anything of the sort.

      if not Result
        or else Has_Discrete_Type (Typ)
        or else Has_Fixed_Point_Type (Typ)
      then
         return;
      end if;

      --  Checks for absence of holes in Typ are done on the RM size. Check
      --  that there are no additional bits in Obj.

      Check_Known_Size_For_Object (Obj, Obj_Size, Explanation, Size_Str);

      --  If the object size and the RM_Size are not known but the check that
      --  Typ is suitable as source succeeds, it means that Obj is a
      --  dynamically constrained array with aliased components. In this case,
      --  the object size necessarily matches the RM_Size, there is nothing
      --  more to check.

      if No (Obj_Size) then
         pragma
           Assert
             (Is_Array_Type (Typ)
                and then Has_Aliased_Components (Etype (Typ)));
         return;
      end if;

      Check_Known_RM_Size (Typ, RM_Size, Explanation);
      pragma Assert (Present (RM_Size));

      if RM_Size /= Obj_Size then
         Result := False;
         Explanation :=
           Size_Str
           & " "
           & UI_Image (Obj_Size)
           & ", but "
           & Type_Name_For_Explanation (Typ)
           & " has Size "
           & UI_Image (RM_Size)
           & Common_Exp;
      end if;
   end Object_Suitable_For_UC_Source;

   --------------------------
   -- Precise_Composite_UC --
   --------------------------

   function Precise_Composite_UC
     (Arg                 : W_Term_Id;
      Source_Type         : Type_Kind_Id;
      Target_Type         : Type_Kind_Id;
      Potentially_Invalid : Boolean) return W_Term_Id
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

      type Target_Value is record
         Value      : W_Term_Id;
         Valid_Flag : W_Term_Id;
      end record
      with Predicate => (Valid_Flag /= Why_Empty) = Potentially_Invalid;

      --  Local subprograms

      function Contribute_Value
        (Base   : W_Type_Id;
         Expr   : W_Expr_Id;
         Offset : Uint;
         Size   : Uint;
         Typ    : Type_Kind_Id) return W_Expr_Id;
      --  Given a scalar expression Expr of type Typ, return its
      --  contribution to a modular value of type Base, when its
      --  bit representation takes Size bits at a given Offset in
      --  Base.

      function Expr_Index (Typ : Type_Kind_Id; Idx : Uint) return W_Expr_Id;
      --  Return the expression for indexing into array of type Typ

      function Extract_Value
        (Base   : W_Type_Id;
         Bits   : W_Expr_Id;
         Offset : Uint;
         Size   : Uint;
         Typ    : Type_Kind_Id) return Target_Value;
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
         Typ    : Type_Kind_Id) return Target_Value;
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
         Typ    : Type_Kind_Id) return W_Expr_Id
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
                   New_Modular_Constant (Value => Uint_1, Typ => Base),
                 Else_Part =>
                   New_Modular_Constant (Value => Uint_0, Typ => Base),
                 Typ       => Base);

         --  If the value is from a modular type, or from a signed
         --  type with no negative value, then simply convert it to
         --  Base.
         elsif Is_Unsigned_Type (Typ) then
            Value :=
              Insert_Scalar_Conversion
                (Domain => EW_Term, Expr => Expr, To => Base);

         --  Otherwise, we need to consider the bit representation
         --  of that (possibly negative) signed value as Base, and
         --  extract the low Size bits with the expression
         --  (uc_of_int Expr) and (2**Size - 1)
         else
            Value :=
              New_Call
                (Domain => EW_Term,
                 Name   => MF_BVs (Base).BW_And,
                 Typ    => Base,
                 Args   =>
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
                        (Value => Uint_2 ** Size - Uint_1, Typ => Base)));
         end if;

         --  Multiply this value by 2**Offset to get its
         --  contribution to the overall value.
         return
           New_Call
             (Domain => EW_Term,
              Name   => MF_BVs (Base).Mult,
              Typ    => Base,
              Args   =>
                (1 =>
                   New_Modular_Constant
                     (Value => Uint_2 ** Offset, Typ => Base),
                 2 => Value));
      end Contribute_Value;

      ----------------
      -- Expr_Index --
      ----------------

      function Expr_Index (Typ : Type_Kind_Id; Idx : Uint) return W_Expr_Id is
         Index_Typ : constant Type_Kind_Id := Etype (First_Index (Typ));
      begin
         if Is_Modular_Integer_Type (Index_Typ) then
            return
              New_Modular_Constant
                (Value => Idx, Typ => Base_Why_Type_No_Bool (Index_Typ));
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
         Typ    : Type_Kind_Id) return Target_Value
      is
         Mask    : constant W_Expr_Id :=
           New_Modular_Constant
             (Value => Uint_2 ** (Offset + Size) - Uint_1, Typ => Base);
         Divisor : constant W_Expr_Id :=
           New_Modular_Constant (Value => Uint_2 ** Offset, Typ => Base);
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
                      Args   => (1 => Bits, 2 => Mask)),
                 2 => Divisor));
         Res     : Target_Value;
      begin
         --  Special case for Boolean
         if Is_Standard_Boolean_Type (Typ) then
            Res :=
              (Value      =>
                 New_Conditional
                   (Condition =>
                      +New_Comparison
                         (Domain => EW_Term,
                          Symbol => Why_Eq,
                          Left   => Value,
                          Right  =>
                            New_Modular_Constant
                              (Value => Uint_1, Typ => Base)),
                    Then_Part => +True_Term,
                    Else_Part => +False_Term,
                    Typ       => EW_Bool_Type),
               Valid_Flag =>
                 (if Potentially_Invalid
                  then
                    New_Or_Term
                      (Left  =>
                         +New_Comparison
                            (Domain => EW_Term,
                             Symbol => Why_Eq,
                             Left   => Value,
                             Right  =>
                               New_Modular_Constant
                                 (Value => Uint_0, Typ => Base)),
                       Right =>
                         +New_Comparison
                            (Domain => EW_Term,
                             Symbol => Why_Eq,
                             Left   => Value,
                             Right  =>
                               New_Modular_Constant
                                 (Value => Uint_1, Typ => Base)))
                  else Why_Empty));

         --  If the value is to a modular type, or an enumeration
         --  with default 0-based representation, or to a signed
         --  type with no negative value, then simply convert it
         --  to Typ.

         elsif Is_Unsigned_Type (Typ) then
            Res :=
              (Value      =>
                 +Insert_Scalar_Conversion
                    (Domain => EW_Term,
                     Expr   => Value,
                     To     => EW_Abstract (Typ)),
               Valid_Flag =>
                 (if Potentially_Invalid
                  then
                    Is_Valid_Scalar
                      (Typ,
                       +Insert_Scalar_Conversion
                          (Domain => EW_Term,
                           Expr   => Value,
                           To     => EW_Split (Typ)))
                  else Why_Empty));

         --  Otherwise, we need to consider the bit representation
         --  of that (possibly negative) signed value, to see
         --  if the high bit is 1, in which case the value is
         --  negative. So we generate the value
         --  if Value >= 2**(Size-1) then Value-2**Size else Value
         else
            declare
               Top_Bit        : constant W_Expr_Id :=
                 New_Modular_Constant
                   (Value => Uint_2 ** (Size - Uint_1), Typ => Base);
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
                       2 => New_Integer_Constant (Value => 2 ** Size)));
               B_Value        : constant W_Expr_Id :=
                 New_Conditional
                   (Domain    => EW_Term,
                    Condition =>
                      New_Comparison
                        (Domain => EW_Term,
                         Symbol => MF_BVs (Base).Uge,
                         Left   => Value,
                         Right  => Top_Bit),
                    Then_Part => Negative_Value,
                    Else_Part =>
                      Insert_Scalar_Conversion
                        (Domain => EW_Term, Expr => Value, To => EW_Int_Type),
                    Typ       => EW_Int_Type);
            begin
               Res :=
                 (Value      =>
                    +Insert_Scalar_Conversion
                       (Domain => EW_Term,
                        Expr   => B_Value,
                        To     => EW_Abstract (Typ)),
                  Valid_Flag =>
                    (if Potentially_Invalid
                     then Is_Valid_Scalar (Typ, +B_Value)
                     else Why_Empty));
            end;
         end if;

         --  If Potentially_Invalid is set, avoid assuming invalid values that
         --  could be incompatible with the dynamic invariant of the object.

         if Potentially_Invalid then
            Res.Value :=
              New_Conditional
                (Condition => Res.Valid_Flag,
                 Then_Part => Res.Value,
                 Else_Part => +Why_Default_Value (EW_Term, Typ),
                 Typ       => EW_Abstract (Typ));
         end if;

         return Res;
      end Extract_Value;

      --------------------------
      -- Get_Type_Offset_List --
      --------------------------

      procedure Get_Source_Elements
        (Typ      : Type_Kind_Id;
         Offset   : Uint;
         Size     : Uint;
         Expr     : W_Term_Id;
         Elements : in out List) is
      begin
         if Is_Scalar_Type (Typ) then
            Elements.Append
              (Source_Element'
                 (Typ => Typ, Offset => Offset, Size => Size, Expr => Expr));

         elsif Is_Record_Type (Typ) then
            declare
               Comp : Node_Id := First_Component (Typ);
            begin
               while Present (Comp) loop
                  declare
                     Size          : Uint;
                     Size_Str, Exp : Unbounded_String;
                  begin
                     Record_Component_Size (Typ, Comp, Size, Exp, Size_Str);
                     Get_Source_Elements
                       (Typ      => Retysp (Etype (Comp)),
                        Offset   => Offset + Component_Bit_Offset (Comp),
                        Size     => Size,
                        Expr     =>
                          New_Ada_Record_Access
                            (Ada_Node => Types.Empty,
                             Name     => +Expr,
                             Ty       => Typ,
                             Field    => Comp),
                        Elements => Elements);
                     Next_Component (Comp);
                  end;
               end loop;
            end;

         elsif Is_Array_Type (Typ) then
            declare
               Index     : constant Node_Id := First_Index (Typ);
               Rng       : constant Node_Id := Get_Range (Index);
               Low       : constant Uint := Expr_Value (Low_Bound (Rng));
               High      : constant Uint := Expr_Value (High_Bound (Rng));
               Cur       : Uint;
               Comp_Size : constant Uint :=
                 Get_Attribute_Value (Typ, Attribute_Component_Size);
            begin
               if Low <= High then
                  Cur := Low;
                  while Cur <= High loop
                     Get_Source_Elements
                       (Typ      => Retysp (Component_Type (Typ)),
                        Offset   => (Cur - Low) * Comp_Size,
                        Size     => Comp_Size,
                        Expr     =>
                          New_Array_Access
                            (Ar    => Expr,
                             Index => (1 => Expr_Index (Typ, Cur))),
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
         Typ    : Type_Kind_Id) return Target_Value is
      begin
         if Is_Scalar_Type (Typ) then
            return
              Extract_Value
                (Base   => Base,
                 Bits   => Bits,
                 Offset => Offset,
                 Size   => Size,
                 Typ    => Typ);

         elsif Is_Record_Type (Typ) then
            declare
               Comps   : constant Component_Sets.Set :=
                 Get_Component_Set (Typ);
               Assocs  :
                 W_Field_Association_Array (1 .. Integer (Comps.Length));
               Flags   :
                 W_Field_Association_Array (1 .. Integer (Comps.Length));
               Index   : Positive := 1;
               F_Index : Positive := 1;
            begin
               for Comp of Comps loop
                  declare
                     F_Value : constant Target_Value :=
                       Reconstruct_Value
                         (Base   => Base,
                          Bits   => Bits,
                          Offset => Offset + Component_Bit_Offset (Comp),
                          Size   => Esize (Comp),
                          Typ    => Retysp (Etype (Comp)));
                  begin
                     Assocs (Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  =>
                            To_Why_Id (Comp, Local => False, Rec => Typ),
                          Value  => +F_Value.Value);
                     Index := Index + 1;

                     if Potentially_Invalid
                       and then not Comp_Has_Only_Valid_Values (Comp, Typ).Ok
                     then
                        Flags (F_Index) :=
                          New_Field_Association
                            (Domain => EW_Term,
                             Field  =>
                               To_Why_Id
                                 (Comp,
                                  Local     => False,
                                  Rec       => Base_Retysp (Typ),
                                  From_Tree => Validity_Tree),
                             Value  => +F_Value.Valid_Flag);
                        F_Index := F_Index + 1;
                     end if;
                  end;
               end loop;

               return
                 (Value      =>
                    New_Record_Aggregate
                      (Associations =>
                         (1 =>
                            New_Field_Association
                              (Domain => EW_Term,
                               Field  => E_Symb (Typ, WNE_Rec_Split_Fields),
                               Value  =>
                                 New_Record_Aggregate
                                   (Associations => Assocs))),
                       Typ          => EW_Abstract (Typ)),
                  Valid_Flag =>
                    (if Potentially_Invalid
                     then
                       New_Record_Aggregate
                         (Associations => Flags (1 .. F_Index - 1),
                          Typ          => Get_Validity_Tree_Type (Typ))
                     else Why_Empty));
            end;

         elsif Is_Array_Type (Typ) then
            declare
               Index : constant Node_Id := First_Index (Typ);
               Rng   : constant Node_Id := Get_Range (Index);
               Low   : constant Uint := Expr_Value (Low_Bound (Rng));
               High  : constant Uint := Expr_Value (High_Bound (Rng));
               Cur   : Uint;
               Ar    : W_Expr_Id := +E_Symb (Typ, WNE_Dummy);
               Flags : W_Term_Id :=
                 (if Potentially_Invalid
                  then New_Valid_Value_For_Type (Typ)
                  else Why_Empty);
            begin
               if Low <= High then
                  Cur := Low;
                  while Cur <= High loop
                     declare
                        Comp_Size : constant Uint :=
                          Get_Attribute_Value (Typ, Attribute_Component_Size);
                        C_Value   : constant Target_Value :=
                          Reconstruct_Value
                            (Base   => Base,
                             Bits   => Bits,
                             Offset => Offset + (Cur - Low) * Comp_Size,
                             Size   => Comp_Size,
                             Typ    => Retysp (Component_Type (Typ)));
                     begin
                        Ar :=
                          New_Array_Update
                            (Ada_Node => Types.Empty,
                             Ar       => Ar,
                             Index    => (1 => Expr_Index (Typ, Cur)),
                             Value    => +C_Value.Value,
                             Domain   => EW_Term);

                        if Potentially_Invalid then
                           Flags :=
                             +New_Validity_Tree_Array_Update
                                (Name   => +Flags,
                                 Index  => (1 => Expr_Index (Typ, Cur)),
                                 Value  => +C_Value.Valid_Flag,
                                 Ty     => Typ,
                                 Domain => EW_Term);
                        end if;
                     end;
                     Cur := Cur + 1;
                  end loop;
               end if;

               return (Value => +Ar, Valid_Flag => Flags);
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
        (if Target_Size <= Uint_8
         then EW_BitVector_8_Type
         elsif Target_Size <= Uint_16
         then EW_BitVector_16_Type
         elsif Target_Size <= Uint_32
         then EW_BitVector_32_Type
         elsif Target_Size <= Uint_64
         then EW_BitVector_64_Type
         elsif Target_Size <= Uint_128
         then EW_BitVector_128_Type
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
              Source_Type   => Type_Of_Node (Source_Type),
              Target_Type   => Base,
              Source_Status => Get_Scalar_Status (Source_Type),
              Target_Status => Modular);

      --  1.b Otherwise extract all scalar subcomponents from the
      --  composite value and sum up their contributions to the
      --  value of type Base.

      else
         Get_Source_Elements (Source_Type, Uint_0, Uint_0, +Arg, Source_Elems);
         Conv := New_Modular_Constant (Value => Uint_0, Typ => Base);

         for Elem of Source_Elems loop
            Conv :=
              New_Call
                (Name => MF_BVs (Base).Add,
                 Typ  => Base,
                 Args =>
                   (1 => +Conv,
                    2 =>
                      Contribute_Value
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
             (Arg                 => Conv,
              Size                => No_Uint,
              Source_Type         => Base,
              Target_Type         => Type_Of_Node (Target_Type),
              Source_Status       => Modular,
              Target_Status       => Get_Scalar_Status (Target_Type),
              Potentially_Invalid => Potentially_Invalid,
              Ada_Target          => Target_Type);

      --  2.b Otherwise recursively reconstruct all scalar
      --  subcomponents from the value of type Base.

      else
         declare
            Val : constant Target_Value :=
              Reconstruct_Value
                (Base   => Base,
                 Bits   => +Conv,
                 Offset => Uint_0,
                 Size   => Get_Attribute_Value (Target_Type, Attribute_Size),
                 Typ    => Target_Type);
         begin
            Def := Val.Value;

            --  If Potentially_Invalid is set, reconstruct the wrapper

            if Potentially_Invalid then
               Def :=
                 +New_Function_Validity_Wrapper_Value
                    (Ty         => Target_Type,
                     Valid_Flag => +Val.Valid_Flag,
                     Value      => +Val.Value);
            end if;
         end;
      end if;
      return Def;
   end Precise_Composite_UC;

   ------------------------
   -- Precise_Integer_UC --
   ------------------------

   function Precise_Integer_UC
     (Arg                 : W_Term_Id;
      Size                : Uint;
      Source_Type         : W_Type_Id;
      Target_Type         : W_Type_Id;
      Source_Status       : Scalar_Status;
      Target_Status       : Scalar_Status;
      Potentially_Invalid : Boolean := False;
      Ada_Target          : Type_Kind_Id := Empty) return W_Term_Id
   is
      Source_Base_Type : constant W_Type_Id :=
        Base_Why_Type_No_Bool (Source_Type);
      Target_Base_Type : constant W_Type_Id :=
        Base_Why_Type_No_Bool (Target_Type);
      Conv             : W_Term_Id;
   begin
      Conv := Insert_Simple_Conversion (Expr => Arg, To => Source_Base_Type);

      if Source_Status = Target_Status then
         null;  --  Trivial case of UC between identical types

      elsif Source_Status = Unsigned and then Target_Status = Modular then
         null;  --  Unsigned value can be directly converted to modular

      elsif Source_Status = Modular and then Target_Status = Unsigned then
         null;  --  Modular value can be directly converted to unsigned

      --  Apply the appropriate UC function for conversions between Modular
      --  and Signed.

      elsif Source_Status = Modular and then Target_Status = Signed then
         Conv :=
           New_Call
             (Name => MF_BVs (Source_Base_Type).UC_To_Int,
              Args => (1 => +Conv),
              Typ  => EW_Int_Type);

      elsif Source_Status = Signed and then Target_Status = Modular then
         Conv :=
           New_Call
             (Name => MF_BVs (Target_Base_Type).UC_Of_Int,
              Args => (1 => +Conv),
              Typ  => Target_Base_Type);

      --  Otherwise, this is a conversion between Unsigned and Signed.
      --  We need to consider the bit representation of that (possibly
      --  negative) signed value, to see if the high bit is 1, in which
      --  case the Signed value is negative.

      elsif Source_Status = Unsigned and then Target_Status = Signed then
         --  Generate the value
         --  if Conv >= 2**(Size-1) then Conv-2**Size else Conv
         declare
            Top_Bit        : constant W_Term_Id :=
              New_Integer_Constant (Value => Uint_2 ** (Size - Uint_1));
            Negative_Value : constant W_Term_Id :=
              New_Call
                (Name => Int_Infix_Subtr,
                 Typ  => EW_Int_Type,
                 Args =>
                   (1 => +Conv,
                    2 => New_Integer_Constant (Value => 2 ** Size)));
         begin
            Conv :=
              New_Conditional
                (Condition =>
                   New_Comparison
                     (Symbol => Int_Infix_Ge, Left => Conv, Right => Top_Bit),
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
                (Name => Int_Infix_Add,
                 Typ  => EW_Int_Type,
                 Args =>
                   (1 => +Conv,
                    2 => New_Integer_Constant (Value => 2 ** Size)));
         begin
            Conv :=
              New_Conditional
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

      --  If Potentially_Invalid is True, it is necessary to reconstruct the
      --  wrapper. Only assume the value of the result if it is valid to avoid
      --  inconsistent assumptions with the dynamic invariant of the result.
      --  Otherwise use a dummy of the type.

      if Potentially_Invalid then
         declare
            Range_Ty     : constant Type_Kind_Id := Retysp (Ada_Target);
            Conv_To_Base : constant W_Term_Id :=
              New_Temp_For_Expr
                (Insert_Simple_Conversion
                   (Expr => Conv, To => Target_Base_Type));
            Valid_Flag   : constant W_Term_Id :=
              New_Temp_For_Expr (Is_Valid_Scalar (Range_Ty, Conv_To_Base));

         begin
            return
              Binding_For_Temp
                (Tmp     => Conv_To_Base,
                 Context =>
                   Binding_For_Temp
                     (Tmp     => Valid_Flag,
                      Context =>
                        +New_Function_Validity_Wrapper_Value
                           (Ty         => Range_Ty,
                            Valid_Flag => +Valid_Flag,
                            Value      =>
                              +New_Conditional
                                 (Condition => Valid_Flag,
                                  Then_Part =>
                                    Insert_Simple_Conversion
                                      (Expr => Conv_To_Base,
                                       To   => Target_Type),
                                  Else_Part =>
                                    Insert_Simple_Conversion
                                      (Expr =>
                                         +Why_Default_Value
                                            (EW_Term, Range_Ty),
                                       To   => Target_Type)))));
         end;
      else
         return Insert_Simple_Conversion (Expr => Conv, To => Target_Type);
      end if;
   end Precise_Integer_UC;

   -----------------------------
   -- Suitable_For_Precise_UC --
   -----------------------------

   function Suitable_For_Precise_UC
     (Arg_Typ : Type_Kind_Id) return True_Or_Explain
   is
      Typ : constant Type_Kind_Id := Retysp (Arg_Typ);
   begin
      case Ekind (Typ) is
         when Integer_Kind     =>
            if Has_Biased_Representation (Typ) then
               return False_With_Explain ("type with biased representation");

            elsif Has_Modular_Integer_Type (Typ)
              and then Has_No_Bitwise_Operations_Annotation (Typ)
            then
               return
                 False_With_Explain
                   ("type with No_Bitwise_Operations annotation");
            end if;

         when Enumeration_Kind =>
            if Has_Enumeration_Rep_Clause (Typ) then
               declare
                  Lit : Node_Id := First_Literal (Typ);
                  Pos : Uint := Uint_0;
               begin
                  loop
                     if Enumeration_Rep (Lit) /= Pos then
                        return
                          False_With_Explain
                            ("enumeration with non-default representation");
                     end if;
                     Lit := Next_Literal (Lit);
                     Pos := Pos + 1;
                     exit when No (Lit);
                  end loop;
               end;
            end if;

         when Record_Kind      =>

            --  Tagged types and discriminants are not supported in UC

            if Is_Tagged_Type (Typ) then
               pragma Assert (False);

            elsif Has_Discriminants (Typ) then
               pragma Assert (False);

            elsif Reverse_Storage_Order (Base_Retysp (Typ)) then
               return False_With_Explain ("type has reverse storage order");
            end if;

            declare
               Comp : Entity_Id := First_Component (Typ);
            begin
               while Present (Comp) loop
                  if No (Component_Bit_Offset (Comp)) then
                     return False_With_Explain ("component offset not known");
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

         when Array_Kind       =>
            declare
               Check : constant True_Or_Explain :=
                 Suitable_For_Precise_UC (Component_Type (Typ));
            begin
               if not Check.Ok then
                  return Check;
               end if;
            end;

            if Number_Dimensions (Typ) > Uint_1 then
               return False_With_Explain ("array has multiple dimensions");

            elsif Reverse_Storage_Order (Base_Retysp (Typ)) then
               return False_With_Explain ("type has reverse storage order");
            end if;

         when others           =>
            return False_With_Explain ("elementary non-integer type");
      end case;

      return True_Or_Explain'(Ok => True);
   end Suitable_For_Precise_UC;

   --------------------------------
   -- Compute_Size_Of_Components --
   --------------------------------

   procedure Compute_Size_Of_Components
     (Typ         : Type_Kind_Id;
      Result      : out Boolean;
      Size        : out Uint;
      Explanation : out Unbounded_String)
   is
      Typ_Name : constant String := Type_Name_For_Explanation (Typ);

   begin
      --  Default initialization for GNAT SAS
      Size := Uint_0;

      if Is_Array_Type (Typ) then

         --  Unconstrained types are not allowed as source or target of UC

         pragma Assert (Is_Constrained (Typ));

         declare
            Comp_Typ  : constant Type_Kind_Id := Retysp (Component_Type (Typ));
            Comp_Size : Uint;
            Index     : Node_Id;

         begin
            if Is_Scalar_Type (Comp_Typ) then
               Comp_Size :=
                 Get_Attribute_Value (Typ, Attribute_Component_Size);
            else
               Compute_Size_Of_Components
                 (Comp_Typ, Result, Comp_Size, Explanation);
               if not Result then
                  return;
               end if;
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
                    Size
                    * (Expr_Value (High_Bound (Rng))
                       - Expr_Value (Low_Bound (Rng))
                       + 1);
                  Next_Index (Index);
               end;
            end loop;
         end;

      elsif Is_Record_Type (Typ) then
         if Has_Discriminants (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " has discriminants");
            return;
         end if;

         for Comp of Get_Component_Set (Typ) loop
            declare
               Comp_Ty   : constant Type_Kind_Id := Retysp (Etype (Comp));
               Comp_Size : Uint;
               Size_Str  : Unbounded_String;
            begin
               if Is_Scalar_Type (Comp_Ty) then
                  Record_Component_Size
                    (Typ, Comp, Comp_Size, Size_Str, Explanation);
                  pragma Assert (Present (Comp_Size));
               else
                  Compute_Size_Of_Components
                    (Comp_Ty, Result, Comp_Size, Explanation);

                  if not Result then
                     return;
                  end if;
               end if;
               Size := Size + Comp_Size;
            end;
         end loop;

      else
         pragma Assert (Is_Scalar_Type (Typ));

         --  We only come here if the top-level type is a scalar type. Also,
         --  this procedure is only called for Unchecked conversion. It means
         --  that RM_Size is the correct size to use here (ARM K.2 226).

         pragma Assert (Known_RM_Size (Typ));
         Size := RM_Size (Typ);
      end if;

      Result := True;
      Explanation := Null_Unbounded_String;
   end Compute_Size_Of_Components;

   ------------------------------------
   -- Create_Module_For_UC_If_Needed --
   ------------------------------------

   procedure Create_Module_For_UC_If_Needed
     (Source_Type, Target_Type : Type_Kind_Id; Potentially_Invalid : Boolean)
   is

      procedure Generate_Inversion_Axiom
        (Source_Type, Target_Type : Type_Kind_Id;
         Module                   : M_UC_Type;
         Inv_Fun                  : W_Identifier_Id);
      --  Create a module for the inversion axiom of the unchecked conversion
      --  function in Module.

      function Inversion_Axiom_OK
        (Source_Type, Target_Type : Type_Kind_Id) return Boolean;
      --  Return True if it is safe to generate the inversion axiom for the
      --  conversion. It is only the case if both directions are valid UCs.

      ------------------------------
      -- Generate_Inversion_Axiom --
      ------------------------------

      procedure Generate_Inversion_Axiom
        (Source_Type, Target_Type : Type_Kind_Id;
         Module                   : M_UC_Type;
         Inv_Fun                  : W_Identifier_Id)
      is
         Axiom_Module : constant W_Module_Id :=
           New_Module
             (File => No_Symbol,
              Name =>
                NID
                  (Img (Get_Name (Module.Module))
                   & To_String (WNE_Axiom_Suffix)));
         Th           : Theory_UC :=
           Open_Theory
             (WF_Context,
              Axiom_Module,
              Comment =>
                "Module for the inversion axiom of Unchecked_Conversion "
                & "function from """
                & Get_Name_String (Chars (Source_Type))
                & """"
                & (if Sloc (Source_Type) > 0
                   then
                     " defined at "
                     & Build_Location_String (Sloc (Source_Type))
                   else "")
                & "to """
                & Get_Name_String (Chars (Target_Type))
                & """"
                & (if Sloc (Target_Type) > 0
                   then
                     " defined at "
                     & Build_Location_String (Sloc (Target_Type))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
         Source_Id    : constant W_Identifier_Id :=
           New_Temp_Identifier
             (Base_Name => "source", Typ => Type_Of_Node (Source_Type));
         UC_Call      : constant W_Term_Id :=
           New_Call
             (Name => Module.UC_Id,
              Args => (1 => +Source_Id),
              Typ  => Get_Typ (Module.UC_Id));

      begin
         --  Generate:
         --
         --    forall source : source_type [uc_id source].
         --      dynamic_invariant source ->
         --        inv_fun (uc_id source) = source

         Emit
           (Th,
            New_Guarded_Axiom
              (Name     => NID ("inversion_axiom"),
               Binders  =>
                 Binder_Array'(1 => (B_Name => Source_Id, others => <>)),
               Triggers =>
                 New_Triggers
                   (Triggers => (1 => New_Trigger (Terms => (1 => +UC_Call)))),
               Pre      =>
                 Compute_Dynamic_Invariant
                   (Expr   => +Source_Id,
                    Ty     => Source_Type,
                    Params => Logic_Params),
               Def      =>
                 New_Comparison
                   (Symbol => Why_Eq,
                    Left   =>
                      New_Call
                        (Name => Inv_Fun,
                         Args => (1 => +UC_Call),
                         Typ  => Get_Typ (Inv_Fun)),
                    Right  => +Source_Id),
               Dep      =>
                 New_Axiom_Dep (Name => Module.UC_Id, Kind => EW_Axdep_Func)));

         Close_Theory (Th, Kind => Definition_Theory);
         Record_Extra_Dependency
           (Defining_Module => Module.Module, Axiom_Module => Th.Module);
      end Generate_Inversion_Axiom;

      ------------------------
      -- Inversion_Axiom_OK --
      ------------------------

      function Inversion_Axiom_OK
        (Source_Type, Target_Type : Type_Kind_Id) return Boolean
      is
         Valid       : Boolean;
         Explanation : Unbounded_String;

      begin
         Suitable_For_UC_Source (Source_Type, Valid, Explanation);
         if not Valid then
            return False;
         end if;

         Suitable_For_UC_Target_UC_Wrap (Source_Type, Valid, Explanation);

         if not Valid then
            return False;
         end if;

         Suitable_For_UC_Source (Target_Type, Valid, Explanation);
         if not Valid then
            return False;
         end if;

         Suitable_For_UC_Target_UC_Wrap (Target_Type, Valid, Explanation);

         if not Valid then
            return False;
         end if;

         Have_Same_Known_RM_Size
           (Source_Type, Target_Type, Valid, Explanation);
         return Valid;
      end Inversion_Axiom_OK;

      Precise_UC  : constant True_Or_Explain :=
        Is_UC_With_Precise_Definition
          (Source_Type, Target_Type, Potentially_Invalid);
      Module_Name : constant Symbol :=
        Get_UC_Theory_Name (Source_Type, Target_Type, Potentially_Invalid);

   begin
      if M_UCs.Contains (Module_Name) then
         return;
      end if;

      declare
         UC_Module : constant W_Module_Id :=
           New_Module (File => No_Symbol, Name => Module_Name);
         UC_Id     : constant W_Identifier_Id :=
           New_Identifier
             (Symb   => NID (To_String (WNE_UC_Function)),
              Module => UC_Module,
              Domain => EW_Term,
              Typ    => Type_Of_Node (Target_Type));
         Source_Id : constant W_Identifier_Id :=
           New_Temp_Identifier
             (Base_Name => "source", Typ => Type_Of_Node (Source_Type));
         Th        : Theory_UC;
         Def       : W_Term_Id;

      begin
         M_UCs.Insert (Module_Name, (UC_Module, UC_Id));

         Th :=
           Open_Theory
             (WF_Context,
              UC_Module,
              Comment =>
                "Module for instance of Unchecked_Conversion function from "
                & """"
                & Get_Name_String (Chars (Source_Type))
                & """"
                & (if Sloc (Source_Type) > 0
                   then
                     " defined at "
                     & Build_Location_String (Sloc (Source_Type))
                   else "")
                & "to """
                & Get_Name_String (Chars (Target_Type))
                & """"
                & (if Sloc (Target_Type) > 0
                   then
                     " defined at "
                     & Build_Location_String (Sloc (Target_Type))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);

         if not Precise_UC.Ok then

            Def := Why_Empty;

         elsif Is_Scalar_Type (Source_Type)
           and then Is_Scalar_Type (Target_Type)
         then
            Def :=
              Precise_Integer_UC
                (Arg                 => +Source_Id,
                 Size                =>
                   Get_Attribute_Value (Source_Type, Attribute_Size),
                 Source_Type         => Type_Of_Node (Source_Type),
                 Target_Type         => Type_Of_Node (Target_Type),
                 Source_Status       => Get_Scalar_Status (Source_Type),
                 Target_Status       => Get_Scalar_Status (Target_Type),
                 Potentially_Invalid => Potentially_Invalid,
                 Ada_Target          => Target_Type);

         --  At least one of Source or Target is a composite type made up
         --  of integers. Convert Source to a large-enough modular type,
         --  and convert that value to Target. If all types involved are
         --  modular, then this benefits from bitvector support in provers.

         else
            Def :=
              Precise_Composite_UC
                (Arg                 => +Source_Id,
                 Source_Type         => Source_Type,
                 Target_Type         => Target_Type,
                 Potentially_Invalid => Potentially_Invalid);
         end if;

         --  Generate a logic function for the unchecked conversion

         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (UC_Id),
               Binders     =>
                 Binder_Array'(1 => (B_Name => Source_Id, others => <>)),
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Def         => +Def,
               Return_Type =>
                 (if Potentially_Invalid
                  then Validity_Wrapper_Type (Target_Type)
                  else Type_Of_Node (Target_Type))));

         Close_Theory (Th, Definition_Theory);
      end;

      --  Generate axiom modules if the inverse of the UC function already
      --  exists.

      if not Potentially_Invalid then
         declare
            Inv_Module : constant Symbol :=
              Get_UC_Theory_Name
                (Source_Type         => Target_Type,
                 Target_Type         => Source_Type,
                 Potentially_Invalid => False);
            Position   : constant Name_Id_UC_Map.Cursor :=
              M_UCs.Find (Inv_Module);
         begin
            if Name_Id_UC_Map.Has_Element (Position)
              and then Inversion_Axiom_OK (Source_Type, Target_Type)
            then
               Generate_Inversion_Axiom
                 (Source_Type => Source_Type,
                  Target_Type => Target_Type,
                  Module      => M_UCs (Module_Name),
                  Inv_Fun     => M_UCs (Position).UC_Id);

               if Source_Type /= Target_Type then
                  Generate_Inversion_Axiom
                    (Source_Type => Target_Type,
                     Target_Type => Source_Type,
                     Module      => M_UCs (Position),
                     Inv_Fun     => M_UCs (Module_Name).UC_Id);
               end if;
            end if;
         end;
      end if;
   end Create_Module_For_UC_If_Needed;

   ---------------------
   -- Suitable_For_UC --
   ---------------------

   procedure Suitable_For_UC
     (Typ         : Type_Kind_Id;
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
            Explanation :=
              To_Unbounded_String (Typ_Name & " is a tagged type");
            return Pass;

         elsif Full_View_Not_In_SPARK (Typ) then
            Explanation :=
              To_Unbounded_String
                (Typ_Name & " is not entirely visible in SPARK");
            return Pass;

         elsif Is_Concurrent_Type (Typ) then
            pragma
              Annotate
                (Xcov,
                 Exempt_On,
                 "The frontend crashes on UC on tasks and "
                   & "rejectes UC on protected types");
            Explanation :=
              To_Unbounded_String (Typ_Name & " is a concurrent type");
            return Pass;
            pragma Annotate (Xcov, Exempt_Off);

         elsif Is_Access_Type (Typ) then
            Explanation :=
              To_Unbounded_String (Typ_Name & " is an access type");
            return Pass;

         --  GNAT only guarantees to zero-out extra bits when writing in a
         --  scalar component if its size is not larger than the largest
         --  floating-point type (for floats) or the largest integer type (for
         --  other scalar types) on the target.

         elsif Is_Floating_Point_Type (Typ)
           and then
             Get_Attribute_Value (Typ, Attribute_Size)
             > Ttypes.Standard_Long_Long_Float_Size
         then
            Explanation :=
              To_Unbounded_String ("too large value of Size for " & Typ_Name);
            return Pass;

         elsif Is_Scalar_Type (Typ)
           and then
             Get_Attribute_Value (Typ, Attribute_Size)
             > Ttypes.Standard_Long_Long_Long_Integer_Size
         then
            Explanation :=
              To_Unbounded_String ("too large value of Size for " & Typ_Name);
            return Pass;

         else
            return Continue;
         end if;
      end Type_Unsuitable_For_UC;

      function Has_Unsuitable_Component is new
        Traverse_Subcomponents (Type_Unsuitable_For_UC);

   begin
      Result := not Has_Unsuitable_Component (Typ);
   end Suitable_For_UC;

   ----------------------------
   -- Suitable_For_UC_Source --
   ----------------------------

   procedure Suitable_For_UC_Source
     (Typ         : Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
      Typ_Name   : constant String := Type_Name_For_Explanation (Typ);
      Common_Exp : constant String :=
        "; "
        & Typ_Name
        & " might have unused bits that are not modelled in SPARK";

      procedure Check_No_Holes_In_Typ
        (Typ : Type_Kind_Id; Size : Uint; Size_Str : String);
      --  Check that the sum of the components of Typ is equal to Size. If not,
      --  store an explanation in Explanation. Set result to the result of the
      --  check.

      ---------------------------
      -- Check_No_Holes_In_Typ --
      ---------------------------

      procedure Check_No_Holes_In_Typ
        (Typ : Type_Kind_Id; Size : Uint; Size_Str : String)
      is
         Sum_Comp : Uint;
      begin
         Compute_Size_Of_Components (Typ, Result, Sum_Comp, Explanation);

         if not Result then
            Append (Explanation, Common_Exp);
         elsif Size = Sum_Comp then
            Result := True;
         else
            Result := False;
            Explanation :=
              To_Unbounded_String
                (Type_Name_For_Explanation (Typ)
                 & " has minimal size "
                 & UI_Image (Sum_Comp)
                 & ", but "
                 & Size_Str
                 & " was declared as "
                 & UI_Image (Size)
                 & Common_Exp);
         end if;
      end Check_No_Holes_In_Typ;

      Size : Uint;

   begin
      Suitable_For_UC (Typ, Result, Explanation);
      if not Result then
         return;
      end if;

      --  Scalar types cannot have holes, as all bits are relevant for their
      --  values. Instead, such objects are considered to have invalid values.

      if Has_Scalar_Type (Typ) then
         return;
      end if;

      --  Check that there is no holes

      Check_Known_RM_Size (Typ, Size, Explanation);

      if No (Size) then

         --  Arrays with aliased components cannot have holes between
         --  components. It is enough to check that the components themselves
         --  have no holes.

         if Is_Array_Type (Typ) and then Has_Aliased_Components (Etype (Typ))
         then
            declare
               Comp_Ty   : constant Type_Kind_Id :=
                 Retysp (Component_Type (Typ));
               Comp_Size : constant Uint :=
                 Get_Attribute_Value (Typ, Attribute_Component_Size);
            begin
               if No (Comp_Size) then
                  Result := False;
                  Explanation :=
                    To_Unbounded_String
                      (Typ_Name
                       & " doesn't have a Component_Size representation clause"
                       & " or aspect");
                  return;
               end if;

               Check_No_Holes_In_Typ (Comp_Ty, Comp_Size, "Component_Size");
               return;
            end;
         else
            Result := False;
            Append (Explanation, Common_Exp);
            return;
         end if;
      end if;

      Check_No_Holes_In_Typ (Typ, Size, "Size");
   end Suitable_For_UC_Source;

   ----------------------------
   -- Suitable_For_UC_Target --
   ----------------------------

   procedure Suitable_For_UC_Target
     (Typ            : Type_Kind_Id;
      Size           : Uint;
      Size_Str       : String;
      For_UC         : Boolean;
      Result         : out Boolean;
      Explanation    : out Unbounded_String;
      Check_Validity : Boolean := True) is
   begin
      Suitable_For_UC (Typ, Result, Explanation);

      --  Check for invalid values

      if Result and then Check_Validity then
         declare
            Res          : True_Or_Explain := (Ok => True);
            Continuation : constant String :=
              (if For_UC
               then
                 "; invalid values could result from the unchecked "
                 & "conversion [SPARK RM 13.9]"
               else
                 "; aliased object could have invalid values "
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
     (Typ            : Type_Kind_Id;
      Obj            : Node_Id;
      Result         : out Boolean;
      Explanation    : out Unbounded_String;
      Check_Validity : Boolean := True)
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
         Explanation,
         Check_Validity);
   end Suitable_For_UC_Target_Overlay_Wrap;

   ------------------------------------
   -- Suitable_For_UC_Target_UC_Wrap --
   ------------------------------------

   procedure Suitable_For_UC_Target_UC_Wrap
     (Typ            : Type_Kind_Id;
      Result         : out Boolean;
      Explanation    : out Unbounded_String;
      Check_Validity : Boolean := True)
   is
      Size : Uint := Uint_0;
   begin
      if Is_Scalar_Type (Typ) then
         --  ARM K.2 226
         Check_Known_RM_Size (Typ, Size, Explanation);
         pragma Assert (not No (Size));
      end if;
      Suitable_For_UC_Target
        (Typ, Size, "Size", True, Result, Explanation, Check_Validity);
   end Suitable_For_UC_Target_UC_Wrap;

   procedure Types_Compatible_Alignment
     (Src_Ty      : Type_Kind_Id;
      Tar_Ty      : Type_Kind_Id;
      Valid       : out Boolean;
      Explanation : out Unbounded_String)
   is
      SA : constant Uint := Get_Attribute_Value (Src_Ty, Attribute_Alignment);
      TA : constant Uint := Get_Attribute_Value (Tar_Ty, Attribute_Alignment);
   begin
      if No (SA) then
         Valid := False;
         Explanation :=
           To_Unbounded_String
             (Source_Name (Src_Ty)
              & " doesn't have an "
              & "Alignment representation clause or aspect");
         return;
      end if;
      if No (TA) then
         Valid := False;
         Explanation :=
           To_Unbounded_String
             (Source_Name (Tar_Ty)
              & " doesn't have an "
              & "Alignment representation clause or aspect");
         return;
      end if;
      if SA mod TA /= Uint_0 then
         Valid := False;
         Explanation :=
           To_Unbounded_String
             ("alignment of "
              & Source_Name (Src_Ty)
              & " (which is "
              & UI_Image (SA)
              & ")"
              & " must be a multiple of the "
              & "alignment of "
              & Source_Name (Tar_Ty)
              & " (which is "
              & UI_Image (TA)
              & ")");
         return;
      end if;
      Valid := True;
      Explanation := Null_Unbounded_String;
   end Types_Compatible_Alignment;

end Gnat2Why.Unchecked_Conversion;
