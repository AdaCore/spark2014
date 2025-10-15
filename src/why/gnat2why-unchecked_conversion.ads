------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--            G N A T 2 W H Y - U N C H E C K E D _ C O N V E R S I O N     --
--                                                                          --
--                                  S p e c                                 --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with SPARK_Util;            use SPARK_Util;
with SPARK_Atree.Entities;  use SPARK_Atree.Entities;
with Types;                 use Types;
with Why.Ids;               use Why.Ids;
with Uintp;                 use Uintp;

package Gnat2Why.Unchecked_Conversion is

   function Is_UC_With_Precise_Definition
     (E : Entity_Id) return True_Or_Explain
   with Pre => Is_Unchecked_Conversion_Instance (E);
   --  Return whether E is an UC for which a precise definition is given

   procedure Suitable_For_UC
     (Typ         : Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  This function is used by Suitable_For_UC_Source and
   --  Suitable_For_UC_Target. It checks common properties of target and source
   --  types of unchecked conversions. If Result is False, Explanation contains
   --  a string explaining why Typ is cannot be determined to be suitable for
   --  unchecked conversion.

   procedure Suitable_For_UC_Source
     (Typ         : Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  This procedure implements the notion of "suitable for unchecked
   --  conversion" of SPARK RM 13.9. It always uses the RM size.

   procedure Object_Suitable_For_UC_Source
     (Obj : Node_Id; Result : out Boolean; Explanation : out Unbounded_String);
   --  This procedure implements the notion of "suitable for unchecked
   --  conversion" of SPARK RM 13.9. It uses the size of Obj.

   procedure Suitable_For_UC_Target
     (Typ            : Type_Kind_Id;
      Size           : Uint;
      Size_Str       : String;
      For_UC         : Boolean;
      Result         : out Boolean;
      Explanation    : out Unbounded_String;
      Check_Validity : Boolean := True);
   --  This procedure implements the notion of "suitable as a target of an
   --  unchecked conversion" of SPARK RM 13.9. Possibility of invalid values is
   --  checked using the passed size.
   --  If For_UC is True, the explanation mentions UC, otherwise, it mentions
   --  aliased objects.
   --  If Check_Validity is False, do not check that Typ does not have invalid
   --  values.

   procedure Suitable_For_UC_Target_UC_Wrap
     (Typ            : Type_Kind_Id;
      Result         : out Boolean;
      Explanation    : out Unbounded_String;
      Check_Validity : Boolean := True);
   --  Wrapper of Suitable_For_UC_Target, to be used with unchecked conversion.
   --  The RM_Size is used to check for invalid values.

   procedure Suitable_For_UC_Target_Overlay_Wrap
     (Typ            : Type_Kind_Id;
      Obj            : Node_Id;
      Result         : out Boolean;
      Explanation    : out Unbounded_String;
      Check_Validity : Boolean := True);
   --  Wrapper of Suitable_For_UC_Target, to be used with overlays.

   function Suitable_For_Precise_UC
     (Arg_Typ : Type_Kind_Id) return True_Or_Explain;
   --  Check if Typ is only made of integers. When returning False,
   --  return also the Explanation.

   procedure Objects_Have_Same_Size
     (A, B        : Node_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  If objects A and B have the same size, then set Result to True;
   --  otherwise set Result to False and Explanation to a possible fix.

   procedure Have_Same_Known_RM_Size
     (A, B        : Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  Same as Have_Same_Known_Esize, but checks the RM_Size.

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
     (Arg           : W_Term_Id;
      Size          : Uint;
      Source_Type   : W_Type_Id;
      Target_Type   : W_Type_Id;
      Source_Status : Scalar_Status;
      Target_Status : Scalar_Status;
      Ada_Function  : Opt_E_Function_Id := Empty) return W_Term_Id;
   --  Return Arg of Source_Type converted to Target_Type, when both are of
   --  scalar types. Size is the shared size of both types, when arguments of
   --  the UC are integer types, which is used for conversion from an
   --  Unsigned type to a Signed one. Otherwise it is No_Uint.
   --  If Ada_Function is provided and its result is potentially invalid, wrap
   --  the result in a validity wrapper. The validity flag is set to True iff
   --  the return value is in the bounds of the return type of Ada_Function.

   function Precise_Composite_UC
     (Arg          : W_Term_Id;
      Source_Type  : Type_Kind_Id;
      Target_Type  : Type_Kind_Id;
      Ada_Function : E_Function_Id) return W_Term_Id;
   --  Return Arg of Source_Type converted to Target_Type, when at least one
   --  is a composite type made up of integers. Convert Arg to a large-enough
   --  modular type, and convert that value to Target. If all types involved
   --  are modular, then this benefits from bitvector support in provers.
   --  If the result of Ada_Function is potentially invalid, wrap it in a
   --  validity wrapper. The validity flag is set to True iff all scalar
   --  subcomponents of the return value are in the bounds of their subtype.

end Gnat2Why.Unchecked_Conversion;
