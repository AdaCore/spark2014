------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--            G N A T 2 W H Y - U N C H E C K E D _ C O N V E R S I O N     --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2025-2026, AdaCore                     --
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
with SPARK_Atree;           use SPARK_Atree;
with SPARK_Atree.Entities;  use SPARK_Atree.Entities;
with Types;                 use Types;
with Why.Ids;               use Why.Ids;
with Uintp;                 use Uintp;

package Gnat2Why.Unchecked_Conversion is

   function Is_UC_With_Precise_Definition
     (Source_Type, Target_Type : Type_Kind_Id; Potentially_Invalid : Boolean)
      return True_Or_Explain;
   --  Return whether an unchecked conversion from Source_Type to Target_Type
   --  is an UC for which we can give a precise definition.

   function Is_Overlay_Handled_As_UC
     (Obj : Object_Kind_Id) return True_Or_Explain;
   --  Return whether an overlay object is translated using an unchecked
   --  conversion module.

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

   procedure Have_Same_Known_RM_Size
     (A, B        : Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  Same as Have_Same_Known_Esize, but checks the RM_Size.

   procedure Create_Module_For_UC_If_Needed
     (Source_Type, Target_Type : Type_Kind_Id; Potentially_Invalid : Boolean);
   --  Generate a module for unchecked conversion from Source_Type to
   --  Target_Type if there isn't one already. If Potentially_Invalid is True,
   --  the target is potentially invalid.

   procedure Types_Compatible_Alignment
     (Src_Ty      : Type_Kind_Id;
      Tar_Ty      : Type_Kind_Id;
      Valid       : out Boolean;
      Explanation : out Unbounded_String);
   --  Check that Src_Ty and Tar_Ty have compatible alignment

   function Get_UC_Function
     (Source_Type, Target_Type : Type_Kind_Id; Potentially_Invalid : Boolean)
      return W_Identifier_Id;
   --  Return the function that should be used to convert from Source_Type to
   --  Target_Type.

end Gnat2Why.Unchecked_Conversion;
