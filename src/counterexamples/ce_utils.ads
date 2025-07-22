------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - C E _ U T I L S                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2025, AdaCore                     --
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

with CE_Values;            use CE_Values;
with Checked_Types;        use Checked_Types;
with GNATCOLL.JSON;        use GNATCOLL.JSON;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Util.Types;     use SPARK_Util.Types;
with Types;                use Types;
with Uintp;                use Uintp;
with VC_Kinds;             use VC_Kinds;

package CE_Utils is

   function Compile_Time_Known_And_Constant (E : Entity_Id) return Boolean;
   --  This is used to know if something is compile time known and has
   --  the keyword constant on its definition. Internally, it calls
   --  Compile_Time_Known_Value_Or_Aggr.

   function Compute_Filename_Previous
     (Filename : String; Is_Previous : out Boolean; Ada_Node : in out Node_Id)
      return String;
   --  This computes the filename from the location given. The location can
   --  be of the form "'@Loop 4200@'filename.adb" in which case it should
   --  set Is_Previous to true and Ada_Node to the value corresponding to
   --  the integer in location. The function returns the filename itself.

   function Component_Is_Removed_In_Type
     (Ty : Entity_Id; Comp : Entity_Id; Vals : Entity_To_Value_Maps.Map)
      return Boolean;
   --  Return True if we can infer from the discriminant associations in Vals
   --  that the component Comp does not occur in the counterexample value.

   function Convert_Node (N : Integer) return Node_Id;
   --  Convert an integer to Node_Id. Return empty on exception.

   function Get_Id_From_Name
     (E : Callable_Kind_Id; Name : String) return Entity_Id;
   --  Return the entity id of the argument of E named Name.

   procedure Find_First_Static_Range
     (N : Node_Id; Fst : out Uint; Lst : out Uint);
   --  @param N any node which has a discrete range
   --  @param Fst low bound of N if it is compile time known, or of the first
   --    type in its etype chain which is compile time known.
   --  @param Lst high bound of N if it is compile time known, or of the first
   --    type in its etype chain which is compile time known.

   function Get_Entity_Id (Is_Record : Boolean; S : String) return Entity_Id;
   --  If Is_record then convert a string of the form ".4554" to the Entity_Id
   --  4554. Otherwise, convert a string of the form "4554".
   --  Return the empty entity if not of the given form.

   function Is_Visible_In_Type
     (Rec : Entity_Id; Comp : Entity_Id) return Boolean
   with
     Pre =>
       Retysp_Kind (Rec)
       in Incomplete_Or_Private_Kind | Record_Kind | Concurrent_Kind
       and Ekind (Comp)
           in E_Discriminant | E_Component | Type_Kind | E_Variable;
   --  True if Comp is a component of an ancestor of Rec which is visible in
   --  Rec.

   function Prefix_Elements
     (Elems : S_String_List.List; Pref : String) return S_String_List.List;
   --  Return a copy of Elems where every string has been prefixed with Pref.

   function To_Value_Access
     (Entity : Entity_Id; JSON_Data : GNATCOLL.JSON.JSON_Value)
      return CE_Values.Value_Access;
   --  Create a Value_Access to a new Value_Type of the type indicated by
   --  Entity and corresponding to the content of JSON_Data.

   function UI_From_String (Val : String) return Uint;
   --  Naive computation of a Uint form a string which is the representation of
   --  an integer in base 10.

   package Remove_Vars is
      --  This package contains the feature that removes duplicates of
      --  counterexample variables from before the current loop.

      procedure Remove_Extra_Vars (Cntexmp : in out Cntexample_File_Maps.Map);
      --  Remove the duplicates of Previous_Line in the normal counterexamples
      --  (those that are before the loop).

   end Remove_Vars;

   function Ultimate_Cursor_Type (Typ : Entity_Id) return Entity_Id;
   --  Type on which the iteration is done in Why.

end CE_Utils;
