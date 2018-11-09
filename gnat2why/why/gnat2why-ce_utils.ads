------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - C E _ U T I L S                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                        Copyright (C) 2018, AdaCore                       --
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

with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Util.Types;     use SPARK_Util.Types;
with Types;                use Types;
with Uintp;                use Uintp;

package Gnat2Why.CE_Utils is

   function Is_Visible_In_Type (Rec  : Entity_Id;
                                Comp : Entity_Id)
                                return Boolean
   with
     Pre => Retysp_Kind (Rec) in Private_Kind | Record_Kind | Concurrent_Kind
     and Ekind (Comp) in
       E_Discriminant | E_Component | Type_Kind | E_Variable;
   --  True if Comp is a component of an ancestor of Rec which is visible in
   --  Rec.

   function Get_Entity_Id (Is_Record : Boolean; S : String) return Entity_Id;
   --  If Is_record then convert a string of the form ".4554" to the Entity_Id
   --  4554. Otherwise, convert a string of the form "4554".
   --  Return the empty entity if not of the given form.

   procedure Find_First_Static_Range
     (N   : Node_Id;
      Fst : out Uint;
      Lst : out Uint);
   --  @param N any node which has a discrete range
   --  @param Fst low bound of N if it is compile time known, or of the first
   --    type in its etype chain which is compile time known.
   --  @param Lst high bound of N if it is compile time known, or of the first
   --    type in its etype chain which is compile time known.

   function UI_From_String (Val : String) return Uint;
   --  Naive computation of a Uint form a string which is the representation of
   --  an integer in base 10.

   function Has_Prefix (S : String; Prefix : String) return Boolean;
   --  Return True if Prefix is a prefix of S

end Gnat2Why.CE_Utils;
