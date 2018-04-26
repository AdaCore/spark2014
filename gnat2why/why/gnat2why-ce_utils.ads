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

with Atree;             use Atree;
with Einfo;             use Einfo;
with SPARK_Util.Types;  use SPARK_Util.Types;
with Gnat2Why.Util;     use Gnat2Why.Util;
with Types;             use Types;

package Gnat2Why.CE_Utils is

   function Count_Why_Visible_Regular_Fields (E : Entity_Id) return Natural
     with Pre => Is_Record_Type_In_Why (E);
   --  Same as Count_Why_Regular_Fields but only counts fields that are
   --  visible according to Component_Is_Visible_In_Type.

   function Is_Visible_In_Type (Rec  : Entity_Id;
                                Comp : Entity_Id)
                                return Boolean
   with
     Pre => Retysp_Kind (Rec) in Private_Kind | Record_Kind | Concurrent_Kind
     and Ekind (Comp) in
       E_Discriminant | E_Component | Type_Kind | E_Variable;
   --  True if Comp is a component of an ancestor of Rec which is visible in
   --  Rec.

end Gnat2Why.CE_Utils;
