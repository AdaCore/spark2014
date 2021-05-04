------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
-- F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 1 . W R I T E  --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                Copyright (C) 2018-2021, Altran UK Limited                --
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
------------------------------------------------------------------------------

with Flow_Generated_Globals.ALI_Serialization;
use Flow_Generated_Globals.ALI_Serialization;

private package Flow_Generated_Globals.Phase_1.Write is

   procedure New_GG_Line (K : ALI_Entry_Kind);
   --  Starts a new ALI line with a GG info

   procedure Terminate_GG_Line;
   --  Terminates a line with a GG info

   --  Serialization for individual data types; these calls should be preceded
   --  with New_GG_Line and finally followed by Terminate_GG_Line.
   --  ??? enforce this with a Pre/Post contracts and a ghost variable

   procedure Serialize (E : Entity_Id);

   procedure Serialize (Nodes : Node_Lists.List; Label : String := "");

   procedure Serialize (Nodes : Node_Sets.Set; Label : String := "");

   procedure Serialize (L : Elist_Id);

   procedure Serialize (N : Int);

   procedure Serialize (S : String);

   generic
      type T is (<>);
   procedure Serialize_Discrete (A : T; Label : String := "");

end Flow_Generated_Globals.Phase_1.Write;
