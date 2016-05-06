------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 1        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2014-2016, Altran UK Limited                 --
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

with Flow_Dependency_Maps;               use Flow_Dependency_Maps;

package Flow_Generated_Globals.Phase_1 is

   -------------
   -- Writing --
   -------------

   procedure GG_Write_Initialize (GNAT_Root : Node_Id)
   with Pre  => GG_Mode = GG_No_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Must be called before the first call to
   --  GG_Write_Global_Info and GG_Write_Package_Info.

   procedure GG_Register_State_Info (DM : Dependency_Maps.Map)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register information related to state abstractions and the refinements
   --  thereof. This will later be used to return the appropriate view
   --  depending on the caller (as opposed to always returning the most refined
   --  view). It also stores information related to external states.

   procedure GG_Register_Global_Info (GI : Global_Phase_1_Info)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register the information we need to later compute globals.
   --  Compute_Globals in Flow.Slice is used to produce the inputs.
   --  It also stores information related to volatiles and possibly blocking
   --  property.

   procedure GG_Register_Nonblocking (EN : Entity_Name)
   with Pre  => EN /= Null_Entity_Name and then
                GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register entity with no potentially blocking statements

   procedure GG_Register_Task_Object (Type_Name : Entity_Name;
                                      Object    : Task_Object)
   with Pre  => Type_Name /= Null_Entity_Name and then
                GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register an instance of a task object

   procedure GG_Register_Tasking_Info (EN : Entity_Name;
                                       TI : Tasking_Info)
   with Pre  => EN /= Null_Entity_Name and then
                GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register tasking-related information for entity

   procedure GG_Register_Protected_Object (PO   : Entity_Name;
                                           Prio : Priority_Value)
   with Pre  => PO /= Null_Entity_Name and then
                GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register protected object and its priority

   procedure GG_Write_Finalize
   with Pre => GG_Mode = GG_Write_Mode;
   --  Appends all collected information to the ALI file.

end Flow_Generated_Globals.Phase_1;
