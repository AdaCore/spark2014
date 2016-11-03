------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--  F L O W . G E N E R A T E D _ G L O B A L S . S E R I A L I Z A T I O N --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--                  Copyright (C) 2016, Altran UK Limited                   --
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

--  This package implements serialization, i.e. writing and reading, of global
--  contracts from an abstract "archive".

with Serialisation; use Serialisation;

package Flow_Generated_Globals.ALI_Serialization is

   type ALI_Entry_Kind is (EK_Error,
                           EK_End_Marker,
                           EK_State_Map,
                           EK_Remote_States,
                           EK_Volatiles,
                           EK_Globals,
                           EK_Protected_Instance,
                           EK_Task_Instance,
                           EK_Tasking_Info,
                           EK_Nonblocking,
                           EK_Nonreturning,
                           EK_Terminating,
                           EK_Direct_Calls);

   type Name_Tasking_Info is array (Tasking_Info_Kind) of Name_Sets.Set;
   --  Similar to Tasking_Info_Bag, but with sets of object names

   type ALI_Entry (Kind : ALI_Entry_Kind := EK_Error) is record
      case Kind is
         when EK_Error | EK_End_Marker =>
            null;
         when EK_State_Map =>
            The_State                    : Entity_Name;
            The_Constituents             : Name_Lists.List;
         when EK_Remote_States =>
            The_Remote_States            : Name_Sets.Set;
         when EK_Volatiles =>
            The_Async_Readers            : Name_Sets.Set;
            The_Async_Writers            : Name_Sets.Set;
            The_Effective_Reads          : Name_Sets.Set;
            The_Effective_Writes         : Name_Sets.Set;
         when EK_Globals =>
            The_Global_Info              : Global_Phase_1_Info;
         when EK_Protected_Instance =>
            The_Variable                 : Entity_Name;
            The_Priority                 : Priority_Value;
         when EK_Task_Instance =>
            The_Type                     : Entity_Name;
            The_Object                   : Task_Object;
         when EK_Tasking_Info =>
            The_Entity                   : Entity_Name;
            The_Tasking_Info             : Name_Tasking_Info;
         when EK_Nonblocking =>
            The_Nonblocking_Subprograms  : Name_Lists.List;
         when EK_Nonreturning =>
            The_Nonreturning_Subprograms : Name_Lists.List;
         when EK_Terminating =>
            The_Terminating_Subprograms  : Name_Lists.List;
         when EK_Direct_Calls =>
            The_Caller                   : Entity_Name;
            The_Callees                  : Name_Lists.List;
      end case;
   end record;
   --  IMPORTANT: If you change this, then also update the serialisation
   --  procedure, and Null_ALI_Entry to initialize any scalars.

   procedure Serialize (A : in out Archive; V : in out ALI_Entry);
   --  Serialization procedure for a single ALI entry

end Flow_Generated_Globals.ALI_Serialization;
