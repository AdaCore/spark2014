------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--  F L O W . G E N E R A T E D _ G L O B A L S . S E R I A L I Z A T I O N --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--                Copyright (C) 2016-2021, Altran UK Limited                --
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

package Flow_Generated_Globals.ALI_Serialization is

   type ALI_Entry_Kind is (EK_End_Marker,
                           EK_State_Map,
                           EK_Remote_States,
                           EK_Predef_Init_Entities,
                           EK_Ghost_Entities,
                           EK_Constants,
                           EK_CAE_Entities,
                           EK_Volatiles,
                           EK_Globals,
                           EK_Constant_Calls,
                           EK_Protected_Instance,
                           EK_Task_Instance,
                           EK_Max_Queue_Length,
                           EK_Direct_Calls,
                           EK_Part_Of,
                           EK_Flow_Scope);
   --  Kinds of the information stored between gnat2why phases, where the info
   --  is written (phase 1) and read (phase 2). Almost no other types are
   --  shared between writing (which takes Entity_Ids) and reading (which gives
   --  Entity_Names).

end Flow_Generated_Globals.ALI_Serialization;
