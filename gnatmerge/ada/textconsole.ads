------------------------------------------------------------------------------
--                                                                          --
--                            G N A T M E R G E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
--                                                                          --
-- gnatmerge is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatmerge is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with GNATCOLL.Scripts;

package TextConsole is

   type Text_Console is new GNATCOLL.Scripts.Virtual_Console_Record
     with private;
   overriding procedure Insert_Text
     (Console : access Text_Console; Txt : String);
   overriding procedure Insert_Prompt
     (Console : access Text_Console; Txt : String);
   overriding procedure Insert_Error
     (Console : access Text_Console; Txt : String);
   overriding procedure Insert_Log
     (Console : access Text_Console; Txt : String);
   overriding procedure Set_Data_Primitive
     (Instance : GNATCOLL.Scripts.Class_Instance;
      Console : access Text_Console);
   overriding function Get_Instance
     (Script  : access GNATCOLL.Scripts.Scripting_Language_Record'Class;
      Console : access Text_Console) return GNATCOLL.Scripts.Class_Instance;

private
   type Text_Console is new GNATCOLL.Scripts.Virtual_Console_Record
     with record
        Instances : GNATCOLL.Scripts.Instance_List;
     end record;

end TextConsole;
