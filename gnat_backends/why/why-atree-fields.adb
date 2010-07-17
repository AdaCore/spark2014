------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - F I E L D S                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package body Why.Atree.Fields is
   
   ------------------
   -- Get_External --
   ------------------
   
   function Get_External (Node : Why_Node_Id) return Why_Node_Id is
   begin
      case Get_Kind (Node) is
	 when W_Type =>
	    return Get_Node (Node).T_External;
	 
	 when W_Logic =>
	    return Get_Node (Node).L_External;
	 
	 when W_Parameter_Declaration =>
	    return Get_Node (Node).PD_External;
	 
	 when others =>
	    pragma Assert (False);
	    return Why_Empty;
      end case;
   end Get_External;
   
   --------------
   -- Get_Name --
   --------------
   
   function Get_Name (Node : Why_Node_Id) return Why_Node_Id is
   begin
      return Get_Node (Node).T_Name;
   end Get_Name;

end Why.Atree.Fields;
