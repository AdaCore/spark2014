------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - S P R I N T                      --
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

with Ada.Text_IO; use Ada.Text_IO;

with Namet; use Namet;

with Why.Atree.Fields; use Why.Atree.Fields;

package body Why.Atree.Sprint is
   
   -----------------
   -- Sprint_Node --
   -----------------

   procedure Sprint_Why_Node (Node : Why_Node_Id) is
   begin
      case Get_Kind (Node) is
	 when W_Identifier =>
	    Put (Get_Name_String (Get_Node (Node).Name));
	    
	 when W_Type =>
	    if Get_External (Node) /= Why_Empty then 
	       Put ("external ");
	    end if;
	    
	    Put ("type ");
	    Sprint_Why_Node (Get_Name (Node));
	 
	 when others =>
	    raise Not_Implemented;
      end case;
   end Sprint_Why_Node;

end Why.Atree.Sprint;
