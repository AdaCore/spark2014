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

package body Why.Atree.Sprint is

   -----------------------
   -- Identifier_Pre_Op --
   -----------------------

   procedure Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Identifier_Id)
   is
      pragma Unreferenced (State);
   begin
      Put (Get_Name_String (Get_Node (Node).Symbol));
   end Identifier_Pre_Op;

   ------------------
   -- Type_Post_Op --
   ------------------

   procedure Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Type_Id)
   is
      pragma Unreferenced (State);
   begin
      New_Line;
   end Type_Post_Op;

   -----------------
   -- Type_Pre_Op --
   -----------------

   procedure Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Id)
   is
      pragma Unreferenced (State);
   begin
      Put ("type ");
   end Type_Pre_Op;

   ---------------------
   -- Sprint_Why_Node --
   ---------------------

   procedure Sprint_Why_Node (Node : Why_Node_Id) is
      PS : Printer_State;
   begin
      Traverse (PS, Node);
   end Sprint_Why_Node;

end Why.Atree.Sprint;
