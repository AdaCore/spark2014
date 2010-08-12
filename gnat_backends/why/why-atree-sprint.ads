------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - S P R I N T                      --
--                                                                          --
--                                 S p e c                                  --
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

with Why.Atree.Traversal; use Why.Atree.Traversal;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Ids;             use Why.Ids;

package Why.Atree.Sprint is

   --  This package provides ways to print source code from the abstract
   --  syntax tree.

   procedure Sprint_Why_Node (Node : Why_Node_Id);
   pragma Precondition (Get_Kind (Node) /= W_Unused_At_Start);

private
   type Printer_State is new Traversal_State with null record;

   procedure Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Identifier_Id);

   procedure Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Id);

   procedure Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Type_Id);

end Why.Atree.Sprint;
