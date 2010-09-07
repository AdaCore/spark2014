------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - T A B L E S                      --
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

package body Why.Atree.Tables is

   procedure Initialize;
   --  Initialize this package

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Node_Lists.List) return Boolean is
      use Node_Lists;

      In_Left  : Cursor  := First (Left);
      In_Right : Cursor  := First (Right);
      Result   : Boolean := True;
   begin
      loop
         if In_Left = No_Element or In_Right = No_Element then
            Result := In_Left = No_Element and In_Right = No_Element;
            exit;
         end if;

         declare
            Left_Element  : constant Why_Node_Id := Element (In_Left);
            Right_Element : constant Why_Node_Id := Element (In_Right);
         begin
            if Left_Element /= Right_Element then
               Result := False;
               exit;
            end if;
         end;

         Next (In_Left);
         Next (In_Right);
      end loop;

      return Result;
   end "=";

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
      use Node_Tables;

      Empty_Node : constant Why_Node (W_Unused_At_Start)
                     := (Kind => W_Unused_At_Start,
                         Ada_Node => Empty,
                         Link => Why_Empty,
                         Checked => True);
   begin
      Append (Node_Table, Empty_Node);
      pragma Assert (To_Index (Last (Node_Table)) = Why_Empty);
   end Initialize;

   --------------
   -- New_List --
   --------------

   function New_List return Why_Node_List is
      use Node_List_Tables;
      use Node_Lists;

      New_List : List;
      New_Item : constant List_Info := (False, New_List);
   begin
      Append (List_Table, New_Item);
      return To_Index (Last (List_Table));
   end New_List;

   ------------------
   -- New_Why_Node --
   ------------------

   function New_Why_Node_Id (Node : Why_Node) return Why_Node_Id is
      use Node_Tables;
   begin
      Append (Node_Table, Node);
      return To_Index (Last (Node_Table));
   end New_Why_Node_Id;

   --------------
   -- Set_Node --
   --------------

   procedure Set_Node (Node_Id : Why_Node_Id; Node : Why_Node) is
      use Node_Tables;
   begin
      Replace_Element (Node_Table, Node_Id, Node);
   end Set_Node;

begin
   Initialize;
end Why.Atree.Tables;
