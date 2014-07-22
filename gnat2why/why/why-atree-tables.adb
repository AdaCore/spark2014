------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - T A B L E S                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package body Why.Atree.Tables is

   procedure Initialize;
   --  Initialize this package

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Why_Node_Lists.List) return Boolean is
      use Why_Node_Lists;

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

   ------------
   -- Append --
   ------------

   procedure Append (List_Id : Why_Node_List; New_Item : Why_Node_Id) is
      use Node_List_Tables;
      use Why_Node_Lists;

      LI : List_Info := List_Table.Element (List_Id);
   begin
      Append (LI.Content, New_Item);
      Set_Link (New_Item, Why_Node_Set (List_Id));

      --  Assuming that the list is kind-valid (which should have been
      --  checked at this point), it is now valid, as it contains at
      --  least one element.
      LI.Checked := True;

      Replace_Element (List_Table, List_Id, LI);
   end Append;

   -------------
   -- Prepend --
   -------------

   procedure Prepend (List_Id : Why_Node_List; New_Item : Why_Node_Id) is
      use Node_List_Tables;
      use Why_Node_Lists;

      LI : List_Info := List_Table.Element (List_Id);
   begin
      Prepend (LI.Content, New_Item);
      Set_Link (New_Item, Why_Node_Set (List_Id));

      --  Assuming that the list is kind-valid (which should have been
      --  checked at this point), it is now valid, as it contains at
      --  least one element.
      LI.Checked := True;

      Replace_Element (List_Table, List_Id, LI);
   end Prepend;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
      use Node_Tables;

      Empty_Node : constant Why_Node (W_Unused_At_Start) :=
                     (Kind     => W_Unused_At_Start,
                      Ada_Node => Empty,
                      Domain   => EW_Prog,
                      Link     => Why_Empty,
                      Checked  => True);
   begin
      Append (Node_Table, Empty_Node);
      pragma Assert (To_Index (Last (Node_Table)) = Why_Empty);
   end Initialize;

   --------------
   -- New_List --
   --------------

   function New_List return Why_Node_List is
      use Node_List_Tables;
      use Why_Node_Lists;

      New_List : List;
      New_Item : constant List_Info := (False, Why_Empty, New_List);
   begin
      Append (List_Table, New_Item);
      return To_Index (Last (List_Table));
   end New_List;

   ------------------
   -- New_Why_Node --
   ------------------

   function New_Why_Node_Id (Node : Why_Node) return Why_Node_Id is
      use Node_Tables;
      Result : Why_Node_Id;
   begin
      Append (Node_Table, Node);
      Result := To_Index (Last (Node_Table));
      return Result;
   end New_Why_Node_Id;

   function New_Why_Node_Id
     (Kind : W_Any_Node)
     return Why_Node_Id
   is
      New_Node : Why_Node (Kind);
   begin
      New_Node.Ada_Node := Empty;
      New_Node.Link := Why_Empty;
      New_Node.Checked := False;
      return New_Why_Node_Id (New_Node);
   end New_Why_Node_Id;

   --------------
   -- Set_Link --
   --------------

   procedure Set_Link
     (Node_Id : Why_Node_Id;
      Link    : Why_Node_Set) is
   begin
      if Node_Id = Why_Empty then
         return;
      end if;

      declare
         Node : Why_Node := Get_Node (Node_Id);
      begin
         Node.Link := Link;
         Set_Node (Node_Id, Node);
      end;
   end Set_Link;

   procedure Set_Link
     (Node_Id : Why_Node_Id;
      Link    : Why_Node_Id) is
   begin
      Set_Link (Node_Id, Why_Node_Set (Link));
   end Set_Link;

   procedure Set_Link
     (Node_Id : Why_Node_Id;
      Link    : Why_Node_List) is
   begin
      Set_Link (Node_Id, Why_Node_Set (Link));
   end Set_Link;

   procedure Set_Link
     (List_Id : Why_Node_List;
      Link    : Why_Node_Set)
   is
      use Node_List_Tables;
      use Why_Node_Lists;

      LI : List_Info := List_Table.Element (List_Id);
   begin
      LI.Link := Link;
      Replace_Element (List_Table, List_Id, LI);
   end Set_Link;

   procedure Set_Link
     (List_Id : Why_Node_List;
      Link    : Why_Node_Id) is
   begin
      Set_Link (List_Id, Why_Node_Set (Link));
   end Set_Link;

   procedure Set_Link
     (List_Id : Why_Node_List;
      Link    : Why_Node_List) is
   begin
      Set_Link (List_Id, Why_Node_Set (Link));
   end Set_Link;

   --------------
   -- Set_Node --
   --------------

   procedure Set_Node (Node_Id : Why_Node_Id; Node : Why_Node) is
      use Node_Tables;
   begin
      Replace_Element (Node_Table, Node_Id, Node);
   end Set_Node;

   ----------------------------
   -- Update_Validity_Status --
   ----------------------------

   procedure Update_Validity_Status
     (Node_Id : Why_Node_Id;
      Checked : Boolean)
   is
      use Node_Tables;

      Node : Why_Node := Get_Node (Node_Id);
   begin
      Node.Checked := Checked;
      Set_Node (Node_Id, Node);
   end Update_Validity_Status;

   procedure Update_Validity_Status
     (List_Id : Why_Node_List;
      Checked : Boolean)
   is
      use Node_List_Tables;
      use Why_Node_Lists;

      LI : List_Info := List_Table.Element (List_Id);
   begin
      LI.Checked := Checked;
      Replace_Element (List_Table, List_Id, LI);
   end Update_Validity_Status;

begin
   Initialize;
end Why.Atree.Tables;
