------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - T A B L E S                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

   ------------
   -- Append --
   ------------

   procedure Append (List_Id : Why_Node_List; New_Item : Why_Node_Id) is
      LI : List_Info renames List_Table (List_Id);
   begin
      LI.Content.Append (New_Item);
      Set_Link (New_Item, Why_Node_Set (List_Id));

      --  Assuming that the list is kind-valid (which should have been checked
      --  at this point), it is now valid, as it contains at least one element.
      LI.Checked := True;
   end Append;

   -------------
   -- Prepend --
   -------------

   procedure Prepend (List_Id : Why_Node_List; New_Item : Why_Node_Id) is
      LI : List_Info renames List_Table (List_Id);
   begin
      LI.Content.Prepend (New_Item);
      Set_Link (New_Item, Why_Node_Set (List_Id));

      --  Assuming that the list is kind-valid (which should have been checked
      --  at this point), it is now valid, as it contains at least one element.
      LI.Checked := True;
   end Prepend;

   ----------
   -- Free --
   ----------

   procedure Free is
   begin
      --  Remove the (controlled) objects of the Why3 nodes with Clear and
      --  free the memory used by the vector itself with Reserve_Capacity.
      --
      --  Note: while Ada RM says "If the capacity of Container is already
      --  greater than or equal to [Reserve_Capacity parameter], then
      --  Reserve_Capacity has no effect" the GNAT's implementation of
      --  Reserve_Capcity frees the underlying memory, so let's do that.

      Node_Table.Clear;
      Node_Table.Reserve_Capacity (0);

      List_Table.Clear;
      List_Table.Reserve_Capacity (0);
   end Free;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
      Empty_Node : constant Why_Node (W_Unused_At_Start) :=
                     (Kind     => W_Unused_At_Start,
                      Ada_Node => Empty,
                      Domain   => EW_Prog,
                      Link     => Why_Empty,
                      Checked  => True);
   begin
      Node_Table.Append (Empty_Node);
      pragma Assert (Node_Table.Last_Index = Why_Empty);
   end Initialize;

   --------------
   -- New_List --
   --------------

   function New_List return Why_Node_List is
      New_Item : constant List_Info :=
        (Checked => False,
         Link    => Why_Empty,
         Content => Why_Node_Lists.Empty_List);
   begin
      List_Table.Append (New_Item);
      return List_Table.Last_Index;
   end New_List;

   ---------------------
   -- New_Why_Node_Id --
   ---------------------

   function New_Why_Node_Id (Node : Why_Node) return Why_Node_Id is
   begin
      Node_Table.Append (Node);
      return Node_Table.Last_Index;
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
         null;
      else
         Node_Table (Node_Id).Link := Link;
      end if;
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
   begin
      List_Table (List_Id).Link := Link;
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
   begin
      Node_Table (Node_Id) := Node;
   end Set_Node;

   ----------------------------
   -- Update_Validity_Status --
   ----------------------------

   procedure Update_Validity_Status
     (Node_Id : Why_Node_Id;
      Checked : Boolean)
   is
   begin
      Node_Table (Node_Id).Checked := Checked;
   end Update_Validity_Status;

   procedure Update_Validity_Status
     (List_Id : Why_Node_List;
      Checked : Boolean)
   is
   begin
      List_Table (List_Id).Checked := Checked;
   end Update_Validity_Status;

begin
   Initialize;
end Why.Atree.Tables;
