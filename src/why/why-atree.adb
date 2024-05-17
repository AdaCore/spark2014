package body Why.Atree is

   procedure Initialize;
   --  Initialize this package

   ------------
   -- Append --
   ------------

   procedure Append (List_Id : Why_Node_List; New_Item : Why_Node_Id) is
      LI : List_Info renames List_Table (List_Id);
   begin
      LI.Content.Append (New_Item);

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
      New_Node.Checked := False;
      return New_Why_Node_Id (New_Node);
   end New_Why_Node_Id;

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

end Why.Atree;
