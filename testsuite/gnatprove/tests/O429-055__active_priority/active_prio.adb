package body Active_Prio is

   task body Task_Type is
   begin
      --  these two calls should succeed
      P.Simple;
      Q.Simple;
      --  jump goes through a PO with higher priority, so violating the check
      P.Jump;
   end Task_Type;

   protected body P_Type is
      procedure Simple is
      begin
         A := A + 1;
      end Simple;

      procedure Jump is
      begin
         Q.Indirect; -- this call is from a high priority to a lower one, so a problem
      end Jump;
   end;

   protected body Q_Type is
      procedure Simple is
      begin
         A := A + 1;
      end Simple;

      procedure Indirect is
      begin
         A := A + 1;
      end Indirect;

      procedure Not_Called is
      begin
         A := A - 1;
      end Not_Called;
   end;

end Active_Prio;
