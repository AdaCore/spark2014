package body P is

   S : Suspension_Object;

   procedure Safe (S1, S2 : in out Suspension_Object) is
      pragma Unreferenced (S1, S2);
      --  ??? As a limitation in flow analysis we can only suspend on
      --  library-level suspension objects, so can't really do anything with S1
      --  and S2, but still a call this procedure should be accepted (e.g. its
      --  body could be hidden with SPARK_Mode => Off).
   begin
      null;
   end;

   procedure Also_Safe (S1 : in out Suspension_Object) is
      pragma Unreferenced (S1);
   begin
     Ada.Synchronous_Task_Control.Suspend_Until_True (S);
   end;

begin
   Safe (SO, SO);
   Also_Safe (S);
end P;
