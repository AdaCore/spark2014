package PO_T8 is
   --  TU: 11. At most one task (including the environment task) shall ever
   --  call (directly or via intermediate calls) the protected entry (if any)
   --  of a given protected object. [Roughly speaking, each protected object
   --  which has an entry can be statically identified with its "suspender
   --  task" and no other task shall call the entry of that protected
   --  object. This rule is enforced via (potentially conservative) flow
   --  analysis, as opposed to by introducing verification conditions.  This
   --  rule discharges the verification condition associated with Ravenscar's
   --  "Max_Entry_Queue_Length => 1" restriction.]
   --  For purposes of this rule,
   --  Ada.Synchronous_Task_Control.Suspension_Object is assumed to be a
   --  protected type having an entry and the procedure Suspend_Until_True is
   --  assumed to contain a call to the entry of its parameter. [This rule
   --  discharges the verification condition associated with the Ada rule that
   --  two tasks cannot simultaneously suspend on one suspension object (see
   --  Ada RM D.10(10)).]

   protected P_Int is
      function Get return Integer;

      procedure Allow_Increase;

      entry Increase;
   private
      Condition : Boolean := True;
      The_Protected_Int : Integer := 0;
   end P_Int;

   task T;
end PO_T8;
