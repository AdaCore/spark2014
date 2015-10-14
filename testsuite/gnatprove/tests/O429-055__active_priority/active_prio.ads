package Active_Prio is

   task type Task_Type is
      pragma Priority(5);
   end Task_Type;

   protected type P_Type is
      pragma Priority(10);
      procedure Simple;
      procedure Jump;
   private
      A : Integer := 0;

   end;

   protected type Q_Type is
      pragma Priority(8);
      procedure Simple;
      procedure Not_Called;
      procedure Indirect;
   private
      A : Integer := 0;

   end;

   T : Task_Type;
   P : P_Type;
   Q : Q_Type;
end Active_Prio;
