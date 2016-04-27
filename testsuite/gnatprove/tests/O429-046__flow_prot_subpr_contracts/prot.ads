package Prot
  with Elaborate_Body, Abstract_State => State
is
   Visible : Integer := 0;

   protected type P_Int (D : Integer) is
      function Get return Integer
        with Global => Visible;

      entry Set (X : Integer)
        with Global => Visible;
   private
      The_Protected_Int : Integer := D;
      Condition         : Boolean := True;
   end P_Int;

   task Singleton_Task
     with Global => (Input  => State,
                     In_Out => Visible);

   task type Task_Type
     with Global => (In_Out => State);

   PO : P_Int (5);
end Prot;
