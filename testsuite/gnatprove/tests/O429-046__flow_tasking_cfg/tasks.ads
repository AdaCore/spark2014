package Tasks
  with Abstract_State => State,
       Initializes    => (Visible, State)
is
   Visible : Integer := 0;

   task Singleton_Task;

   task type Task_Type;

   task type Task_Type2;
end Tasks;
