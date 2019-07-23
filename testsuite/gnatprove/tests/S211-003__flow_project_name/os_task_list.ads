package os_task_list with
   Spark_Mode     => On,
   Abstract_State => Os_Task_State
 is

   function os_ghost_task_list_is_well_formed return Boolean with
      Global  => (Input => Os_Task_State),
      Depends => (os_ghost_task_list_is_well_formed'Result => Os_Task_State),
      Ghost   => True;

end os_task_list;
