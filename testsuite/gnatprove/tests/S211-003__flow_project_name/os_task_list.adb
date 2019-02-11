package body os_task_list with
   Spark_Mode    => On,
   Refined_State => (Os_Task_State => os_task_list_rw)
 is

   os_task_list_rw : Boolean := True;

   ---------------------------------------
   -- os_ghost_task_list_is_well_formed --
   ---------------------------------------

   function os_ghost_task_list_is_well_formed return Boolean is
     (os_task_list_rw);

end os_task_list;
