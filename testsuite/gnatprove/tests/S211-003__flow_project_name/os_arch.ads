with os_task_list;

package os_arch with
   SPARK_Mode => On
 is

   procedure os_arch_idle with
      Global        => null,
      Post          => os_task_list.os_ghost_task_list_is_well_formed,
      Import        => True,
      External_Name => "os_arch_idle",
      Convention    => C;

end os_arch;
