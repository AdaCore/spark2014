generic
   Task_Stack_Size : in Natural;
   --  Task stack size

package Dummy_Task is

   task The_Task is
      pragma Storage_Size (Task_Stack_Size);
   end The_Task;

end Dummy_Task;
