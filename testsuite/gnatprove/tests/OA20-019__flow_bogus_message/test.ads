with Dummy_Task;
pragma ELaborate_All (Dummy_Task);

package Test is

   package My_Task is new Dummy_Task (128_000);
   --  XXX triggers
   --
   --  dummy_task.ads:7:09: cannot write "The_Task" during elaboration
   --  of "Test" (SPARK RM 7.7.1(6)), in instantiation at test.ads:6

end Test;
