pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Concurrent is

   task type Some_Task is
   end Some_Task;
   
   task type Some_Other_Task is
   end Some_Other_Task;
   pragma Annotate (GNATprove, Skip_Proof, Some_Task);
   pragma Annotate (GNATprove, Skip_Proof, Some_Other_Task);
     
   protected type Some_Protected_Object is
      entry Fake_Entry;
      pragma Annotate (GNATprove, Skip_Proof, Fake_Entry);
   end Some_Protected_Object;
   protected type Some_Other_Protected_Object is
      entry Other_Fake_Entry;
      procedure Fake_Init;
      pragma Annotate (GNATprove, Skip_Proof, Other_Fake_Entry);
   end Some_Other_Protected_Object;

end Concurrent;
