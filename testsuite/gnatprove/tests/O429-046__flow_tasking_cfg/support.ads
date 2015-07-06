package Support is
   --  This protected object holds the summary
   protected Prot is
      procedure Add (X : Natural);

      function Get return Natural;
   private
      Summary : Natural := 0;
   end Prot;

   task type Rand_Task;

   Number_Of_Tasks : constant Natural := 1000;
   Task_Array      : array (1 .. Number_Of_Tasks) of Rand_Task;
end Support;
