with Ada.Numerics.Discrete_Random;

package Support is
   subtype RandomRange is Positive range 1 .. 3;

   package Random_3 is new Ada.Numerics.Discrete_Random
     (Result_Subtype => RandomRange);

   G: Random_3.Generator;

   --  This protected object holds the summary
   protected Prot is
      procedure Add (X : Natural);

      function Get return Natural;
   private
      Summary : Natural := 0;
   end Prot;

   task type Rand_Task;

   Number_Of_Tasks : constant Natural := 10;
   Task_Array      : array (1 .. Number_Of_Tasks) of Rand_Task;
end Support;
