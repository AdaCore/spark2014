with SM_Types; use SM_Types;

package SM_Using_Case_Stmt
  with SPARK_Mode
is

   -- Initialises the system state to "Start"
   procedure Initialise;

   -- Progresses the system state based on the trigger
   procedure Progress_SM(Trigger : in Triggers_T);

   -- Return's true if the state of the system is "Finish"
   function Is_Final_State return Boolean;

end SM_Using_Case_Stmt;
