with SM_Types; use SM_Types;

package SM_Using_Contracts
  with SPARK_Mode
is

   State : States_T;

   -- Initialises the system state to "Start"
   procedure Initialise
     with Post => (State = States_T'First);

   -- Progresses the system state based on the trigger
   procedure Progress_SM(Trigger : in Triggers_T)
     with Contract_Cases => (
            State = Start and Trigger = Btn_pressed => State = Progress,
            State = Start and Trigger = Btn_Released => State = Start,
            State = Progress and Trigger = Btn_pressed => State = Finish,
            State = Progress and Trigger = Btn_Released => State = Progress,
            State = Finish and Trigger = Btn_Pressed => State = Finish,
            State = Finish and Trigger = Btn_Released => State = Finish,
            others => False);

   -- Return's true if the state of the system is "Finish"
   function Is_Final_State return Boolean is (State = States_T'Last);

end SM_Using_Contracts;
