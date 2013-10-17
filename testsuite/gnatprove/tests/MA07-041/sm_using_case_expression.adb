with SM_Operations; use SM_Operations;

package body SM_Using_Case_Expression
   with Refined_State => (Abs_State => State)
is


   State : States_T;

   function Get_State return States_T is (State)
     with Refined_Global => (input => State);

   procedure Set_State(New_State : in States_T)
     with Refined_Global => (output => State)
   is
   begin
      State := New_State;

   end Set_State;


   procedure Initialise
     with Refined_Global => (output => State)
   is
   begin
      Set_State(States_T'First);
   end;

   procedure Progress_SM(Trigger : in Triggers_T)
     with Refined_Global => (in_out => State)
   is
      -- This copy of state is required for the pragmas,
      -- in later releases this could be declared as a
      -- ghost function to ensure it isn't used by the code.
      Old_State : constant States_T := State;
   begin

      -- Check that all states are reachable
      -- NB This pragma can not be proven because of the nested
      -- existential quantifier but it can be executed successfully.
      pragma Assert
        (for all Final_State in States_T =>
           (for some Initial_State in States_T =>
                (for some Trigger2 in Triggers_T =>
                     (Final_State = My_SM(Initial_State, Trigger2)))));


      -- Check that all valid trigger conditions are defined
      -- NB This pragma can not be proven because of the nested
      -- existential quantifier but it can be executed successfully.
      pragma Assert
       (for all State2 in States_T =>
         (for all Trigger in Triggers_T =>
                 (My_SM(State2, Trigger) /= Invalid_State or
                 (for some Idx in Invalid_Transition_Array_T'Range =>
                     Invalid_Transition_Array(Idx).Initial_State = State2 and
                      Invalid_Transition_Array(Idx).Trigger = Trigger))));


      -- The implementation here could be any code because the
      -- proof tools will generate verification conditions that check
      -- that the implementation matches the contract cases defined above.

      -- Example implementation
      -- Implementation note, if I didn't know that the proof tools were
      -- going to check this implementation I'd be worried that I hadn't
      -- implemented it correctly.
      if Trigger = Btn_Pressed then
         if State = Start then
            Set_State(Progress);
         elsif State = Progress or State = Finish then
            Set_State(Finish);
         else
            Set_State(Invalid_State);
         end if;

         -- This pragmas can be commented out or deleted it is
         -- left in as example of a method of identifying errors
         -- in the code or specification.
         -- pragma Assert (if Trigger = Btn_Pressed then Get_State = My_SM(Old_State, Trigger));

      elsif Trigger = Btn_Start then
         Set_State(Start);

      elsif Trigger = Btn_Finish then
         -- Error Seed #1 - uncomment setting state to "Start" and comment out
         -- setting the state to "Finish"
         -- This demonstrates what happens when the implementation does not
         -- match the specification. The post condition on the body of
         -- Progress_SM is no longer provable. Selecting the post condition
         -- and selecting "Prove Line" brings up the option to "Show Paths".
         -- This then highlights this path as being unprovable.
         Set_State(Finish);
         -- Set_State(Start);

      elsif Trigger = Invalid_Trigger then
         Set_State(Invalid_State);

      end if;

   end Progress_SM;

end SM_Using_Case_Expression;
