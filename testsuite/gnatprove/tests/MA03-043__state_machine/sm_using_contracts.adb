with SM_Operations; use SM_Operations;

package body SM_Using_Contracts is

   procedure Initialise is
   begin
      State := States_T'First;
   end;

   procedure Progress_SM(Trigger : in Triggers_T) is
   begin
      -- The implementation here could be any code because the
      -- proof tools will generate verification conditions that check
      -- that the implementation matches the contract cases defined above.

      -- Example implementation
      -- Implementation note, if I didn't know that the proof tools were
      -- going to check this implementation I'd be worried that I hadn't
      -- implemented it correctly.
      if Trigger = Btn_Pressed then
         if State = Start then
            State := Progress;
         elsif State = Progress or State = Finish then
            State := Finish;
         end if;
      end if;

      -- NB there is no else clause because in all cases no action is taken
      -- after the button has been released.
   end Progress_SM;

end SM_Using_Contracts;
