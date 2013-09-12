package body Vehicle is

   procedure Halt
      with Pre  => Speed_Is_Valid,
           Post => State = Still and Speed_Is_Valid;

   ------------------
   -- State_Update --
   ------------------

   procedure State_Update (I : Valid_Input) is
   begin
      if I = Accelerate then
         if Speed < Speed_Type'Last then
            Speed := Speed + 1;
         end if;
      elsif I = Brake then
         if Speed > Speed_Type'First then
            Speed := Speed - 1;
         end if;
      end if;
      if Speed = 0 then
         State := Still;
      elsif Speed = 1 and then I = Accelerate then
         State := Forward;
      elsif Speed = -1 and then I = Accelerate then
         --  Oops, copy and paste error in the condition
         State := Backward;
      end if;
   end State_Update;

   ----------
   -- Halt --
   ----------

   procedure Halt is
   begin
      while State /= Still loop
         pragma Loop_Invariant (Speed_Is_Valid);
         if Speed > 0 then
            State_Update (Brake);
         else
            State_Update (Accelerate);
         end if;
      end loop;
   end Halt;

end Vehicle;
