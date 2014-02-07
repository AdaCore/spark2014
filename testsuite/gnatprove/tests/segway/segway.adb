package body Segway
  with SPARK_Mode
is
   ----------------------------------------------------
   --         SPARK 2014 - Segway Example            --
   --                                                --
   -- This example illustrates the use of an Ada2012 --
   -- expression function to specify an invariant    --
   -- that must be maintained in a state-machine     --
   -- package                                        --
   ----------------------------------------------------

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin
      State := Still;
      Speed := 0;
   end Initialize;

   ------------------
   -- State_Update --
   ------------------

   procedure State_Update (I : Valid_Input) is
   begin
      case I is
         when Nothing =>
            null;
         when Accelerate =>
            if Speed < Speed_Type'Last then
               Speed := Speed + 1;
            end if;
         when Brake =>
            if Speed > Speed_Type'First then
               Speed := Speed - 1;
            end if;
      end case;
      if Speed = 0 then
         State := Still;
      elsif Speed = 1 and then I = Accelerate then
         State := Forward;
      elsif Speed = -1 and then I = Brake then
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

end Segway;
