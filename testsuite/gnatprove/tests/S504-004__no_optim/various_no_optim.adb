pragma SPARK_Mode;
with External; use External;

procedure Various_No_Optim is
begin
   -- Code Sample #2

   declare
      Cond : NvU32 with Volatile, No_Caching;
   begin
      -- Code to initialize Cond. Could be read of MMIO
      Cond := Get_Value;

      if Cond = 16#5A_3C_A5_55# then
         -- Entering a very critical path
         if (not Cond) /= 16#A5_C3_5A_AA# then
            -- FI detected. Take necessary action
            Error_Detected;
         end if;
      end if;
   end;

   -- Code Sample #3: Check loop counter after exit

   declare
      Loop_Counter : NvU32 := 0 with Volatile, No_Caching;
   begin
      while Loop_Counter < 10 loop
         -- Do work
         Loop_Counter := Loop_Counter + 1;
      end loop;
      pragma Assert (Loop_Counter = 10);
   end;

   -- Code Sample #4: CFI check

   declare
      Counter : NvU32 := 16#5A# with Volatile, No_Caching;
   begin
      Execute_Step_1;
      Counter := Counter + 1;

      Execute_Step_2;
      Counter := Counter + 1;

      Execute_Step_N;
      Counter := Counter + 1; -- At this point counter should be 5A + N
      pragma Assert (Counter = 16#5D#);
   end;
end Various_No_Optim;
