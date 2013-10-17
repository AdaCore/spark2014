with HAL;
use type HAL.Byte_T;

procedure Main
  with SPARK_Mode,
       Global  => (Input  => HAL.FIFO_Status,
                   In_Out => (HAL.Serial_In,
                              HAL.Wdog_State),
                   Output => (HAL.FIFO_Control,
                              HAL.Serial_Out)),
       Depends => (HAL.Serial_In    =>+ (HAL.FIFO_Status,
                                         HAL.Wdog_State),
                   HAL.Serial_Out   =>  (HAL.Serial_In,
                                         HAL.FIFO_Status,
                                         HAL.Wdog_State),
                   HAL.Wdog_State   =>+ HAL.FIFO_Status,
                   HAL.FIFO_Control =>  null)
is
   Wdog_Timed_Out, Found : Boolean;
   A_Byte                : HAL.Byte_T;
begin
   HAL.Clear_Out_FIFO;

   -- The start of the data is marked by the sequence 16#5555#
   -- Skip until we find the start of the message or the FIFO is empty.
   loop
      HAL.Wdog_Timed_Out (Wdog_Timed_Out);
      exit when Wdog_Timed_Out;
      HAL.Skip_To (16#55#, Found);
      exit when not Found;
      HAL.Get_Byte (A_Byte);
      exit when A_Byte = 16#55#;
   end loop;

   if Found and not Wdog_Timed_Out then
      -- We have found the start of the data

      -- As long as the watchdog doesn't time out, move data
      -- from Serial_In to Serial_Out.
      loop
         HAL.Wdog_Timed_Out (Wdog_Timed_Out);

         exit when Wdog_Timed_Out;

         HAL.Get_Byte (A_Byte);
         HAL.Put_Byte (A_Byte);
         end loop;
   end if;

end Main;
