package body Interrupt_Priority with SPARK_Mode is
   protected body No_Interrupt_Needed_1 is
      procedure OK is
      begin
         if I < Integer'Last then
            I := I + 1;
         end if;
      end OK;
   end No_Interrupt_Needed_1;
end Interrupt_Priority;
