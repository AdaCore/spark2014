package body Interrupt_Priority with SPARK_Mode is
   protected body No_Interrupt_Needed_1 is
      procedure OK is
      begin
         if I < Integer'Last then
            I := I + 1;
         end if;
      end OK;
   end No_Interrupt_Needed_1;
   protected body Interrupt_Needed_1 is
      procedure OK is
      begin
         if I < Integer'Last then
            I := I + 1;
         end if;
      end OK;
   end Interrupt_Needed_1;
   protected body No_Interrupt_Needed_2 is
      procedure OK is
      begin
         if I < Integer'Last then
            I := I + 1;
         end if;
      end OK;
   end No_Interrupt_Needed_2;
end Interrupt_Priority;
