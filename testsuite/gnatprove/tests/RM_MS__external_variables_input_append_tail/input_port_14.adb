with System.Storage_Elements;

package body Input_Port_14
  with SPARK_Mode,
       Refined_State => (Inputs => Input_Port)
is
   Input_Port : Integer
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#ACECAF0#);

   procedure Read_From_Port(Input_Value : out Integer)
     with Refined_Global  => Input_Port,
          Refined_Depends => (Input_Value => Input_Port)
   is
      First_Read  : Integer;
      Second_Read : Integer;
   begin
      Second_Read := Input_Port;    -- Ensure Second_Read is initialized
      pragma Assume (Second_Read'Valid);
      First_Read  := Second_Read;   -- but it is infact the First_Read.
      if First_Read = 0 then
         Second_Read := Input_Port; -- Now it is the Second_Read
         pragma Assume (Second_Read'Valid);
         Input_Value := Second_Read;
      else
         Input_Value := First_Read;
      end if;
      pragma Assert ((First_Read = 0 and then Input_Value = Second_Read)
                     or else (Input_Value = First_Read));
   end Read_From_Port;
end Input_Port_14;
