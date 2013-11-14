package body Processing
is

   subtype State_Type is Integer range 0 .. 100;

   State : State_Type := 77;

   procedure Get_Processed_Data (Value : out Integer)
   is
      Local_Value : Integer;
   begin
      Local_Value := Raw_Data.Get_Value;
      if Local_Value < 0 or else Local_Value >= Integer'Last - State then
         Local_Value := 42;
      end if;
      Value := State + Local_Value;
      if State <= State_Type'Last - Local_Value then
         State := State + Local_Value;
      else
         State := 0;
      end if;

   end Get_Processed_Data;

end Processing;
