package body Processing
  with SPARK_Mode,
       Refined_State => (State => S)
is
   subtype State_Type is Integer range 0 .. 100;

   S : State_Type := 77;

   procedure Get_Processed_Data (Value : out Integer)
     with Refined_Global  => (Input  => Raw_Data.State,
                              In_Out => S),
          Refined_Depends => ((Value,
                               S) => (S,
                                      Raw_Data.State))
   is
      Local_Value : Integer;
   begin
      Local_Value := Raw_Data.Get_Value;
      if Local_Value < 0 or else Local_Value >= Integer'Last - S then
         Local_Value := 42;
      end if;
      Value := S + Local_Value;
      if S <= State_Type'Last - Local_Value then
         S := S + Local_Value;
      else
         S := 0;
      end if;
   end Get_Processed_Data;
end Processing;
