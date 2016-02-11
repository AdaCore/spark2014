pragma SPARK_Mode (On);

package body Time_Triggered_Response is

   Time_Idle : Natural := 0;

   package body History is

      function Valid return Boolean is
         ((if Time_Idle /= 0 then Always_Set_Until_Now (From => Natural'Min (Past_Time'Last, Time_Idle - 1)))
            and then
          (if Time_Idle <= Past_Time'Last then Idle_History (Time_Idle) = False));

   end History;

   procedure Update_Status (Status : out Boolean) is
   begin
      if Time_Idle >= 10 then
         Status := True;
      else
         Status := False;
      end if;
   end Update_Status;

end Time_Triggered_Response;
