pragma SPARK_Mode (On);

package Time_Triggered_Response is

   package History with Ghost is
      Max_History : constant := 50;
      subtype Past_Time is Natural range 0 .. Max_History;
      type Boolean_History is array (Past_Time) of Boolean;
      Idle_History : Boolean_History := (others => False);

      function Always_Set_Until_Now (From : Past_Time) return Boolean is
         (for all T in Past_Time range 0 .. From => Idle_History (T) = True);

      function Valid return Boolean;

   end History;

   procedure Update_Status (Status : out Boolean) with
     Pre => History.Valid,
     Contract_Cases =>
       (History.Always_Set_Until_Now (From => 9) =>
          Status = True,
        others =>
          Status = False);

end Time_Triggered_Response;
