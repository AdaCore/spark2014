pragma SPARK_Mode(On);
package body TickTock
   with Refined_State => (TickTock_State => Clock_Value)
is
   type Clock_Type is range 0 .. 2 ** 63 - 1;
   Clock_Value : Clock_Type := 0;

   procedure Tick
      with
         Refined_Global  => (In_Out      =>  Clock_Value),
         Refined_Depends => (Clock_Value =>+ null)
   is
   begin
      Clock_Value := Clock_Value + 1;
      -- Other housekeeping...
   end Tick;

end TickTock;
