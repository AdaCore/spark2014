with System.Storage_Elements;

Package body Alarm
  with Refined_State => (Blinkenlights => (Blinken_Task,
                                           Blinken_PO))
is

   protected Blinken_PO is
      procedure Turn_On;
      procedure Turn_Off;
      entry Cycle;
   private
      Blinken_State : Boolean := False;
   end Blinken_PO;

   The_Light : Boolean := False with
     Volatile,
     Atomic,
     Async_Readers, Async_Writers,
     Address => System.Storage_Elements.To_Address (16#FFFF_DDDD#),
     Part_Of => Blinken_PO;

   task Blinken_Task;

   procedure Turn_On is
   begin
      Blinken_PO.Turn_On;
   end Turn_On;

   procedure Turn_Off is
   begin
      Blinken_PO.Turn_Off;
   end Turn_Off;

   task body Blinken_Task is
   begin
      loop
         Blinken_PO.Cycle;
      end loop;
   end Blinken_Task;

   protected body Blinken_PO is
      procedure Turn_On is
      begin
         Blinken_State := True;
         The_Light     := True;
      end Turn_On;

      procedure Turn_Off is
      begin
         Blinken_State := False;
         The_Light     := False;
      end Turn_Off;

      entry Cycle when Blinken_State is
         L : constant Boolean := The_Light;
      begin
         The_Light := not L;
      end Cycle;

   end Blinken_PO;

end Alarm;
