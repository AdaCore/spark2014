with Alarm;  use Alarm;
with Sensor; use Sensor;

package Watchdog is

   task Watchdog_Task;
   --  with Global => (Input => Sensor.Power_Level,
   --                  Output => Alarm.Blinkenlights);

end Watchdog;
