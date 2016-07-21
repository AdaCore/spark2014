with Ada.Real_Time;
pragma Elaborate (Ada.Real_Time);

package P is

   Wakeup : Ada.Real_Time.Time := Ada.Real_Time.Clock;

   function Wakeup_Time return Ada.Real_Time.Time;

   task type TT;

   T1, T2 : TT; -- two tasks access unsynchronized global variable

end;
