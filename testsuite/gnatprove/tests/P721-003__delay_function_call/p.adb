package body P is

   function Wakeup_Time return Ada.Real_Time.Time is (Wakeup);

   task body TT is
      --  Wakeup : Ada.Real_Time.Time := Wakeup_Time;
      --
      --  Here function call (and access to unsynchronized global variable)
      --  is detected.
   begin
      loop
         delay until Wakeup_Time; --  but here it is not
      end loop;
   end;

end;
