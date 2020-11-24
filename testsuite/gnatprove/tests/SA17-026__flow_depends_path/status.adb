package body Status
   with Refined_State => (S => current_status, mode => (found, topic))
is
   current_status : Boolean;

   found : Boolean;
   topic : Integer;

   procedure set (device : Integer)
     with Global => (In_Out => (Time.S, current_status))
   is begin null; end;

   procedure update
     with Refined_Global => (Input  => topic,
                             In_Out => (Time.S, current_status))
   is
   begin
      set (topic);
   end update;

end Status;
