package body P is
   procedure Dummy is
   begin
      delay until
        (if Truth
         then Ada.Real_Time.Time_First
         else Ada.Real_Time.Time_Last);
      --  Call to Truth will reference X in Truth's precondition
   end;
end;
