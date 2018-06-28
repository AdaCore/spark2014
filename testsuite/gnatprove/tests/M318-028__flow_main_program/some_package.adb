package body Some_Package with Refined_State => (State => Y) is
   Y : Integer;
   procedure Init with Refined_Global => (Output => Y) is
   begin
      Y := 0;
   end;
end Some_Package;
