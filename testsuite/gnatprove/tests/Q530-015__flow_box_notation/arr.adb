package body Arr is
   procedure Reset (This : out A) is
   begin
      This := (2, others => <>);
   end Reset;
end Arr;
