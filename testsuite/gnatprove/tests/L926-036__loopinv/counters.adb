package body Counters is

   ----------
   -- Tick --
   ----------

   procedure Tick (C : in out Counter) is
      M : Change_Mode renames C.Mode;

   begin
      --  Increase the number of ticks

      C.T := C.T + 1;

      --  Update the counter

      if M = Increase then
         C.C := C.C + 1;
      elsif M = Increase_Then_Decrease then
         if C.T >= C.Ticks then
            C.C := C.C - 1;
         else
            C.C := C.C + 1;
         end if;
      elsif M = Decrease then
         C.C := C.C - 1;
      elsif M = Decrease_Then_Increase then
         if C.T >= C.Ticks then
            C.C := C.C + 1;
         else
            C.C := C.C - 1;
         end if;
      end if;
   end Tick;

   -----------
   -- Value --
   -----------

   function Value (C : Counter) return Integer is
   begin
      return C.C;
   end Value;
end Counters;
