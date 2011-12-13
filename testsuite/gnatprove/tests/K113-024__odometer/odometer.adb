package body Odometer is

   procedure Zero_Trip is
   begin
      Trip := 0;
   end Zero_Trip;

   function Read_Trip return Integer
   is
   begin
      return Trip;
   end Read_Trip;

   function Read_Total return Integer
   is
   begin
      return Total;
   end Read_Total;

   procedure Inc is
   begin
      Trip := Trip + 1; Total := Total + 1;
   end Inc;
end Odometer;
