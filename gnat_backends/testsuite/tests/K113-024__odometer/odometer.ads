package Odometer
is
   Trip  : Integer;
   Total : Integer;

   procedure Zero_Trip
      with Post => (Trip = 0);

   function Read_Trip return Integer;
   function Read_Total return Integer;

   procedure Inc
      with Pre => (Trip < Integer'Last and then Total < Integer'Last),
           Post => (Trip = Trip'Old + 1 and then Total = Total'Old + 1);
end Odometer;
