package P is

   no_of_cpus : Integer;

   type cpu_number is new Integer range 0..no_of_cpus;
   --  This type is not in SPARK due to variable in bound

end;
