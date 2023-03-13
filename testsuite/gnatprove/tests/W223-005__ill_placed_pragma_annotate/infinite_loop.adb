package body Infinite_loop with SPARK_Mode is

   procedure Loop_Indefinitely is
   begin
      loop
         null;
      end loop;
   end Loop_Indefinitely;

end Infinite_loop;
