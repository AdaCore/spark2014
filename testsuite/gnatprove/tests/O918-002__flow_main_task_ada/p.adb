package body P with SPARK_Mode => On is

   task body TT is
   begin
      loop
         V := V + 1;
      end loop;
   end;

end;
