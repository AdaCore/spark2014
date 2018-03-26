package body P with SPARK_Mode is
   procedure Dummy is
   begin
      for J in 1 .. Bad.X.C loop
         null;
      end loop;
   end;
end;
