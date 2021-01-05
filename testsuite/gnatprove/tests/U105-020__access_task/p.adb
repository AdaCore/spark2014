package body P with SPARK_Mode is
   task body TT is
   begin
      loop
         X.all := not X.all;
      end loop;
   end TT;
end P;
