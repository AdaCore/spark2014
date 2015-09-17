package body T
  with SPARK_Mode
is
   X : Integer;
   task body TT is
   begin
      loop
         X := 0;
      end loop;
   end TT;
end T;
