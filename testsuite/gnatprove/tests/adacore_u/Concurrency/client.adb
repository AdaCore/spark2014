with Service; use Service;

package body Client
  with SPARK_Mode
is
   task body T is
      X : Integer;
   begin
      loop
         Extract (X);
      end loop;
   end T;
end Client;
