package body Protected_Unprotected
  with SPARK_Mode
is
   Data : Integer := 0;

   protected body P is
      procedure Set (Value : Integer) is
      begin
         Data := Value;
      end Set;
   end P;

   task body TT is
      Local : Integer := 0;
   begin
      loop
         Local := (Local + 1) mod 100;
         P.Set (Local);
      end loop;
   end TT;

end Protected_Unprotected;
