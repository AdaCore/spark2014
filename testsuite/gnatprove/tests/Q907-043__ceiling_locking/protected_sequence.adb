package body Protected_Sequence
  with SPARK_Mode
is
   protected body P1 is
      procedure Set (Value : Integer) is
      begin
         Data := Value;
      end Set;
   end P1;

   protected body P2 is
      procedure Set (Value : Integer) is
      begin
         P1.Set (Value);
      end Set;
   end P2;

   task body TT is
      Local : Integer := 0;
   begin
      loop
         Local := (Local + 1) mod 100;
         P2.Set (Local);
      end loop;
   end TT;

end Protected_Sequence;
