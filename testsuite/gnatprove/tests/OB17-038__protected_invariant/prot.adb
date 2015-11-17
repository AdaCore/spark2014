package body Prot
  with SPARK_Mode
is
   protected body T is
      procedure Check is
      begin
         pragma Assert (Data.V >= 0);
      end Check;
   end T;
end Prot;
