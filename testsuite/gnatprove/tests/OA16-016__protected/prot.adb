package body Prot
  with SPARK_Mode
is
   protected body P is
      function Peek return Boolean is (G);
      procedure Flip is
      begin
         G := not G;
      end Flip;
   end P;

end Prot;
