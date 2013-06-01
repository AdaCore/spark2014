package Pack is
   pragma SPARK_Mode (On);

   G : access Boolean := new Boolean;

   function F return Boolean
     with Pre => G.all;
   procedure P;
end;
