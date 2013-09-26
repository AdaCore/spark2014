package Pack
   with SPARK_Mode
is
   G : access Boolean := new Boolean;

   function F return Boolean
     with Pre => G.all;
   procedure P;
end;
