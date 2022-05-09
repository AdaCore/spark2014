package B with SPARK_Mode is

   function Valid return Boolean;

   procedure Set
   with Post => Valid;

   procedure P;

end B;
