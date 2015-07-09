package Tagged_Conv with SPARK_Mode is
   type Root is tagged null record;
   type Child is new Root with null record;

   procedure P;
end Tagged_Conv;
