package Split
  with SPARK_Mode
is
   U, V : Integer;

   procedure P
     with Pre => U in 1 .. 10 and then V in 1.. 10;

   procedure Q
     with Post => U in 1 .. 5 and then V in 1.. 5;

end Split;
