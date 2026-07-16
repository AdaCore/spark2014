package Pkg
  with SPARK_Mode
is
   Sink : Integer := 0;

   procedure R (X : Integer)
   with Post => Sink = X;

   package Inner
     with SPARK_Mode
   is
      procedure S (X : Integer)
      with Post => Sink = X;
   end Inner;
end Pkg;
