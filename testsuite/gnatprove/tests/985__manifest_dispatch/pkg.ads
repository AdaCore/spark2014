package Pkg
  with SPARK_Mode
is
   Sink : Integer := 0;

   procedure P (X : Integer);
   procedure P (X : Boolean);
   procedure Q;

   procedure R (X : Integer)
   with Post => Sink = X;

   package Inner
     with SPARK_Mode
   is
      procedure S (X : Integer)
      with Post => Sink = X;
   end Inner;
end Pkg;
