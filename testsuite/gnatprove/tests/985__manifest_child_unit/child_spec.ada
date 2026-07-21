package Pkg.Child
  with SPARK_Mode
is
   procedure R (X : Integer)
   with Post => Sink = X;
end Pkg.Child;
