package Reduced_01
  with SPARK_Mode
is
   type NewFloat is new Float;

   function Foo (X : NewFloat) return NewFloat
   is (if X >= 0.0 then X else -X);

end Reduced_01;
