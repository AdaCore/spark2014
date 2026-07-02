package Pkg
  with SPARK_Mode
is
   protected type Box is
      entry Set (X : Integer)
      with Post => X = X;
   private
      Value : Integer := 0;
   end Box;
end Pkg;
