package SPARK_Modes with
  SPARK_Mode => On
is
   procedure Should_Not_Prove (B : out Boolean) with
     Post => B = True;
end SPARK_Modes;
