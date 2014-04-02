package No_Separate_Spec with
  SPARK_Mode => On
is
   procedure Should_Prove (B : out Boolean) with
     Post => B = True;
end No_Separate_Spec;
