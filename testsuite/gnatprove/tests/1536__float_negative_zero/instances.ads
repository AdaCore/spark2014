with Zero_Powers;

package Instances with SPARK_Mode is
   --  Exercise both signs of zero in each supported floating-point format
   package Single_Negative is new Zero_Powers (Float, -1.0);
   package Single_Positive is new Zero_Powers (Float, 1.0);
   package Double_Negative is new Zero_Powers (Long_Float, -1.0);
   package Double_Positive is new Zero_Powers (Long_Float, 1.0);
   package Extended_Negative is new Zero_Powers (Long_Long_Float, -1.0);
   package Extended_Positive is new Zero_Powers (Long_Long_Float, 1.0);
end Instances;
