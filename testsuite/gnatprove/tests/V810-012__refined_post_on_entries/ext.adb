package body Ext with SPARK_Mode is

   protected body P is
      entry E (X : Integer) with Refined_Post => C = X when C /= 0 is
      begin
         C := X;
      end E;
   end P;

end Ext;
