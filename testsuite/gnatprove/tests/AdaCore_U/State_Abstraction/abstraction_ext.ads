package Abstraction_Ext with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   V_Ext : Integer := Id (1);
end Abstraction_Ext;
