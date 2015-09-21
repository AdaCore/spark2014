package Ext_Ax with SPARK_Mode is
   pragma Annotate (GNATprove, External_Axiomatization);
   function My_Eq (X1, X2 : Integer) return Boolean is
     (X1 = X2);
end Ext_Ax;
