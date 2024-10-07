package Ext_1 with SPARK_Mode is
   generic
   package Gen is
      procedure P_Null;
   end Gen;

   type T is private;
private
   type C;
   type T is access C;
end Ext_1;
