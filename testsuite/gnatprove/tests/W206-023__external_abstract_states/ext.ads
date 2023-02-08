package Ext with SPARK_Mode, Abstract_State => (G with External) is

   function Read_G return Integer with Volatile_Function, Global => G;
   --  Function with explicit global with effective reads

private
   X : Integer with Volatile, Part_Of => G;
end Ext;
