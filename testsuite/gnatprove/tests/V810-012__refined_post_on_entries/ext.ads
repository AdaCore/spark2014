pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);
package Ext with SPARK_Mode is

   protected type P is
     entry E (X : Integer);
   private
     C : Integer := 0;
   end P;

end Ext;
