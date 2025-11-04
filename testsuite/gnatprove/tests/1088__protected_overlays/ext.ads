pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package Ext with SPARK_Mode is

   protected type PT is
      procedure P;
   private
      X : Integer := 0;
   end;

   protected PO is
      procedure P;
   end;

   X : Integer := 1 with Part_Of => PO;

end Ext;
