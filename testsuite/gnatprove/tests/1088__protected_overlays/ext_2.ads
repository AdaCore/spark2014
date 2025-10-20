pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package Ext_2 with SPARK_Mode is
   G : Integer := 1;

   protected PO is
      procedure P;
   end;

   X : Integer := 1 with Part_Of => PO;
   Y : Integer := 1 with Address => G'Address, Part_Of => PO; --  Rejected in marking

end Ext_2;
