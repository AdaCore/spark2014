package body Ext with SPARK_Mode is

   protected body PT is
      procedure P is
         L : Integer := 0 with Address => X'Address;
      begin
         null;
      end P;
   end PT;

   protected body PO is
      procedure P is
         L : Integer := 0 with Address => X'Address;
      begin
         null;
      end P;
   end PO;

end Ext;
