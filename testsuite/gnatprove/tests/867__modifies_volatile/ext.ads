package Ext with SPARK_Mode is
   type R is record
      F, G : Integer;
   end record;

   X : R with Volatile, Async_Writers => True;

   protected Prot is
      procedure P;
   end Prot;

end Ext;
