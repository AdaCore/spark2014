package body Ext with SPARK_Mode is
   protected body Prot is
      procedure P is
      begin
         null;
      end;
   end;

   Y : R with Volatile, Async_Writers => True;

   procedure Update_Hidden_Volatile_Object is
   begin
      Y.F := Y.G;
   end;

end;
