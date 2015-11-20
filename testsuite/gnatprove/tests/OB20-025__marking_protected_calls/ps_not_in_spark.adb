package body ps_not_in_spark is

   protected body PT
   is
      procedure Dummy with SPARK_Mode => Off is
      begin
         null;
      end;
   end;

   procedure Foo with SPARK_Mode is
   begin
      PO1.Dummy;
   end;

   procedure Bar with SPARK_Mode is
   begin
      PO2.PC.Dummy;
   end;

end;
