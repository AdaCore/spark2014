package body pt_not_in_spark is

   protected body PT with
     SPARK_Mode => Off
   is
      procedure Dummy is
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
