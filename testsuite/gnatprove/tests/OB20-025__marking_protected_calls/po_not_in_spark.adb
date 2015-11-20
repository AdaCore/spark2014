package body PO_Not_In_Spark is

   protected body PT with
     SPARK_Mode => Off
   is
      procedure Proc is
      begin
         null;
      end;
   end;

   procedure Foo with
     SPARK_Mode
   is
   begin
      PO1.PC.Proc;
   end;

   procedure Bar with
     SPARK_Mode
   is
   begin
      PO2.Proc;
   end;

end;
