package pt_not_in_spark is

   protected type PT with
     SPARK_Mode => Off
   is
      procedure Dummy;
   end;

   type PR is
     record
       PC : PT;
     end record with Volatile;

   PO1 : PT;
   PO2 : PR;

   procedure Foo with SPARK_Mode;

   procedure Bar with SPARK_Mode;

end;
