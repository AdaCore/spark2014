package PO_Not_In_Spark is

   --  Protected type is not in SPARK
   protected type PT with
     SPARK_Mode => Off
   is
      procedure Proc;
   end;

   --  Record with protected component is also not in SPARK
   type PR is
      record
         PC : PT;
      end record with Volatile;

   PO1 : PR; --  instance of protected type
   PO2 : PT; --  instance of record with protected component

   --  Body calls procedures of protected objects that are not in SPARK
   procedure Foo with SPARK_Mode => On;

end;
