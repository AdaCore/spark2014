package Ext with
   SPARK_Mode
is
   type My_Int is private;

private
   type My_Int is new Integer with
     Type_Invariant => My_Int >= 0;

   X : My_Int with Volatile, Async_Readers => True;
   Y : My_Int with Volatile, Async_Writers => True;
end Ext;
