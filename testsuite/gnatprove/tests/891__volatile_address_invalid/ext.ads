package Ext with Spark_Mode is

   type R is record
      F : Positive;
   end record;

   --  Volatile

   V : R with Volatile, Potentially_Invalid;

end Ext;
