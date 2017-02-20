generic
package G with SPARK_Mode is

   function Is_Initialized return Boolean with SPARK_Mode;

   procedure Initialize with Post => Is_Initialized;

end G;
