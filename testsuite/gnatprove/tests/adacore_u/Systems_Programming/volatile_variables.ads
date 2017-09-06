with System.Storage_Elements;

package Volatile_Variables
  with SPARK_Mode
is

   AR : Integer with Volatile, Async_Readers;
   AW : Integer with Volatile, Async_Writers;
   EW : Integer with Volatile, Effective_Writes, Async_Readers;
   ER : Integer with Volatile, Effective_Reads, Async_Writers;

   procedure Read_All;

   function Read_ER return Integer;

end Volatile_Variables;
