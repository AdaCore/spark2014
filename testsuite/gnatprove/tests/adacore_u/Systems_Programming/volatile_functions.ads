with System.Storage_Elements;

package Volatile_Functions
  with SPARK_Mode
is

   AR : Integer with Volatile, Async_Readers;
   AW : Integer with Volatile, Async_Writers;
   EW : Integer with Volatile, Effective_Writes, Async_Readers;
   ER : Integer with Volatile, Effective_Reads, Async_Writers;

   function Read_Non_Volatile return Integer;

   function Read_Volatile return Integer with Volatile_Function;

   function Read_ER return Integer with Volatile_Function;

end Volatile_Functions;
