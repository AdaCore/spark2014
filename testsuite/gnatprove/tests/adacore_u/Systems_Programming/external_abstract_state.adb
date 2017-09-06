with System.Storage_Elements;

package body External_Abstract_State
  with SPARK_Mode,
       Refined_State => (AR_State => (AR, EW),
                         AW_State => (AW, ER))
is

   AR : Integer with Volatile, Async_Readers;
   AW : Integer with Volatile, Async_Writers;
   EW : Integer with Volatile, Effective_Writes, Async_Readers;
   ER : Integer with Volatile, Effective_Reads, Async_Writers;

end External_Abstract_State;
