package body Bundling_Abstract_State
  with SPARK_Mode,
       Refined_State => (State => (X, Y, Z))
is
   X : Integer with Volatile, Async_Readers;
   Y : Integer with Volatile, Async_Writers;
   Z : Integer := 0;
end Bundling_Abstract_State;
