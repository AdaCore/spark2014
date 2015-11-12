package body Volatiles_Illegal_8
  with SPARK_Mode,
       Refined_State => (State => Different_Vol)
       --  Volatile state State has different volatile properties set.
is
   Different_Vol : Integer
     with Volatile,
          Async_Readers;
end Volatiles_Illegal_8;
