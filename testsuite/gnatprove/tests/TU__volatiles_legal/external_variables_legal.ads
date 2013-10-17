with System.Storage_Elements;

package External_Variables_Legal
  with SPARK_Mode
is
   type Volatile_Type is record
      I : Integer;
   end record with Volatile;

   --  Only the following combinations should be accepted.
   Var1 : Volatile_Type
      with Async_Readers,
           Effective_Writes,
           Address => System.Storage_Elements.To_Address (16#BAD0#);

   Var2 : Volatile_Type
      with Async_Writers,
           Effective_reads,
           Address => System.Storage_Elements.To_Address (16#BEE0#);

   Var3 : Volatile_Type
      with Async_Readers,
           Address => System.Storage_Elements.To_Address (16#DEAD0#);

   Var4 : Volatile_Type
      with Async_Writers,
           Address => System.Storage_Elements.To_Address (16#C0FFEE0#);

   Var5 : Volatile_Type
      with Async_Readers,
           Async_Writers,
           Effective_Writes,
           Address => System.Storage_Elements.To_Address (16#BEEF0#);

   Var6 : Volatile_Type
      with Async_Readers,
           Async_Writers,
           Effective_Reads,
           Address => System.Storage_Elements.To_Address (16#FEED0#);

   Var7 : Volatile_Type
      with Async_Readers,
           Async_Writers,
           Address => System.Storage_Elements.To_Address (16#ACE0#);

   Var8 : Volatile_Type
      with Async_Readers,
           Async_Writers,
           Effective_Reads,
           Effective_Writes,
           Address => System.Storage_Elements.To_Address (16#FACE0#);
end External_Variables_Legal;
