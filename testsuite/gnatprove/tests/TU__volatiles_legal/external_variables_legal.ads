with System.Storage_Elements;

package External_Variables_Legal is
   type Volatile_Type is record
      I : Integer;
   end record with Volatile;

   --  Only the following combinations should be accepted.
   Var1 : Volatile_Type
      with Async_Readers,
           Effective_Writes,
           Address => System.Storage_Elements.To_Address (16#BAD#);

   Var2 : Volatile_Type
      with Async_Writers,
           Effective_reads,
           Address => System.Storage_Elements.To_Address (16#BEE#);

   Var3 : Volatile_Type
      with Async_Readers,
           Address => System.Storage_Elements.To_Address (16#DEAD#);

   Var4 : Volatile_Type
      with Async_Writers,
           Address => System.Storage_Elements.To_Address (16#C0FFEE#);

   Var5 : Volatile_Type
      with Async_Readers,
           Async_Writers,
           Effective_Writes,
           Address => System.Storage_Elements.To_Address (16#BEEF#);

   Var6 : Volatile_Type
      with Async_Readers,
           Async_Writers,
           Effective_Reads,
           Address => System.Storage_Elements.To_Address (16#FEED#);

   Var7 : Volatile_Type
      with Async_Readers,
           Async_Writers,
           Address => System.Storage_Elements.To_Address (16#ACE#);

   Var8 : Volatile_Type
      with Async_Readers,
           Async_Writers,
           Effective_Reads,
           Effective_Writes,
           Address => System.Storage_Elements.To_Address (16#FACE#);
end External_Variables_Legal;
