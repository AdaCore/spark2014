with System;

package P with SPARK_Mode is

   C : constant Integer
   with
       Import,
       Volatile,
       Async_Writers,
       Async_Readers => False,
       Address => System'To_Address (12);

   V3 : Integer
   with
       Import,
       Volatile,
       No_Caching,
       Async_Readers => False,
       Async_Writers => False,
       Effective_Reads => False,
       Effective_Writes => False,
       Address => System'To_Address (14);

   Bad1 : Integer
   with
       Import,
       Volatile,
       No_Caching,
       Async_Readers => True,
       Async_Writers => False,
       Effective_Reads => False,
       Effective_Writes => False,
       Address => System'To_Address (14);

   Bad2 : Integer
   with
       Import,
       Volatile,
       No_Caching,
       Async_Readers => False,
       Async_Writers => True,
       Address => System'To_Address (14);

   Bad3 : Integer
   with
       Async_Readers => False,
       Async_Writers => False,
       Effective_Writes => False,
       Effective_Reads => True,
       Import,
       Volatile,
       No_Caching,
       Address => System'To_Address (14);

   Bad4 : Integer
   with
       Effective_Writes => True,
       Import,
       Volatile,
       No_Caching,
       Address => System'To_Address (14);

end P;
