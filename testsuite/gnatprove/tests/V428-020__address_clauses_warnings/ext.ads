with System; use System;
package Ext with SPARK_Mode is
   C1 : constant Integer
   with
       Import,
       Volatile,
       Async_Writers,
       Address => System'To_Address (12);
   --  Here we have no warnings, C1 cannot be modified and potential writes
   --  are taken into account.
   V1 : Integer
   with
       Import,
       Volatile,
       Async_Readers,
       Address => System'To_Address (12);
   --  Here we have a warning that writing to V1 might affect other objects.
   --  We have no warnings about potential writes to V1 because we are
   --  implicitly saying that V1 has no asynchronous writers here.
   V2 : Integer
   with
       Import,
       Volatile,
       Async_Writers,
       Address => System'To_Address (13);
   --  Here we have no warnings, potential writes are taken into account and we
   --  are implicitly saying that V2 has no asynchronous readers.
   V3 : Integer
   with
       Import,
       Volatile,
       No_Caching,
       Address => System'To_Address (14);
   --  Here we have no warnings, we are implicitly saying that V3 has no
   --  asynchronous readers and no asynchronous writers.
   C2 : constant Integer
   with
       Import,
       Volatile,
       Async_Readers,
       Address => System'To_Address (15);
   --  Here we have no warnings, C2 cannot be modified and we are implicitly
   --  saying that it has no asynchronous writers. Note that asynchronous
   --  readers do not make much difference for a constant, but No_Caching is
   --  not allowed on constants.
end Ext;
