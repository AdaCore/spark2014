package VC3
  with SPARK_Mode => On
is
   F : constant Boolean := False;
   T : constant Boolean := True;

   -- Exhaustive test for SPARK RM 7.1.2(6), where the
   -- aspects appear attached to object declarations.

   -- There are 4 aspects, so 16 cases.
   --
   -- Cases are numbered using the following assignment of binary digits:
   --   Async_Readers    = 8
   --   Async_Writers    = 4
   --   Effective_Reads  = 2
   --   Effective_Writes = 1
   --
   V0 : Integer
     with Volatile,
          Async_Readers    => F, -- illegal combination
          Async_Writers    => F,
          Effective_Reads  => F,
          Effective_Writes => F;

   V1 : Integer
     with Volatile,
          Async_Readers    => F, -- illegal combination
          Async_Writers    => F,
          Effective_Reads  => F,
          Effective_Writes => T;

   V2 : Integer
     with Volatile,
          Async_Readers    => F, -- illegal combination
          Async_Writers    => F,
          Effective_Reads  => T,
          Effective_Writes => F;

   V3 : Integer
     with Volatile,
          Async_Readers    => F, -- illegal combination
          Async_Writers    => F,
          Effective_Reads  => T,
          Effective_Writes => T;

   V4 : Integer
     with Volatile,
          Async_Readers    => F, -- OK
          Async_Writers    => T,
          Effective_Reads  => F,
          Effective_Writes => F;

   V5 : Integer
     with Volatile,
          Async_Readers    => F, -- illegal combination
          Async_Writers    => T,
          Effective_Reads  => F,
          Effective_Writes => T;

   V6 : Integer
     with Volatile,
          Async_Readers    => F, -- OK
          Async_Writers    => T,
          Effective_Reads  => T,
          Effective_Writes => F;

   V7 : Integer
     with Volatile,
          Async_Readers    => F, -- illegal combination
          Async_Writers    => T,
          Effective_Reads  => T,
          Effective_Writes => T;

   V8 : Integer
     with Volatile,
          Async_Readers    => T, -- OK
          Async_Writers    => F,
          Effective_Reads  => F,
          Effective_Writes => F;

   V9 : Integer
     with Volatile,
          Async_Readers    => T, -- OK
          Async_Writers    => F,
          Effective_Reads  => F,
          Effective_Writes => T;

   V10 : Integer
     with Volatile,
          Async_Readers    => T, -- illegal combination
          Async_Writers    => F,
          Effective_Reads  => T,
          Effective_Writes => F;

   V11 : Integer
     with Volatile,
          Async_Readers    => T, -- illegal combination
          Async_Writers    => F,
          Effective_Reads  => T,
          Effective_Writes => T;

   V12 : Integer
     with Volatile,
          Async_Readers    => T, -- OK
          Async_Writers    => T,
          Effective_Reads  => F,
          Effective_Writes => F;

   V13 : Integer
     with Volatile,
          Async_Readers    => T, -- OK
          Async_Writers    => T,
          Effective_Reads  => F,
          Effective_Writes => T;

   V14 : Integer
     with Volatile,
          Async_Readers    => T, -- OK
          Async_Writers    => T,
          Effective_Reads  => T,
          Effective_Writes => F;

   V15 : Integer
     with Volatile,
          Async_Readers    => T, -- OK
          Async_Writers    => T,
          Effective_Reads  => T,
          Effective_Writes => T;

end VC3;
