package VC
  with SPARK_Mode => On
is
   --  Tests for legal/illegal placement of external aspects

   --  Types

   type I is range 1 .. 10
     with Async_Readers; -- Illegal - only applies to objects

   type I2 is range 1 .. 10
     with Async_Readers => True; -- Illegal - only applies to objects

   type I3 is range 1 .. 10
     with Async_Readers => False; -- Illegal - only applies to objects

   type T1 is array (I) of Integer
     with Volatile; -- OK

   type T2 is array (I) of Integer
     with Volatile,
          Async_Readers    => True, -- illegal - only applies to objects
          Async_Writers    => False,
          Effective_Writes => False,
          Effective_Reads  => False;


   type T3 is array (I) of Integer
     with Volatile,
          Async_Readers    => False, -- illegal - only applies to objects
          Async_Writers    => False,
          Effective_Writes => False,
          Effective_Reads  => False;

   --  Subtypes

   subtype S1 is Integer range 1 .. 10
     with Async_Readers; -- illegal - only applies to objects

   subtype S2 is Integer range 1 .. 10
     with Async_Readers => True; -- illegal - only applies to objects

   subtype S3 is Integer range 1 .. 10
     with Async_Readers => False; -- illegal - only applies to objects

   --  Constants

   C1 : constant Integer
     with Volatile, Import, Convention => C;

   C2 : constant Integer
     with Volatile,
          Async_Readers,
          Import,
          Convention => C;

   C3 : constant Integer
     with Volatile,
          Async_Readers => True,
          Import,
          Convention => C;

   C4 : constant Integer
     with Volatile,
          Async_Readers => False, -- also illegal - not a variable
          Import,
          Convention => C;

   --  Subprograms

   procedure P1 -- OK
     with Import,
          Convention => C;

   procedure P2
     with Import,
          Async_Readers, -- illegal - only applies to objects
          Convention => C;

   procedure P3
     with Import,
          Async_Readers => True, -- illegal - only applies to objects
          Convention => C;

   procedure P4
     with Import,
          Async_Readers => False, -- illegal - only applies to objects
          Convention => C;
end VC;
