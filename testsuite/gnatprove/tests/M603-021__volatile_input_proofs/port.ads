-- M603-021 - Proof support for Volatile and External Variables
--
-- This package illustrates proof examples for volatile inputs

package Port
is
   --  E is an enumeration type with non contiguous representation
   --  so introduces possibility of abnormal values "between"
   --  the normal ones.
   type E is (Red, Green, Blue);
   for E use (1, 5, 13);


   --  U32 is a modular type with NO abnormal values
   type U32 is mod 2**32;
   pragma Assert (U32'Size = U32'Object_Size);

   type U8 is mod 2**8;

   -- S1 is a subtype where S1'Size < S1'Object_Size
   subtype S1 is Integer range 0 .. 17;


   V1 : S1
     with Volatile,
          Async_Writers => True;

   V1Raw : U32
     with Volatile,
          Async_Writers => True;

   -- V2 is same subtype as V1, but NOT volatile
   V2 : S1 := S1'First;

   -- V3 is a volatile modular
   V3 : U32
     with Volatile,
          Async_Writers => True;


   -- VB is a volatile Boolean - nasty since Boolean'Size = 1
   -- but Boolean'Object_Size is typically 8, so potential
   -- for 7 bits of junk in every read.
   VB : Boolean
     with Volatile,
          Async_Writers => True;

   VBRaw : U8
     with Volatile,
          Async_Writers => True;

   -- Volatile enumarated value
   VE : E
     with Volatile,
          Async_Writers => True;

   VERaw : U8
     with Volatile,
          Async_Writers => True;

   -------------------------
   -- Cases for reading V1
   -------------------------

   procedure Read_V1_Bad1 (X : out S1)
     with Global => (Input => V1),
          Depends => (X => V1),
          Post    => X'Valid and X in S1;

   procedure Read_V1_Bad2 (X : out S1)
     with Global => (Input => V1Raw),
          Depends => (X => V1Raw),
          Post    => X'Valid and X in S1;

   procedure Read_V1_Good1 (X : out S1)
     with Global => (Input => V1),
          Depends => (X => V1),
          Post    => X'Valid and X in S1;

   procedure Read_V1_Good2 (X : out S1)
     with Global => (Input => V1Raw),
          Depends => (X => V1Raw),
          Post    => X'Valid and X in S1;


   -------------------------
   -- Cases for reading VB
   -------------------------

   procedure Read_VB_Bad1 (X : out Boolean)
     with Global => (Input => VB),
          Depends => (X => VB),
          Post    => X'Valid and X in Boolean; -- Tautology?

   procedure Read_VB_Bad2 (X : out Boolean)
     with Global => (Input => VB),
          Depends => (X => VB),
          Post    => X'Valid and X in Boolean; -- Tautology?

   -------------------------
   -- Cases for reading VE
   -------------------------

   procedure Read_VE_Bad1 (X : out E)
     with Global => (Input => VE),
          Depends => (X => VE),
          Post    => X'Valid and X in E;

   procedure Read_VE_Bad2 (X : out E)
     with Global => (Input => VERaw),
          Depends => (X => VERaw),
          Post    => X'Valid and X in E;

   procedure Read_VE_Good1 (X : out E)
     with Global => (Input => VE),
          Depends => (X => VE),
          Post    => X'Valid and X in E;

   procedure Read_VE_Good2 (X : out E)
     with Global => (Input => VERaw),
          Depends => (X => VERaw),
          Post    => X'Valid and X in E;

   --------------------------
   -- No same value read test
   --------------------------

   procedure Test_NSVR1 (X : out Boolean)
     with Global => (Input => V1),
          Depends => (X => V1);

   procedure Test_NSVR2 (X : out Boolean)
     with Global => (Input => V2),
          Depends => (X => V2);


end Port;
