with Ada.Unchecked_Conversion;
package body Port
is

   function C is new Ada.Unchecked_Conversion (U32, Integer);

   function C2 is new Ada.Unchecked_Conversion (U8, Boolean);

   function C3 is new Ada.Unchecked_Conversion (U8, E);



   procedure Read_V1_Bad1 (X : out S1)
   is
   begin
      X := V1;  -- no validity check. Must FAIL to prove
   end Read_V1_Bad1;


   procedure Read_V1_Bad2 (X : out S1)
   is
      Tmp : U32;
   begin
      -- User attempts to cheat by reading a 32-bit
      -- modular value, and doing an unchecked conversion
      -- to S1.  No validity check, though, so must also
      -- fail to prove.
      Tmp := V1Raw;
      X := S1 (C (Tmp)); -- Should not prove
   end Read_V1_Bad2;


   procedure Read_V1_Good1 (X : out S1)
   is
      T : S1;
   begin
      -- Read direct, then immediate Valid check
      T := V1;
      if T'Valid then
         X := T; -- Should be OK
      else
         X := S1'First;
      end if;
   end Read_V1_Good1;

   procedure Read_V1_Good2 (X : out S1)
   is
      T : S1;
      Tmp : U32;
   begin
      -- Read as 32-but modular, then unchecked convert,
      -- then validity check.
      Tmp := V1Raw;
      T := S1 (C (Tmp));
      if T'Valid then
         X := T; -- Should be OK
      else
         X := S1'First;
      end if;
   end Read_V1_Good2;



   procedure Read_VB_Bad1 (X : out Boolean)
   is
   begin
      -- Direct read.  Should NOT prove, since VB might
      -- be abnormal
      X := VB;
   end Read_VB_Bad1;

   procedure Read_VB_Bad2 (X : out Boolean)
   is
      Tmp : U8;
   begin
      -- Read unsigned 8 bits, then unchecked convert to Boolean
      -- Should NOT prove.
      Tmp := VBRaw;
      X := C2 (Tmp);
   end Read_VB_Bad2;




   procedure Read_VE_Bad1 (X : out E)
   is
   begin
      -- Direct read.  Should NOT prove, since VE might
      -- be abnormal
      X := VE;
   end Read_VE_Bad1;

   procedure Read_VE_Bad2 (X : out E)
   is
      Tmp : U8;
   begin
      Tmp := VERaw;
      -- Read unsigned 8 bits, then unchecked convert to E
      -- Should NOT prove.
      X := C3 (Tmp);
   end Read_VE_Bad2;

   procedure Read_VE_Good1 (X : out E)
   is
      T : E;
   begin
      -- Direct read followed by immediate Valid test
      T := VE;
      if T'Valid then
         X := T; -- Should be OK
      else
         X := E'First;
      end if;
   end Read_VE_Good1;

   procedure Read_VE_Good2 (X : out E)
   is
      T : E;
      Tmp : U8;
   begin
      -- Read modular 8 bits, unchecked convert, and valid test
      Tmp := VERaw;
      T := C3 (Tmp);
      if T'Valid then
         X := T; -- Should be OK
      else
         X := E'First;
      end if;
   end Read_VE_Good2;



   procedure Test_NSVR1 (X : out Boolean)
   is
      T1 : S1;
      T2 : S1;
   begin
      T1 := V1;
      T2 := V1;

      -- must NOT prove, since V1 is volatile and has
      -- Async_Writers
      pragma Assert (T1 = T2);

      X := (T1 = T2);
   end Test_NSVR1;


   -- Same as Test_NSVR1 but reading V2, which is NOT
   -- Volatile.
   procedure Test_NSVR2 (X : out Boolean)
   is
      T1 : S1;
      T2 : S1;
   begin
      T1 := V2;
      T2 := V2;

      -- MUST PROVE OK
      pragma Assert (T1 = T2);

      X := (T1 = T2);
   end Test_NSVR2;


end Port;
