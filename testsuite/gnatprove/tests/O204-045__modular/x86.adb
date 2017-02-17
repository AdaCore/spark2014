package body X86
with SPARK_Mode
is

   procedure CallExit
   is
   begin
      Exit_Called := true;
   end CallExit;

   -----------------------------------------------------------------------
   --            Implementation of AL, AH, AX, EAX, and RAX             --
   -----------------------------------------------------------------------

   function AL return Unsigned8 is
   begin
      return Unsigned8(RAX and 16#00000000000000FF#);
   end AL;

   procedure Write_AL(Val : in Unsigned8) is
   begin
      RAX := (RAX and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_AL;

   function AH return Unsigned8 is
   begin
      return Unsigned8'Mod((RAX and 16#000000000000FF00#) / 256);
   end AH;

   procedure Write_AH(Val : in Unsigned8) is
   begin
      RAX := ((RAX and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256));
   end Write_AH;

   function AX return Unsigned16 is
   begin
      return Unsigned16(RAX and 16#000000000000FFFF#);
   end AX;

   procedure Write_AX(Val : in Unsigned16) is
   begin
      RAX := (RAX and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end Write_AX;

   function EAX return Unsigned32 is
   begin
      return Unsigned32(RAX and 16#00000000FFFFFFFF#);
   end EAX;

   procedure Write_EAX(Val : in Unsigned32) is
   begin
      RAX := (RAX and 16#FFFFFFFF00000000#) or Unsigned64(Val);
   end Write_EAX;

   -----------------------------------------------------------------------
   --            Implementation of CL, CH, CX, ECX, and RCX             --
   -----------------------------------------------------------------------

   function CL return Unsigned8 is
   begin
      return Unsigned8(RCX and 16#00000000000000FF#);
   end CL;

   procedure Write_CL(Val : in Unsigned8) is
   begin
      RCX := (RCX and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_CL;

   function CH return Unsigned8 is
   begin
      return Unsigned8'Mod((RCX and 16#000000000000FF00#) / 256);
   end CH;

   procedure Write_CH(Val : in Unsigned8) is
   begin
      RCX := ((RCX and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256));
   end Write_CH;

   function CX return Unsigned16 is
   begin
      return Unsigned16(RCX and 16#000000000000FFFF#);
   end CX;

   procedure Write_CX(Val : in Unsigned16) is
   begin
      RCX := (RCX and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end Write_CX;

   function ECX return Unsigned32 is
   begin
      return Unsigned32(RCX and 16#00000000FFFFFFFF#);
   end ECX;

   procedure Write_ECX(Val : in Unsigned32) is
   begin
      RCX := (RCX and 16#FFFFFFFF00000000#) or Unsigned64(Val);
   end Write_ECX;

   -----------------------------------------------------------------------
   --            Implementation of DL, DH, DX, EDX, and RDX             --
   -----------------------------------------------------------------------

   function DL return Unsigned8 is
   begin
      return Unsigned8(RDX and 16#00000000000000FF#);
   end DL;

   procedure Write_DL(Val : in Unsigned8) is
   begin
      RDX := (RDX and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_DL;

   function DH return Unsigned8 is
   begin
      return Unsigned8'Mod((RDX and 16#000000000000FF00#) / 256);
   end DH;

   procedure Write_DH(Val : in Unsigned8) is
   begin
      RDX := ((RDX and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256));
   end Write_DH;

   function DX return Unsigned16 is
   begin
      return Unsigned16(RDX and 16#000000000000FFFF#);
   end DX;

   procedure Write_DX(Val : in Unsigned16) is
   begin
      RDX := (RDX and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end Write_DX;

   function EDX return Unsigned32 is
   begin
      return Unsigned32(RDX and 16#00000000FFFFFFFF#);
   end EDX;

   procedure Write_EDX(Val : in Unsigned32) is
   begin
      RDX := (RDX and 16#FFFFFFFF00000000#) or Unsigned64(Val);
   end Write_EDX;

   -----------------------------------------------------------------------
   --            Implementation of BL, BH, BX, EBX, and RBX             --
   -----------------------------------------------------------------------

   function BL return Unsigned8 is
   begin
      return Unsigned8(RBX and 16#00000000000000FF#);
   end BL;

   procedure Write_BL(Val : in Unsigned8) is
   begin
      RBX := (RBX and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_BL;

   function BH return Unsigned8 is
   begin
      return Unsigned8'Mod((RBX and 16#000000000000FF00#) / 256);
   end BH;

   procedure Write_BH(Val : in Unsigned8) is
   begin
      RBX := ((RBX and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256));
   end Write_BH;

   function BX return Unsigned16 is
   begin
      return Unsigned16(RBX and 16#000000000000FFFF#);
   end BX;

   procedure Write_BX(Val : in Unsigned16) is
   begin
      RBX := (RBX and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end Write_BX;

   function EBX return Unsigned32 is
   begin
      return Unsigned32(RBX and 16#00000000FFFFFFFF#);
   end EBX;

   procedure Write_EBX(Val : in Unsigned32) is
   begin
      RBX := (RBX and 16#FFFFFFFF00000000#) or Unsigned64(Val);
   end Write_EBX;

   -----------------------------------------------------------------------
   --                Implementation of SP, ESP, and RSP                 --
   -----------------------------------------------------------------------

   function SP return Unsigned16 is
   begin
      return Unsigned16(RSP and 16#000000000000FFFF#);
   end SP;

   procedure Write_SP(Val : in Unsigned16) is
   begin
      RSP := (RSP and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end Write_SP;

   function ESP return Unsigned32 is
   begin
      return Unsigned32(RSP and 16#00000000FFFFFFFF#);
   end ESP;

   procedure Write_ESP(Val : in Unsigned32) is
   begin
      RSP := (RSP and 16#FFFFFFFF00000000#) or Unsigned64(Val);
   end Write_ESP;

   -----------------------------------------------------------------------
   --                Implementation of BP, EBP, and RBP                 --
   -----------------------------------------------------------------------

   function BP return Unsigned16 is
   begin
      return Unsigned16(RBP and 16#000000000000FFFF#);
   end BP;

   procedure Write_BP(Val : in Unsigned16) is
   begin
      RBP := (RBP and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end Write_BP;

   function EBP return Unsigned32 is
   begin
      return Unsigned32(RBP and 16#00000000FFFFFFFF#);
   end EBP;

   procedure Write_EBP(Val : in Unsigned32) is
   begin
      RBP := (RBP and 16#FFFFFFFF00000000#) or Unsigned64(Val);
   end Write_EBP;

   -----------------------------------------------------------------------
   --                Implementation of SI, ESI, and RSI                 --
   -----------------------------------------------------------------------

   function SI return Unsigned16 is
   begin
      return Unsigned16(RSI and 16#000000000000FFFF#);
   end SI;

   procedure Write_SI(Val : in Unsigned16) is
   begin
      RSI := (RSI and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end Write_SI;

   function ESI return Unsigned32 is
   begin
      return Unsigned32(RSI and 16#00000000FFFFFFFF#);
   end ESI;

   procedure Write_ESI(Val : in Unsigned32) is
   begin
      RSI := (RSI and 16#FFFFFFFF00000000#) or Unsigned64(Val);
   end Write_ESI;

   -----------------------------------------------------------------------
   --                Implementation of DI, EDI, and RDI                 --
   -----------------------------------------------------------------------

   function DI return Unsigned16 is
   begin
      return Unsigned16(RDI and 16#000000000000FFFF#);
   end DI;

   procedure Write_DI(Val : in Unsigned16) is
   begin
      RDI := (RDI and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end Write_DI;

   function EDI return Unsigned32 is
   begin
      return Unsigned32(RDI and 16#00000000FFFFFFFF#);
   end EDI;

   procedure Write_EDI(Val : in Unsigned32) is
   begin
      RDI := (RDI and 16#FFFFFFFF00000000#) or Unsigned64(Val);
   end Write_EDI;

   -----------------------------------------------------------------------
   --                Implementation of R8 and R8L                       --
   -----------------------------------------------------------------------

   function R8L return Unsigned8 is
   begin
      return Unsigned8(R8 and 16#00000000000000FF#);
   end R8L;

   procedure Write_R8L(Val : in Unsigned8) is
   begin
      R8 := (R8 and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_R8L;

   -----------------------------------------------------------------------
   --                Implementation of R9 and R9L                       --
   -----------------------------------------------------------------------

   function R9L return Unsigned8 is
   begin
      return Unsigned8(R9 and 16#00000000000000FF#);
   end R9L;

   procedure Write_R9L(Val : in Unsigned8) is
   begin
      R9 := (R9 and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_R9L;

   -----------------------------------------------------------------------
   --                Implementation of R10 and R10L                       --
   -----------------------------------------------------------------------

   function R10L return Unsigned8 is
   begin
      return Unsigned8(R10 and 16#00000000000000FF#);
   end R10L;

   procedure Write_R10L(Val : in Unsigned8) is
   begin
      R10 := (R10 and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_R10L;

   -----------------------------------------------------------------------
   --                Implementation of R11 and R11L                       --
   -----------------------------------------------------------------------

   function R11L return Unsigned8 is
   begin
      return Unsigned8(R11 and 16#00000000000000FF#);
   end R11L;

   procedure Write_R11L(Val : in Unsigned8) is
   begin
      R11 := (R11 and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_R11L;

   -----------------------------------------------------------------------
   --                Implementation of R12 and R12L                       --
   -----------------------------------------------------------------------

   function R12L return Unsigned8 is
   begin
      return Unsigned8(R12 and 16#00000000000000FF#);
   end R12L;

   procedure Write_R12L(Val : in Unsigned8) is
   begin
      R12 := (R12 and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_R12L;

   -----------------------------------------------------------------------
   --                Implementation of R13 and R13L                       --
   -----------------------------------------------------------------------

   function R13L return Unsigned8 is
   begin
      return Unsigned8(R13 and 16#00000000000000FF#);
   end R13L;

   procedure Write_R13L(Val : in Unsigned8) is
   begin
      R13 := (R13 and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_R13L;

   -----------------------------------------------------------------------
   --                Implementation of R14 and R14L                       --
   -----------------------------------------------------------------------

   function R14L return Unsigned8 is
   begin
      return Unsigned8(R14 and 16#00000000000000FF#);
   end R14L;

   procedure Write_R14L(Val : in Unsigned8) is
   begin
      R14 := (R14 and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_R14L;

   -----------------------------------------------------------------------
   --                Implementation of R15 and R15L                       --
   -----------------------------------------------------------------------

   function R15L return Unsigned8 is
   begin
      return Unsigned8(R15 and 16#00000000000000FF#);
   end R15L;

   procedure Write_R15L(Val : in Unsigned8) is
   begin
      R15 := (R15 and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_R15L;

   -----------------------------------------------------------------------
   --                         Read/Write Memory                         --
   -----------------------------------------------------------------------

   function ReadMem8(addr : in Unsigned64) return Unsigned8
   is
   begin
      return Memory(addr);
   end ReadMem8;

   -- Note that if addr is Unsigned64'Last, this will take the last byte in
   -- Memory as the "low" byte and the first byte in Memory as the "high" byte
   function ReadMem16(addr: in Unsigned64) return Unsigned16
   is
   begin
      return Unsigned16(ReadMem8(addr)) +
        (Unsigned16(ReadMem8(addr + 1)) * (256));
   end ReadMem16;

   -- See note for ReadMem16, but this can wrap around 3 different ways
   function ReadMem32(addr: in Unsigned64) return Unsigned32
   is
   begin
      return Unsigned32(ReadMem16(addr)) +
        (Unsigned32(ReadMem16(addr + 2)) * (2**16));
   end ReadMem32;

   -- Saves a 32-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-3
   procedure WriteMem32(addr : in Unsigned64; Val : in Unsigned32)
   is
   begin
      Memory(addr) := Unsigned8(Val rem 256);
      Memory(addr + 1) := Unsigned8((Val / (256)) rem 256);
      Memory(addr + 2) := Unsigned8((Val / (2**16)) rem 256);
      Memory(addr + 3) := Unsigned8((Val / (2**24)) rem 256);
   end WriteMem32;

   -- See note for ReadMem32
   function ReadMem64(addr: in Unsigned64) return Unsigned64
   is
   begin
      return Unsigned64(ReadMem32(addr)) +
        (Unsigned64(ReadMem32(addr + 4)) * (2**32));
   end ReadMem64;

   -- Saves a 64-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-7
   procedure WriteMem64(addr : in Unsigned64; Val : in Unsigned64)
   is
   begin
      Memory(addr) := Unsigned8(Val rem 256);
      Memory(addr + 1) := Unsigned8((Val / (256)) rem 256);
      Memory(addr + 2) := Unsigned8((Val / (2**16)) rem 256);
      Memory(addr + 3) := Unsigned8((Val / (2**24)) rem 256);
      Memory(addr + 4) := Unsigned8((Val / (2**32)) rem 256);
      Memory(addr + 5) := Unsigned8((Val / (2**40)) rem 256);
      Memory(addr + 6) := Unsigned8((Val / (2**48)) rem 256);
      Memory(addr + 7) := Unsigned8((Val / (2**56)) rem 256);
   end WriteMem64;

   -----------------------------------------------------------------------
   --                       Comparison functions                        --
   -----------------------------------------------------------------------

   function SignedLT_32(Val1, Val2 : in Unsigned32) return boolean
   is
   begin
     return ((Unsigned64(Val1) + Unsigned64(Val2)) >
               Unsigned64(Val1 + Val2));
   end SignedLT_32;

   function SignedLTE_32(Val1, Val2 : in Unsigned32) return boolean
   is
   begin
      return ((Val1 = Val2) or SignedLT_32(Val1, Val2));
   end SignedLTE_32;

   -----------------------------------------------------------------------
   --                         Semi-complex X86                          --
   -----------------------------------------------------------------------

   -- repe32 uses ESI and EDI as the location of memory addresses to compare
   -- and ECX as the counter
   procedure repe32_cmpsb
   is
      Val1, Val2: Unsigned8;
   begin
      repe_loop:
      while (ECX > 0) loop
         pragma Assert (ECX /= 0);
         -- TODO: when logic is added to deal with interrupts, that code should
         -- be added here
         Val1 := ReadMem8(Unsigned64(ESI));
         Val2 := ReadMem8(Unsigned64(EDI));
         ZeroFlag := ((Val1 - Val2) = 0);
         CarryFlag := (Unsigned16(Val1) + Unsigned16(Val2) >
                      Unsigned16(Val1 + Val2));
         Write_ECX(ECX - 1);
         exit repe_loop when ((ECX = 0) or (not ZeroFlag));
         Write_ESI(ESI + 1);
         Write_EDI(EDI + 1);
      end loop repe_loop;
--        pragma Assert ((ECX = 0) or (not ZeroFlag));
   end repe32_cmpsb;

   -- repe64 uses RSI and RDI as the location of memory addresses to compare
   -- and RCX as the counter
   procedure repe64_cmpsb
   is
      Val1, Val2: Unsigned8;
   begin
      repe_loop:
      while (RCX > 0) loop
         pragma Assert (RCX /= 0);
         -- TODO: when logic is added to deal with interrupts, that code should
         -- be added here
         Val1 := ReadMem8(RSI);
         Val2 := ReadMem8(RDI);
         ZeroFlag := ((Val1 - Val2) = 0);
         CarryFlag := (Unsigned16(Val1) + Unsigned16(Val2) >
                      Unsigned16(Val1 + Val2));
         RCX := RCX - 1;
         exit repe_loop when ((RCX = 0) or (not ZeroFlag));
         RSI := RSI + 1;
         RDI := RDI + 1;
      end loop repe_loop;
--        pragma Assert ((RCX = 0) or (not ZeroFlag));
   end repe64_cmpsb;

   procedure setb_DL
   is
   begin
      if (CarryFlag) then
         Write_DL(1);
      else
         Write_DL(0);
      end if;
   end setb_DL;

   procedure setnbe_CL
   is
   begin
      if ((not CarryFlag) and (not ZeroFlag)) then
         Write_CL(1);
      else
         Write_CL(0);
      end if;
   end setnbe_CL;
end X86;

