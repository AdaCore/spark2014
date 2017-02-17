with Interfaces;
use Interfaces;

package X86
  with SPARK_Mode
is
   subtype Unsigned64 is Interfaces.Unsigned_64;
   subtype Unsigned32 is Interfaces.Unsigned_32;
   subtype Unsigned16 is Interfaces.Unsigned_16;
   subtype Unsigned8  is Interfaces.Unsigned_8;

   -- This array models 2**64 8-bit elements of memory
   type Mem_Array is array (Unsigned64) of Unsigned8;

   subtype Count8 is Natural range 0..7;

   MaxSignedInt8:  constant Unsigned8  := 16#7f#;
   MaxSignedInt16: constant Unsigned16 := 16#7fff#;
   MaxSignedInt32: constant Unsigned32 := 16#7fffffff#;
   MaxSignedInt64: constant Unsigned64 := 16#7fffffffffffffff#;

   DS               : Unsigned64 := 0;
   ES               : Unsigned64 := 0;
   FS               : Unsigned64 := 0;
   GS               : Unsigned64 := 0;
   StackAddressSize : Unsigned16 := 8; -- Default to 64-bit mode

   Exit_Called      : Boolean     := False;

   ZeroFlag         : Boolean     := false;
   CarryFlag        : Boolean     := false;
   SignFlag         : Boolean     := false;
   OverflowFlag     : Boolean     := false;

   procedure CallExit with
     Global => (Output => Exit_Called),
     Post => (Exit_Called);

   -----------------------------------------------------------------------
   --              Definition of AL, AH, AX, EAX, and RAX               --
   -----------------------------------------------------------------------

   RAX : Unsigned64 := 0;

   function AL return Unsigned8 with
     Global => (Input => RAX),
     Post => (AL'Result = Unsigned8(RAX and 16#00000000000000FF#));

   procedure Write_AL(Val : in Unsigned8) with
     Global => (In_Out => RAX),
     Post => (RAX = ((RAX'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   function AH return Unsigned8 with
     Global => (Input => RAX),
     Post => (AH'Result = Unsigned8'Mod((RAX and 16#000000000000FF00#) / 256));

   procedure Write_AH(Val : in Unsigned8) with
     Global => (In_Out => RAX),
     Post => (RAX = ((RAX'Old and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256)));

   -- Returns the Value of bits 1-16 from RAX
   function AX return Unsigned16 with
     Global => (Input => RAX),
     Post => (AX'Result = Unsigned16(RAX and 16#000000000000FFFF#));

   procedure Write_AX(Val : in Unsigned16) with
     Global => (In_Out => RAX),
     Post => (RAX = ((RAX'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EAX return Unsigned32 with
     Global => (Input => RAX),
     Post   => (EAX'Result = Unsigned32(RAX and 16#00000000FFFFFFFF#));

   procedure Write_EAX(Val : in Unsigned32) with
     Global => (In_Out => RAX),
     Post   => (RAX = ((RAX'Old and 16#FFFFFFFF00000000#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --              Definition of CL, CH, CX, ECX, and RCX               --
   -----------------------------------------------------------------------

   RCX : Unsigned64 := 0;

   function CL return Unsigned8 with
     Global => (Input => RCX),
     Post => (CL'Result = Unsigned8(RCX and 16#00000000000000FF#));

   procedure Write_CL(Val : in Unsigned8) with
     Global => (In_Out => RCX),
     Post => (RCX = ((RCX'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   function CH return Unsigned8 with
     Global => (Input => RCX),
     Post => (CH'Result = Unsigned8'Mod((RCX and 16#000000000000FF00#) / 256));

   procedure Write_CH(Val : in Unsigned8) with
     Global => (In_Out => RCX),
     Post => (RCX = ((RCX'Old and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256)));

   -- Returns the Value of bits 1-16 from RCX
   function CX return Unsigned16 with
     Global => (Input => RCX),
     Post => (CX'Result = Unsigned16(RCX and 16#000000000000FFFF#));

   procedure Write_CX(Val : in Unsigned16) with
     Global => (In_Out => RCX),
     Post => (RCX = ((RCX'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function ECX return Unsigned32 with
     Global => (Input => RCX),
     Post   => (ECX'Result = Unsigned32(RCX and 16#00000000FFFFFFFF#));

   procedure Write_ECX(Val : in Unsigned32) with
     Global => (In_Out => RCX),
     Post   => (RCX = ((RCX'Old and 16#FFFFFFFF00000000#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --              Definition of DL, DH, DX, EDX, and RDX               --
   -----------------------------------------------------------------------

   RDX : Unsigned64 := 0;

   function DL return Unsigned8 with
     Global => (Input => RDX),
     Post => (DL'Result = Unsigned8(RDX and 16#00000000000000FF#));

   procedure Write_DL(Val : in Unsigned8) with
     Global => (In_Out => RDX),
     Post => (RDX = ((RDX'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   function DH return Unsigned8 with
     Global => (Input => RDX),
     Post => (DH'Result = Unsigned8'Mod((RDX and 16#000000000000FF00#) / 256));

   procedure Write_DH(Val : in Unsigned8) with
     Global => (In_Out => RDX),
     Post => (RDX = ((RDX'Old and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256)));

   -- Returns the Value of bits 1-16 from RDX
   function DX return Unsigned16 with
     Global => (Input => RDX),
     Post => (DX'Result = Unsigned16(RDX and 16#000000000000FFFF#));

   procedure Write_DX(Val : in Unsigned16) with
     Global => (In_Out => RDX),
     Post => (RDX = ((RDX'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EDX return Unsigned32 with
     Global => (Input => RDX),
     Post   => (EDX'Result = Unsigned32(RDX and 16#00000000FFFFFFFF#));

   procedure Write_EDX(Val : in Unsigned32) with
     Global => (In_Out => RDX),
     Post   => (RDX = ((RDX'Old and 16#FFFFFFFF00000000#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --              Definition of BL, BH, BX, EBX, and RBX               --
   -----------------------------------------------------------------------

   RBX : Unsigned64 := 0;

   function BL return Unsigned8 with
     Global => (Input => RBX),
     Post => (BL'Result = Unsigned8(RBX and 16#00000000000000FF#));

   procedure Write_BL(Val : in Unsigned8) with
     Global => (In_Out => RBX),
     Post => (RBX = ((RBX'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   function BH return Unsigned8 with
     Global => (Input => RBX),
     Post => (BH'Result = Unsigned8'Mod((RBX and 16#000000000000FF00#) / 256));

   procedure Write_BH(Val : in Unsigned8) with
     Global => (In_Out => RBX),
     Post => (RBX = ((RBX'Old and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256)));

   -- Returns the Value of bits 1-16 from RBX
   function BX return Unsigned16 with
     Global => (Input => RBX),
     Post => (BX'Result = Unsigned16(RBX and 16#000000000000FFFF#));

   procedure Write_BX(Val : in Unsigned16) with
     Global => (In_Out => RBX),
     Post => (RBX = ((RBX'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EBX return Unsigned32 with
     Global => (Input => RBX),
     Post   => (EBX'Result = Unsigned32(RBX and 16#00000000FFFFFFFF#));

   procedure Write_EBX(Val : in Unsigned32) with
     Global => (In_Out => RBX),
     Post   => (RBX = ((RBX'Old and 16#FFFFFFFF00000000#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of SP, ESP, and RSP                   --
   -----------------------------------------------------------------------

   RSP : Unsigned64 := 0;

   -- Returns the Value of bits 1-16 from RSP
   function SP return Unsigned16 with
     Global => (Input => RSP),
     Post => (SP'Result = Unsigned16(RSP and 16#000000000000FFFF#));

   procedure Write_SP(Val : in Unsigned16) with
     Global => (In_Out => RSP),
     Post => (RSP = ((RSP'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function ESP return Unsigned32 with
     Global => (Input => RSP),
     Post   => (ESP'Result = Unsigned32(RSP and 16#00000000FFFFFFFF#));

   procedure Write_ESP(Val : in Unsigned32) with
     Global => (In_Out => RSP),
     Post   => (RSP = ((RSP'Old and 16#FFFFFFFF00000000#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of BP, EBP, and RBP                   --
   -----------------------------------------------------------------------

   RBP : Unsigned64 := 0;

   -- Returns the Value of bits 1-16 from RBP
   function BP return Unsigned16 with
     Global => (Input => RBP),
     Post => (BP'Result = Unsigned16(RBP and 16#000000000000FFFF#));

   procedure Write_BP(Val : in Unsigned16) with
     Global => (In_Out => RBP),
     Post => (RBP = ((RBP'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EBP return Unsigned32 with
     Global => (Input => RBP),
     Post   => (EBP'Result = Unsigned32(RBP and 16#00000000FFFFFFFF#));

   procedure Write_EBP(Val : in Unsigned32) with
     Global => (In_Out => RBP),
     Post   => (RBP = ((RBP'Old and 16#FFFFFFFF00000000#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of SI, ESI, and RSI                   --
   -----------------------------------------------------------------------

   RSI : Unsigned64 := 0;

   -- Returns the Value of bits 1-16 from RSI
   function SI return Unsigned16 with
     Global => (Input => RSI),
     Post => (SI'Result = Unsigned16(RSI and 16#000000000000FFFF#));

   procedure Write_SI(Val : in Unsigned16) with
     Global => (In_Out => RSI),
     Post => (RSI = ((RSI'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function ESI return Unsigned32 with
     Global => (Input => RSI),
     Post   => (ESI'Result = Unsigned32(RSI and 16#00000000FFFFFFFF#));

   procedure Write_ESI(Val : in Unsigned32) with
     Global => (In_Out => RSI),
     Post   => (RSI = ((RSI'Old and 16#FFFFFFFF00000000#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of DI, EDI, and RDI                   --
   -----------------------------------------------------------------------

   RDI : Unsigned64 := 0;

   -- Returns the Value of bits 1-16 from RDI
   function DI return Unsigned16 with
     Global => (Input => RDI),
     Post => (DI'Result = Unsigned16(RDI and 16#000000000000FFFF#));

   procedure Write_DI(Val : in Unsigned16) with
     Global => (In_Out => RDI),
     Post => (RDI = ((RDI'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EDI return Unsigned32 with
     Global => (Input => RDI),
     Post   => (EDI'Result = Unsigned32(RDI and 16#00000000FFFFFFFF#));

   procedure Write_EDI(Val : in Unsigned32) with
     Global => (In_Out => RDI),
     Post   => (RDI = ((RDI'Old and 16#FFFFFFFF00000000#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of R8 and R8L                         --
   -----------------------------------------------------------------------

   R8 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R8
   function R8L return Unsigned8 with
     Global => (Input => R8),
     Post => (R8L'Result = Unsigned8(R8 and 16#00000000000000FF#));

   procedure Write_R8L(Val : in Unsigned8) with
     Global => (In_Out => R8),
     Post => (R8 = ((R8'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of R9 and R9L                         --
   -----------------------------------------------------------------------

   R9 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R9
   function R9L return Unsigned8 with
     Global => (Input => R9),
     Post => (R9L'Result = Unsigned8(R9 and 16#00000000000000FF#));

   procedure Write_R9L(Val : in Unsigned8) with
     Global => (In_Out => R9),
     Post => (R9 = ((R9'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of R10 and R10L                         --
   -----------------------------------------------------------------------

   R10 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R10
   function R10L return Unsigned8 with
     Global => (Input => R10),
     Post => (R10L'Result = Unsigned8(R10 and 16#00000000000000FF#));

   procedure Write_R10L(Val : in Unsigned8) with
     Global => (In_Out => R10),
     Post => (R10 = ((R10'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of R11 and R11L                         --
   -----------------------------------------------------------------------

   R11 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R11
   function R11L return Unsigned8 with
     Global => (Input => R11),
     Post => (R11L'Result = Unsigned8(R11 and 16#00000000000000FF#));

   procedure Write_R11L(Val : in Unsigned8) with
     Global => (In_Out => R11),
     Post => (R11 = ((R11'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of R12 and R12L                         --
   -----------------------------------------------------------------------

   R12 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R12
   function R12L return Unsigned8 with
     Global => (Input => R12),
     Post => (R12L'Result = Unsigned8(R12 and 16#00000000000000FF#));

   procedure Write_R12L(Val : in Unsigned8) with
     Global => (In_Out => R12),
     Post => (R12 = ((R12'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of R13 and R13L                         --
   -----------------------------------------------------------------------

   R13 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R13
   function R13L return Unsigned8 with
     Global => (Input => R13),
     Post => (R13L'Result = Unsigned8(R13 and 16#00000000000000FF#));

   procedure Write_R13L(Val : in Unsigned8) with
     Global => (In_Out => R13),
     Post => (R13 = ((R13'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of R14 and R14L                         --
   -----------------------------------------------------------------------

   R14 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R14
   function R14L return Unsigned8 with
     Global => (Input => R14),
     Post => (R14L'Result = Unsigned8(R14 and 16#00000000000000FF#));

   procedure Write_R14L(Val : in Unsigned8) with
     Global => (In_Out => R14),
     Post => (R14 = ((R14'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                  Definition of R15 and R15L                         --
   -----------------------------------------------------------------------

   R15 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R15
   function R15L return Unsigned8 with
     Global => (Input => R15),
     Post => (R15L'Result = Unsigned8(R15 and 16#00000000000000FF#));

   procedure Write_R15L(Val : in Unsigned8) with
     Global => (In_Out => R15),
     Post => (R15 = ((R15'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --                         Read/Write Memory                         --
   -----------------------------------------------------------------------
   Memory           : Mem_Array   := Mem_Array'(others => 0);

   function ReadMem8(addr : in Unsigned64) return Unsigned8 with
     Global => (Input => Memory),
     Post => ((ReadMem8'Result = Memory(addr)) and (ReadMem8'Result >= 0));

   -- Note that if addr is Unsigned64'Last, this will take the last byte in
   -- Memory as the "low" byte and the first byte in Memory as the "high" byte
   function ReadMem16(addr: in Unsigned64) return Unsigned16 with
     Global => (Input => Memory),
     Post => ((ReadMem16'Result = Unsigned16(Memory(addr)) +
              (Unsigned16(Memory(addr + 1)) * (256))) and
                (ReadMem16'Result >= 0));

   -- See note for ReadMem16, but this can wrap around 3 different ways
   function ReadMem32(addr: in Unsigned64) return Unsigned32 with
     Global => (Input => Memory),
     Post => ((ReadMem32'Result = Unsigned32(ReadMem16(addr)) +
              (Unsigned32(ReadMem16(addr + 2)) * (2**16))) and
                (ReadMem32'Result >= 0));

   -- Saves a 32-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-3
   procedure WriteMem32(addr : in Unsigned64; Val : in Unsigned32) with
     Global => (In_Out => Memory),
     Post => (((Unsigned32(Memory(addr)) +
              (Unsigned32(Memory(addr + 1)) * (256)) +
              (Unsigned32(Memory(addr + 2)) * (2**16)) +
              (Unsigned32(Memory(addr + 3)) * (2**24))) = Val) and
                (for all i in Unsigned64 =>
                     (if ((i /= addr) and (i /= addr + 1) and
                          (i /= addr + 2) and (i /= addr + 3)) then
                          (Memory(i) = Memory'Old(i)))));

   -- See note for ReadMem32
   function ReadMem64(addr: in Unsigned64) return Unsigned64 with
     Global => (Input => Memory),
     Post => ((ReadMem64'Result = Unsigned64(ReadMem32(addr)) +
              (Unsigned64(ReadMem32(addr + 4)) * (2**32))) and
                (ReadMem64'Result >= 0));

   -- Saves a 64-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-7
   procedure WriteMem64(addr : in Unsigned64; Val : in Unsigned64) with
     Global => (In_Out => Memory),
     Post => (((Unsigned64(Memory(addr)) +
              (Unsigned64(Memory(addr + 1)) * (256)) +
              (Unsigned64(Memory(addr + 2)) * (2**16)) +
              (Unsigned64(Memory(addr + 3)) * (2**24)) +
              (Unsigned64(Memory(addr + 4)) * (2**32)) +
              (Unsigned64(Memory(addr + 5)) * (2**40)) +
              (Unsigned64(Memory(addr + 6)) * (2**48)) +
              (Unsigned64(Memory(addr + 7)) * (2**56))) = Val) and
                (for all i in Unsigned64 =>
                     (if ((i /= addr) and (i /= addr + 1) and
                            (i /= addr + 2) and (i /= addr + 3) and
                            (i /= addr + 4) and (i /= addr + 5) and
                            (i /= addr + 6) and (i /= addr + 7)) then
                          (Memory(i) = Memory'Old(i)))));

   -----------------------------------------------------------------------
   --                       Comparison functions                        --
   -----------------------------------------------------------------------

   function SignedLT_32(Val1, Val2 : in Unsigned32) return boolean with
     Post => (SignedLT_32'Result = ((Unsigned64(Val1) + Unsigned64(Val2)) >
                  Unsigned64(Val1 + Val2)));

   function SignedLTE_32(Val1, Val2 : in Unsigned32) return boolean with
     Post => (SignedLTE_32'Result = ((Val1 = Val2) or SignedLT_32(Val1, Val2)));

   -----------------------------------------------------------------------
   --                         Semi-complex X86                          --
   -----------------------------------------------------------------------

   procedure repe32_cmpsb with
     Global => (In_Out => (RSI, RDI, RCX, ZeroFlag, CarryFlag),
                Input  => Memory),
     Post => true; --((ECX = 0) or (not ZeroFlag));
   -- TODO figure out stronger post condition

   procedure repe64_cmpsb with
     Global => (In_Out => (RSI, RDI, RCX, ZeroFlag, CarryFlag),
                Input  => Memory),
     Post => true; --((RCX = 0) or (not ZeroFlag));
   -- TODO figure out stronger post condition

   ----------------------------------------------------------------------
   --   setb, setnbe                                                   --
   ----------------------------------------------------------------------

   procedure setb_DL with
     Global => (Input => CarryFlag, In_Out => RDX),
     Post => ((if (CarryFlag) then (DL = 1)) and
                (if (not CarryFlag) then (DL = 0)));

   procedure setnbe_CL with
     Global => (Input => (ZeroFlag, CarryFlag), In_Out => RCX),
     Post => ((if ((not CarryFlag) and (not ZeroFlag)) then (CL = 1)) and
                (if (CarryFlag or ZeroFlag) then (CL = 0)));

end X86;



