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

   MaxSignedInt8  :  constant Unsigned8 := 16#7f#;
   MaxSignedInt16 : constant Unsigned16 := 16#7fff#;
   MaxSignedInt32 : constant Unsigned32 := 16#7fffffff#;
   MaxSignedInt64 : constant Unsigned64 := 16#7fffffffffffffff#;

   --Highest permissible stack index
   StackBottom : constant Unsigned64 := 16#CFFFFFFFFFFFFFFF#;
   --Lowest permissible stack index
   StackTop    : constant Unsigned64 := 16#7FFFFFFFFFFFFFFF#;

   DummyRSP : constant Unsigned64 := StackTop + (StackBottom - StackTop)/2;


   --Highest permissiable non-stack storage address
   MiscStorageHigh : constant Unsigned64 := StackTop/2;
   --Lowest permissible non-stack storage address
   MiscStorageLow  : constant Unsigned64 := 0;

   DummyStorage : constant Unsigned64 := MiscStorageHigh/2;


   DS		             : Unsigned64 := 0;
   ES		             : Unsigned64 := 0;
   FS		             : Unsigned64 := 0;
   GS		             : Unsigned64 := 0;
   SS : Unsigned64 :=0;
   StackAddressSize  : Unsigned16 := 8; -- Default to 64-bit mode

   Exit_Called	     : Boolean	  := False;

   ZeroFlag	     : Boolean	  := false;
   CarryFlag	     : Boolean	  := false;
   SignFlag	     : Boolean	  := false;
   OverflowFlag      : Boolean	  := false;

   -- This function is only to be used to mask possible division by zero
   -- Do not use this function in code where the goal is to prove an absence of
   -- divide-by-zero errors
   function SafeDivision64(dividend: in Unsigned64; divisor: in Unsigned64)
                           return Unsigned64 with
     Post => (SafeDivision64'Result = dividend/divisor);

   -----------------------------------------------------------------------
   -- InRange64 is designed to handle wrapping of Unsigned64 integers
   -- To test to see if val is between x and x+3, you would invoke
   -- InRange64(val, x, 4) which would check to see if val = x, x+1, x+2, or x+3
   -- This works even for the case where x = 2^64-1 and x+1 = 0.
   function InRange64(var: in Unsigned64; bottom: in Unsigned64; range_size: Unsigned64)
                     return Boolean with Ghost,
     -- The following post-condition, while easier for humans to understand is harder for the
     -- prover to use. It can be proven to be identical, however.
--     Post => (InRange64'Result =
--                (for some N in Unsigned64 range 0 .. range_size - 1 => (var = (bottom + N))));
       Post => InRange64'Result = (if (Bottom <= Unsigned64'Last - Range_Size + 1) then
           (Bottom <= Var and Var <= Bottom + (Range_Size - 1))
         else
           (Bottom <= Var and Var <= Unsigned64'Last) or
             (Var <= Range_Size - (Unsigned64'Last - Bottom) - 2));

   function InMemoryRange(Var: in Unsigned64; Lower: in Unsigned64; Upper: Unsigned64)
                          return Boolean with Ghost,
     Post => InMemoryRange'Result = (if (Lower < Upper) then
                                      (Lower <= Var and Var < Upper)
                                     else
                                      (Lower <= Var or Var < Upper));
   -----------------------------------------------------------------------

   function RangesIntersect(var1: in Unsigned64; var1_range_size: in Unsigned64; var2: in Unsigned64; var2_range_size: in Unsigned64)
                                 return Boolean with Ghost,
     Pre => var1_range_size < Unsigned64'Last - var2_range_size,
     Post => RangesIntersect'Result = (InRange64(var1,var2-(var1_range_size-1), (var1_range_size-1)+var2_range_size));

   function InSafeRegion64(var: in Unsigned64; rsp: in Unsigned64)
                             return Boolean with Ghost,
     Post => InSafeRegion64'Result = ((var <= X86.StackBottom and var >= rsp + 8) or (var <= X86.MiscStorageHigh and var >= X86.MiscStorageLow));

   procedure CallExit with
     Global => (Output => Exit_Called),
     Post => (Exit_Called);


   XMM0 :  Unsigned64 := 0;
   XMM1 :  Unsigned64 := 0;
   XMM2 :  Unsigned64 := 0;
   XMM3 :  Unsigned64 := 0;
   XMM4 :  Unsigned64 := 0;
   XMM5 :  Unsigned64 := 0;
   XMM6 :  Unsigned64 := 0;
   XMM7 :  Unsigned64 := 0;


   function readRegLow8 (Reg : in Unsigned64) return Unsigned8 with
     Post => (readRegLow8'Result = Unsigned8(Reg and 16#00000000000000FF#));

   procedure writeRegLow8 (Reg : in out Unsigned64; Val : in Unsigned8) with
     Post => (writeRegLow8Post(Reg'Old, Reg, Val));

   function writeRegLow8Post(RegOld : in Unsigned64; RegNew: in Unsigned64; Val : in Unsigned8)
                             return Boolean with Ghost,
     Post => writeRegLow8Post'Result = ((readRegLow8(RegNew) = Val) and
                  ((RegNew and 16#FFFFFFFFFFFFFF00#) = (RegOld and 16#FFFFFFFFFFFFFF00#)));

   function readRegHigh8 (Reg : in Unsigned64) return Unsigned8 with
     Post => (readRegHigh8'Result = Unsigned8'Mod((Reg and 16#000000000000FF00#) / 256));

   procedure writeRegHigh8(Reg : in out Unsigned64; Val : in Unsigned8) with
    Post => (writeRegHigh8Post(Reg'Old, Reg, Val));

   function writeRegHigh8Post(RegOld : in Unsigned64; RegNew: in Unsigned64; Val : in Unsigned8)
                             return Boolean with Ghost,
     Post => writeRegHigh8Post'Result = ((readRegHigh8(RegNew) = Val) and
                                           ((RegNew and 16#FFFFFFFFFFFF00FF#) = (RegOld and 16#FFFFFFFFFFFF00FF#)));

   function readReg16 (Reg : in Unsigned64) return Unsigned16 with
     Post => (readReg16'Result = Unsigned16(Reg and 16#000000000000FFFF#));

   procedure writeReg16 (Reg : in out Unsigned64; Val : in Unsigned16) with
     Post => (writeReg16Post(Reg'Old, Reg, Val));

   function writeReg16Post(RegOld : in Unsigned64; RegNew: in Unsigned64; Val : in Unsigned16)
                           return Boolean with Ghost,
     Post => writeReg16Post'Result = ((readReg16(RegNew) = Val) and
                                        ((RegNew and 16#FFFFFFFFFFFF0000#) = (RegOld and 16#FFFFFFFFFFFF0000#)));

   function readReg32 (Reg : in Unsigned64) return Unsigned32 with
     Post   => (readReg32'Result = Unsigned32(Reg and 16#00000000FFFFFFFF#));

   procedure writeReg32(Reg : in out Unsigned64; Val : in Unsigned32) with
     Post => (writeReg32Post(Reg,Val));

   function writeReg32Post(RegNew: in Unsigned64; Val : in Unsigned32)
                           return Boolean with Ghost,
     Post => writeReg32Post'Result = ((readReg32(RegNew) = Val) and ((RegNew and 16#FFFFFFFF00000000#) = (16#0000000000000000#)));

   -----------------------------------------------------------------------
   --		   Definition of AL, AH, AX, EAX, and RAX		--
   -----------------------------------------------------------------------

   RAX : Unsigned64 := 0;

   function AL return Unsigned8 with
     Global => (Input => RAX),
     Post => (AL'Result = readRegLow8(RAX));
     --Post => (AL'Result = Unsigned8(RAX and 16#00000000000000FF#));

   procedure Write_AL(Val : in Unsigned8) with
     Global => (In_Out => RAX),
     Post => (writeRegLow8Post(RAX'Old, RAX, Val));
     --Post => ((AL = Val) and ((RAX and 16#FFFFFFFFFFFFFF00#) = (RAX'Old and 16#FFFFFFFFFFFFFF00#)));

   function AH return Unsigned8 with
       Global => (Input => RAX),
     Post => (AH'Result = readRegHigh8(RAX));
     --Post => (AH'Result = Unsigned8'Mod((RAX and 16#000000000000FF00#) / 256));

   procedure Write_AH(Val : in Unsigned8) with
     Global => (In_Out => RAX),
     Post =>(writeRegHigh8Post(RAX'Old, RAX, Val));
     --Post => ((AH = Val) and ((RAX and 16#FFFFFFFFFFFF00FF#) = (RAX'Old and 16#FFFFFFFFFFFF00FF#)));

   -- Returns the Value of bits 1-16 from RAX
   function AX return Unsigned16 with
     Global => (Input => RAX),
     Post => (AX'Result = readReg16(RAX));
     --Post => (AX'Result = Unsigned16(RAX and 16#000000000000FFFF#));

   procedure Write_AX(Val : in Unsigned16) with
     Global => (In_Out => RAX),
     Post => (writeReg16Post(RAX'Old, RAX, Val));
     --Post => ((AX = Val) and ((RAX and 16#FFFFFFFFFFFF0000#) = (RAX'Old and 16#FFFFFFFFFFFF0000#)));

   function EAX return Unsigned32 with
     Global => (Input => RAX),
     Post   => (EAX'Result = Unsigned32(RAX and 16#00000000FFFFFFFF#));

   procedure Write_EAX(Val : in Unsigned32) with
     Global => (In_Out => RAX),
     Post => (writeReg32Post(RAX, Val));
     --Post => ((EAX = Val) and ((RAX and 16#FFFFFFFF00000000#) = (16#0000000000000000#)));

   -----------------------------------------------------------------------
   --		   Definition of CL, CH, CX, ECX, and RCX		--
   -----------------------------------------------------------------------

   RCX : Unsigned64 := 0;

   function CL return Unsigned8 with
     Global => (Input => RCX),
     Post => (CL'Result = readRegLow8(RCX));
     --Post => (CL'Result = Unsigned8(RCX and 16#00000000000000FF#));

   procedure Write_CL(Val : in Unsigned8) with
     Global => (In_Out => RCX),
     Post => (writeRegLow8Post(RCX'Old, RCX, Val));
     --Post => (RCX = ((RCX'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   function CH return Unsigned8 with
     Global => (Input => RCX),
     Post => (CH'Result = readRegHigh8(RCX));
     --Post => (CH'Result = Unsigned8'Mod((RCX and 16#000000000000FF00#) / 256));

   procedure Write_CH(Val : in Unsigned8) with
     Global => (In_Out => RCX),
     Post => (writeRegHigh8Post(RCX'Old,RCX,Val));
     --Post => ((CH = Val) and ((RCX and 16#FFFFFFFFFFFF00FF#) = (RCX'Old and 16#FFFFFFFFFFFF00FF#)));

   -- Returns the Value of bits 1-16 from RCX
   function CX return Unsigned16 with
     Global => (Input => RCX),
     Post => (CX'Result = readReg16(RCX));
     --Post => (CX'Result = Unsigned16(RCX and 16#000000000000FFFF#));

   procedure Write_CX(Val : in Unsigned16) with
     Global => (In_Out => RCX),
     Post => (writeReg16Post(RCX'Old, RCX, Val));
     --Post => (RCX = ((RCX'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function ECX return Unsigned32 with
     Global => (Input => RCX),
     Post => (ECX'Result = readReg32(RCX));
     --Post   => (ECX'Result = Unsigned32(RCX and 16#00000000FFFFFFFF#));

   procedure Write_ECX(Val : in Unsigned32) with
     Global => (In_Out => RCX),
     Post => (writeReg32Post(RCX, Val));
     --Post   => ((ECX = Val) and ((RCX and 16#FFFFFFFF00000000#) = 16#0000000000000000#));

   -----------------------------------------------------------------------
   --		   Definition of DL, DH, DX, EDX, and RDX		--
   -----------------------------------------------------------------------

   RDX : Unsigned64 := 0;

   function DL return Unsigned8 with
     Global => (Input => RDX),
     Post => (DL'Result = readRegLow8(RDX));
     --Post => (DL'Result = Unsigned8(RDX and 16#00000000000000FF#));

   procedure Write_DL(Val : in Unsigned8) with
     Global => (In_Out => RDX),
     Post => (writeRegLow8Post(RDX'Old, RDX, Val));
     --Post => (RDX = ((RDX'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   function DH return Unsigned8 with
     Global => (Input => RDX),
     Post => (DH'Result = readRegHigh8(RDX));
     --Post => (DH'Result = Unsigned8'Mod((RDX and 16#000000000000FF00#) / 256));

   procedure Write_DH(Val : in Unsigned8) with
     Global => (In_Out => RDX),
     Post => (writeRegHigh8Post(RDX'Old, RDX, Val));
     --Post => ((DH = Val) and ((RDX and 16#FFFFFFFFFFFF00FF#) = (RDX'Old and 16#FFFFFFFFFFFF00FF#)));

   -- Returns the Value of bits 1-16 from RDX
   function DX return Unsigned16 with
     Global => (Input => RDX),
     Post => (DX'Result = readReg16(RDX));
     --Post => (DX'Result = Unsigned16(RDX and 16#000000000000FFFF#));

   procedure Write_DX(Val : in Unsigned16) with
     Global => (In_Out => RDX),
     Post => (writeReg16Post(RDX'Old, RDX, Val));
     --Post => (RDX = ((RDX'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EDX return Unsigned32 with
     Global => (Input => RDX),
     Post => (EDX'Result = readReg32(RDX));
     --Post   => (EDX'Result = Unsigned32(RDX and 16#00000000FFFFFFFF#));

   procedure Write_EDX(Val : in Unsigned32) with
     Global => (In_Out => RDX),
     Post => (writeReg32Post(RDX, Val));
     --Post   => ((EDX = Val) and ((RDX and 16#FFFFFFFF00000000#) = 16#0000000000000000#));

   -----------------------------------------------------------------------
   --		   Definition of BL, BH, BX, EBX, and RBX		--
   -----------------------------------------------------------------------

   RBX : Unsigned64 := 0;

   function BL return Unsigned8 with
     Global => (Input => RBX),
     Post => (BL'Result = readRegLow8(RBX));
     --Post => (BL'Result = Unsigned8(RBX and 16#00000000000000FF#));

   procedure Write_BL(Val : in Unsigned8) with
     Global => (In_Out => RBX),
     Post => (writeRegLow8Post(RBX'Old, RBX, Val));
     --Post => (RBX = ((RBX'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   function BH return Unsigned8 with
     Global => (Input => RBX),
     Post => (BH'Result = readRegHigh8(RBX));
     --Post => (BH'Result = Unsigned8'Mod((RBX and 16#000000000000FF00#) / 256));

   procedure Write_BH(Val : in Unsigned8) with
     Global => (In_Out => RBX),
     Post => (writeRegHigh8Post(RBX'Old, RBX, Val));
     --Post => ((BH = Val) and ((RBX and 16#FFFFFFFFFFFF00FF#) = (RBX'Old and 16#FFFFFFFFFFFF00FF#)));

   -- Returns the Value of bits 1-16 from RBX
   function BX return Unsigned16 with
     Global => (Input => RBX),
     Post => (BX'Result = readReg16(RBX));
     --Post => (BX'Result = Unsigned16(RBX and 16#000000000000FFFF#));

   procedure Write_BX(Val : in Unsigned16) with
     Global => (In_Out => RBX),
     Post => (writeReg16Post(RBX'Old, RBX, Val));
     --Post => (RBX = ((RBX'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EBX return Unsigned32 with
     Global => (Input => RBX),
     Post => (EBX'Result = readReg32(RBX));
     --Post   => (EBX'Result = Unsigned32(RBX and 16#00000000FFFFFFFF#));

   procedure Write_EBX(Val : in Unsigned32) with
     Global => (In_Out => RBX),
     Post => (writeReg32Post(RBX, Val));
     --Post   => ((EBX = Val) and ((RBX and 16#FFFFFFFF00000000#) = 16#0000000000000000#));

   -----------------------------------------------------------------------
   --		       Definition of SP, ESP, and RSP			--
   -----------------------------------------------------------------------

   RSP : Unsigned64 := 0;

   -- Returns the Value of bits 1-16 from RSP
   function SP return Unsigned16 with
     Global => (Input => RSP),
     Post => (SP'Result = readreg16(RSP));
     --Post => (SP'Result = Unsigned16(RSP and 16#000000000000FFFF#));

   procedure Write_SP(Val : in Unsigned16) with
     Global => (In_Out => RSP),
     Post => (writeReg16Post(RSP'Old, RSP, Val));
     --Post => (RSP = ((RSP'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function ESP return Unsigned32 with
     Global => (Input => RSP),
     Post => (ESP'Result = readReg32(RSP));
     --Post   => (ESP'Result = Unsigned32(RSP and 16#00000000FFFFFFFF#));

   procedure Write_ESP(Val : in Unsigned32) with
     Global => (In_Out => RSP),
     Post => (writeReg32Post(RSP, Val));
     --Post   => ((ESP = Val) and ((RSP and 16#FFFFFFFF00000000#) = 16#0000000000000000#));

   -----------------------------------------------------------------------
   --		       Definition of BP, EBP, and RBP			--
   -----------------------------------------------------------------------

   RBP : Unsigned64 := 0;

   -- Returns the Value of bits 1-16 from RBP
   function BP return Unsigned16 with
     Global => (Input => RBP),
     Post => (BP'Result = readReg16(RBP));
     --Post => (BP'Result = Unsigned16(RBP and 16#000000000000FFFF#));

   procedure Write_BP(Val : in Unsigned16) with
     Global => (In_Out => RBP),
     Post => (writeReg16Post(RBP'Old, RBP, Val));
     --Post => (RBP = ((RBP'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EBP return Unsigned32 with
     Global => (Input => RBP),
     Post => (EBP'Result = readReg32(RBP));
     --Post   => (EBP'Result = Unsigned32(RBP and 16#00000000FFFFFFFF#));

   procedure Write_EBP(Val : in Unsigned32) with
     Global => (In_Out => RBP),
     Post => (writeReg32Post(RBP, Val));
     --Post   => ((EBP = Val) and ((RBP and 16#FFFFFFFF00000000#) = 16#0000000000000000#));

   -----------------------------------------------------------------------
   --		       Definition of SI, ESI, and RSI			--
   -----------------------------------------------------------------------

   RSI : Unsigned64 := 0;

   -- Returns the Value of bits 1-16 from RSI
   function SI return Unsigned16 with
     Global => (Input => RSI),
     Post => (SI'Result = readReg16(RSI));
     --Post => (SI'Result = Unsigned16(RSI and 16#000000000000FFFF#));

   procedure Write_SI(Val : in Unsigned16) with
     Global => (In_Out => RSI),
     Post => (writeReg16Post(RSI'Old, RSI, Val));
     --Post => (RSI = ((RSI'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function ESI return Unsigned32 with
     Global => (Input => RSI),
     Post => (ESI'Result = readReg32(RSI));
     --Post   => (ESI'Result = Unsigned32(RSI and 16#00000000FFFFFFFF#));

   procedure Write_ESI(Val : in Unsigned32) with
     Global => (In_Out => RSI),
     Post => (writeReg32Post(RSI, Val));
     --Post   => ((ESI = Val) and ((RSI and 16#FFFFFFFF00000000#) = 16#0000000000000000#));

   -----------------------------------------------------------------------
   --		       Definition of DI, EDI, and RDI			--
   -----------------------------------------------------------------------

   RDI : Unsigned64 := 0;

   -- Returns the Value of bits 1-16 from RDI
   function DI return Unsigned16 with
     Global => (Input => RDI),
     Post => (DI'Result = readReg16(RDI));
     --Post => (DI'Result = Unsigned16(RDI and 16#000000000000FFFF#));

   procedure Write_DI(Val : in Unsigned16) with
     Global => (In_Out => RDI),
     Post => (writeReg16Post(RDI'Old, RDI, Val));
     --Post => (RDI = ((RDI'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EDI return Unsigned32 with
     Global => (Input => RDI),
     Post => (EDI'Result = readReg32(RDI));
     --Post   => (EDI'Result = Unsigned32(RDI and 16#00000000FFFFFFFF#));

   procedure Write_EDI(Val : in Unsigned32) with
     Global => (In_Out => RDI),
     Post => (writeReg32Post(RDI, Val));
     --Post   => ((EDI = Val) and ((RDI and 16#FFFFFFFF00000000#) = 16#0000000000000000#));

   -----------------------------------------------------------------------
   --		       Definition of R8 and R8L 			--
   -----------------------------------------------------------------------

   R8 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R8
   function R8L return Unsigned8 with
     Global => (Input => R8),
     Post => (R8L'Result = readRegLow8(R8));
     --Post => (R8L'Result = Unsigned8(R8 and 16#00000000000000FF#));

   procedure Write_R8L(Val : in Unsigned8) with
     Global => (In_Out => R8),
     Post => (writeRegLow8Post(R8'Old, R8, Val));
     --Post => (R8 = ((R8'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --		       Definition of R9 and R9L 			--
   -----------------------------------------------------------------------

   R9 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R9
   function R9L return Unsigned8 with
     Global => (Input => R9),
     Post => (R9L'Result = readRegLow8(R9));
     --Post => (R9L'Result = Unsigned8(R9 and 16#00000000000000FF#));

   procedure Write_R9L(Val : in Unsigned8) with
     Global => (In_Out => R9),
     Post => (writeRegLow8Post(R9'Old, R9, Val));
     --Post => (R9 = ((R9'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --		       Definition of R10 and R10L			  --
   -----------------------------------------------------------------------

   R10 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R10
   function R10L return Unsigned8 with
     Global => (Input => R10),
     Post => (R10L'Result = readRegLow8(R10));
     --Post => (R10L'Result = Unsigned8(R10 and 16#00000000000000FF#));

   procedure Write_R10L(Val : in Unsigned8) with
     Global => (In_Out => R10),
     Post => (writeRegLow8Post(R10'Old, R10, Val));
     --Post => (R10 = ((R10'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --		       Definition of R11 and R11L			  --
   -----------------------------------------------------------------------

   R11 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R11
   function R11L return Unsigned8 with
     Global => (Input => R11),
     Post => (R11L'Result = readRegLow8(R11));
     --Post => (R11L'Result = Unsigned8(R11 and 16#00000000000000FF#));

   procedure Write_R11L(Val : in Unsigned8) with
     Global => (In_Out => R11),
     Post => (writeRegLow8Post(R11'Old, R11, Val));
     --Post => (R11 = ((R11'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --		       Definition of R12 and R12L			  --
   -----------------------------------------------------------------------

   R12 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R12
   function R12L return Unsigned8 with
     Global => (Input => R12),
     Post => (R12L'Result = readRegLow8(R12));
     --Post => (R12L'Result = Unsigned8(R12 and 16#00000000000000FF#));

   procedure Write_R12L(Val : in Unsigned8) with
     Global => (In_Out => R12),
     Post => (writeRegLow8Post(R12'Old, R12, Val));
     --Post => (R12 = ((R12'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --		       Definition of R13 and R13L			  --
   -----------------------------------------------------------------------

   R13 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R13
   function R13L return Unsigned8 with
     Global => (Input => R13),
     Post => (R13L'Result = readRegLow8(R13));
     --Post => (R13L'Result = Unsigned8(R13 and 16#00000000000000FF#));

   procedure Write_R13L(Val : in Unsigned8) with
     Global => (In_Out => R13),
     Post => (writeRegLow8Post(R13'Old, R13, Val));
     --Post => (R13 = ((R13'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --		       Definition of R14 and R14L			  --
   -----------------------------------------------------------------------

   R14 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R14
   function R14L return Unsigned8 with
     Global => (Input => R14),
     Post => (R14L'Result = readRegLow8(R14));
     --Post => (R14L'Result = Unsigned8(R14 and 16#00000000000000FF#));

   procedure Write_R14L(Val : in Unsigned8) with
     Global => (In_Out => R14),
     Post => (writeRegLow8Post(R14'Old, R14, Val));
     --Post => (R14 = ((R14'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --		       Definition of R15 and R15L			  --
   -----------------------------------------------------------------------

   R15 : Unsigned64 := 0;

   -- Returns the Value of bits 1-8 from R15
   function R15L return Unsigned8 with
     Global => (Input => R15),
     Post => (R15L'Result = readRegLow8(R15));
     --Post => (R15L'Result = Unsigned8(R15 and 16#00000000000000FF#));

   procedure Write_R15L(Val : in Unsigned8) with
     Global => (In_Out => R15),
     Post => (writeRegLow8Post(R15'Old, R15, Val));
     --Post => (R15 = ((R15'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --			      Read/Write Memory 			--
   -----------------------------------------------------------------------
   Memory	    : Mem_Array   := Mem_Array'(others => 0);

   function ReadMem8(addr : in Unsigned64) return Unsigned8 with
     Global => (Input => Memory),
     Post => (ReadMem8'Result = Memory(addr));

   procedure WriteMem8(addr : in Unsigned64; Val : in Unsigned8) with
     Global => (In_Out => Memory),
     Post => --((ReadMem8(addr) = Val) and
               ((Memory(addr) = Val) and
                (for all i in Unsigned64 =>
                     (if (i /= addr) then
                        (Memory(i) = Memory'Old(i)))));

   -- Note that if addr is Unsigned64'Last, this will take the last byte in
   -- Memory as the "low" byte and the first byte in Memory as the "high" byte
   function ReadMem16(addr: in Unsigned64) return Unsigned16 with
     Global => (Input => Memory),
     -- Post => (ReadMem16'Result = (Unsigned16(Memory(addr)) or
     --             Shift_Left(Unsigned16(Memory(addr+1)),8)));
     Post => (((ReadMem16'Result and 16#00FF#) = Unsigned16(Memory(addr))) and
              ((ReadMem16'Result and 16#FF00#) = Unsigned16(Memory(addr+1))*16#100#));

   procedure WriteMem16(addr : in Unsigned64; Val : in Unsigned16) with
     Global => (In_Out => Memory),
     Post => --((ReadMem16(addr) = Val) and
                (((Val and 16#00FF#) = Unsigned16(Memory(addr)))               and
                 ((Val and 16#FF00#) = Unsigned16(Memory(addr+1))*16#100#)     and
                (for all i in Unsigned64 =>
                     (if ((i /= addr) and (i /= addr + 1)) then
                          (Memory(i) = Memory'Old(i)))));

   -- See note for ReadMem16, but this can wrap around 3 different ways
   function ReadMem32(addr: in Unsigned64) return Unsigned32 with
     Global => (Input => Memory),
     -- Post => (ReadMem32'Result = (Unsigned32(ReadMem16(addr)) or
     --             Shift_Left(Unsigned32(ReadMem16(addr + 2)),16)));
     Post => (((ReadMem32'Result and 16#000000FF#) = Unsigned32(Memory(addr)))             and
              ((ReadMem32'Result and 16#0000FF00#) = Unsigned32(Memory(addr+1))*16#100#)   and
              ((ReadMem32'Result and 16#00FF0000#) = Unsigned32(Memory(addr+2))*16#10000#) and
              ((ReadMem32'Result and 16#FF000000#) = Unsigned32(Memory(addr+3))*16#1000000#));

   -- Saves a 32-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-3
   procedure WriteMem32(addr : in Unsigned64; Val : in Unsigned32) with
     Global => (In_Out => Memory),
     Post => -- ((ReadMem32(addr) = Val) and
     (((Val and 16#000000FF#) = Unsigned32(Memory(addr)))               and
     ((Val and 16#0000FF00#) = Unsigned32(Memory(addr+1))*16#100#)     and
     ((Val and 16#00FF0000#) = Unsigned32(Memory(addr+2))*16#10000#)   and
     ((Val and 16#FF000000#) = Unsigned32(Memory(addr+3))*16#1000000#) and
       (for all i in Unsigned64 =>
          (if ((i /= addr) and (i /= addr + 1) and
             (i /= addr + 2) and (i /= addr + 3)) then
             (Memory(i) = Memory'Old(i)))));

   -- See note for ReadMem32
   function ReadMem64(addr: in Unsigned64) return Unsigned64 with
     Global => (Input => Memory),
     -- Post => (ReadMem64'Result = (Unsigned64(ReadMem32(addr)) or
     --             Shift_Left(Unsigned64(ReadMem32(addr + 4)),32)));
     Post => (((ReadMem64'Result and 16#00000000000000FF#) = Unsigned64(Memory(addr)))                    and
             ((ReadMem64'Result and 16#000000000000FF00#) = Unsigned64(Memory(addr+1))*16#100#)           and
             ((ReadMem64'Result and 16#0000000000FF0000#) = Unsigned64(Memory(addr+2))*16#10000#)         and
             ((ReadMem64'Result and 16#00000000FF000000#) = Unsigned64(Memory(addr+3))*16#1000000#)       and
             ((ReadMem64'Result and 16#000000FF00000000#) = Unsigned64(Memory(addr+4))*16#100000000#)     and
             ((ReadMem64'Result and 16#0000FF0000000000#) = Unsigned64(Memory(addr+5))*16#10000000000#)   and
             ((ReadMem64'Result and 16#00FF000000000000#) = Unsigned64(Memory(addr+6))*16#1000000000000#) and
             ((ReadMem64'Result and 16#FF00000000000000#) = Unsigned64(Memory(addr+7))*16#100000000000000#));

   -- Saves a 64-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-7
   procedure WriteMem64(addr : in Unsigned64; Val : in Unsigned64) with
     Global => (In_Out => Memory),
     Post => -- ((ReadMem64(addr) = Val) and
          (((Val and 16#00000000000000FF#) = Unsigned64(Memory(addr)))                      and
          ((Val and 16#000000000000FF00#) = Unsigned64(Memory(addr+1))*16#100#)             and
          ((Val and 16#0000000000FF0000#) = Unsigned64(Memory(addr+2))*16#10000#)           and
          ((Val and 16#00000000FF000000#) = Unsigned64(Memory(addr+3))*16#1000000#)         and
          ((Val and 16#000000FF00000000#) = Unsigned64(Memory(addr+4))*16#100000000#)       and
          ((Val and 16#0000FF0000000000#) = Unsigned64(Memory(addr+5))*16#10000000000#)     and
          ((Val and 16#00FF000000000000#) = Unsigned64(Memory(addr+6))*16#1000000000000#)   and
          ((Val and 16#FF00000000000000#) = Unsigned64(Memory(addr+7))*16#100000000000000#) and
            (for all i in Unsigned64 =>
               (if  ((i /= addr)    and (i /= addr + 1) and
                  (i /= addr + 2) and (i /= addr + 3) and
                  (i /= addr + 4) and (i /= addr + 5) and
                  (i /= addr + 6) and (i /= addr + 7)) then
                  (Memory(i) = Memory'Old(i)))));


   -----------------------------------------------------------------------
   --			    Comparison functions			--
   -----------------------------------------------------------------------

   function SignedLT_32(Val1, Val2 : in Unsigned32) return boolean with
     Post => (SignedLT_32'Result = ((Unsigned64(Val1) + Unsigned64(Val2)) >
                  Unsigned64(Val1 + Val2)));

   function SignedLTE_32(Val1, Val2 : in Unsigned32) return boolean with
     Post => (SignedLTE_32'Result = ((Val1 = Val2) or SignedLT_32(Val1, Val2)));

   -----------------------------------------------------------------------
   --			      Sign extensions                           --
   -----------------------------------------------------------------------

   function SignExtend8To16(Val : in Unsigned8) return Unsigned16 with
     Post => ((if (Val > 16#7F#) then
                 (SignExtend8To16'Result = (16#FF00# or Unsigned16(Val)))
               else
                 (SignExtend8To16'Result = Unsigned16(Val))) and
               (Unsigned8(SignExtend8To16'Result and 16#00FF#) = Val));

   function SignExtend16To32(Val : in Unsigned16) return Unsigned32 with
     Post => ((if (Val > 16#7FFF#) then
                 (SignExtend16To32'Result = (16#FFFF0000# or Unsigned32(Val)))
               else
                 (SignExtend16To32'Result = Unsigned32(Val))) and
               (Unsigned16(SignExtend16To32'Result and 16#0000FFFF#) = Val));

   function SignExtend32To64(Val : in Unsigned32) return Unsigned64 with
     Post => ((if (Val > 16#7FFFFFFF#) then
                 (SignExtend32To64'Result = (16#FFFFFFFF00000000# or Unsigned64(Val)))
               else
                 (SignExtend32To64'Result = Unsigned64(Val))) and
               (Unsigned32(SignExtend32To64'Result and 16#00000000FFFFFFFF#) = Val));

   -----------------------------------------------------------------------
   --			      Semi-complex X86				--
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

   procedure  rep_stosq with
     Global => (In_Out => (RDI, RCX, Memory),
                Input => (RAX)),
     --Pre => RCX < Unsigned64'Last/8,
     Post =>
       RCX = 0 and
       RDI = RDI'Old + (8*RCX'Old) and
     (for all i in Unsigned64 =>
        ( if not InRange64(i,RDI'Old,RCX'Old*8) then
             Memory'Old(i) = Memory(i))) and
     (if RCX'Old /= 0 then
        (for all i in 0 .. (RCX'Old-1)  =>
             ReadMem64(RDI'Old+i*8) = RAX));

   ----------------------------------------------------------------------
   --	setb, setnbe						       --
   ----------------------------------------------------------------------

   procedure setb_DL with
     Global => (Input => CarryFlag, In_Out => RDX),
     Post => (if (CarryFlag) then (DL = 1) else
                  (DL = 0));

   procedure setnbe_CL with
     Global => (Input => (ZeroFlag, CarryFlag), In_Out => RCX),
     Post => (if ((not CarryFlag) and (not ZeroFlag)) then (CL = 1) else
                  (CL = 0));

   ----------------------------------------------------------------------

   function ReadMem64Ghost(mem: in Mem_Array; addr: in Unsigned64)
                           return Unsigned64 with Ghost,
     Global => (Input => Memory),
     Post => (ReadMem64Ghost'Result = (Unsigned64(mem(addr)) or
                  Shift_Left(Unsigned64(mem(addr+1)),8) or
                Shift_Left(Unsigned64(mem(addr+2)),16) or
                Shift_Left(Unsigned64(mem(addr+3)),24) or
                Shift_Left(Unsigned64(mem(addr+4)),32) or
                Shift_Left(Unsigned64(mem(addr+5)),40) or
                Shift_Left(Unsigned64(mem(addr+6)),48) or
                Shift_Left(Unsigned64(mem(addr+7)),56)));

   function ReadMem8Ghost(mem: in Mem_Array; addr: in Unsigned64)
                          return Unsigned8 with Ghost,
     Global => (Input => Memory),
     Post => (ReadMem8Ghost'Result = (mem(addr)));

end X86;




