package body X86
with SPARK_Mode
is

   function SafeDivision64(dividend: in Unsigned64; divisor: in Unsigned64)
                           return Unsigned64 is
   begin
      pragma Assume (divisor /= 0);
      return dividend / divisor;
   end SafeDivision64;

   -----------------------------------------------------------------------
   function InRange64(Var: in Unsigned64; Bottom: in Unsigned64; Range_Size: Unsigned64)
                      return Boolean is
     (if (Range_Size = 0) then
           false
      elsif (Bottom <= Unsigned64'Last - (Range_Size - 1)) then
        (Bottom <= Var and Var <= Bottom + (Range_Size - 1))
      else
        (Bottom <= Var and Var <= Unsigned64'Last) or
          (Var <= Range_Size - (Unsigned64'Last - Bottom) - 2));





   -----------------------------------------------------------------------

   function InSafeRegion64(var: in Unsigned64; rsp: in Unsigned64)
                           return Boolean is
     ((var>= rsp+8 and var < X86.StackBottom) or (var <= X86.MiscStorageHigh and var >= X86.MiscStorageLow));


   function RangesIntersect(var1: in Unsigned64; var1_range_size: in Unsigned64; var2: in Unsigned64; var2_range_size: in Unsigned64)
                            return Boolean is
   begin
      return InRange64(var1,var2-(var1_range_size-1), (var1_range_size-1)+var2_range_size);
   end RangesIntersect;


   procedure CallExit
   is
   begin
      Exit_Called := true;
   end CallExit;



   -----------------------------------------------------------------------
   --		 X86 Register Hierarchy Generic Read and Write 		--
   -----------------------------------------------------------------------

   function readRegLow8 (Reg : in Unsigned64) return Unsigned8 is
   begin
      return Unsigned8(Reg and 16#00000000000000FF#);
   end readRegLow8;

   procedure writeRegLow8(Reg : in out Unsigned64; Val : in Unsigned8) is
   begin
      Reg := (Reg and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end writeRegLow8;

   function writeRegLow8Post(RegOld : in Unsigned64; RegNew: in Unsigned64; Val : in Unsigned8)
                             return Boolean is
     ((readRegLow8(RegNew) = Val) and ((RegNew and 16#FFFFFFFFFFFFFF00#) = (RegOld and 16#FFFFFFFFFFFFFF00#)));

   function readRegHigh8 (Reg : in Unsigned64) return Unsigned8 is
   begin
      return Unsigned8((Reg and 16#000000000000FF00#) / 256);
   end readRegHigh8;

   procedure writeRegHigh8(Reg : in out Unsigned64; Val : in Unsigned8) is
   begin
      Reg := ((Reg and 16#FFFFFFFFFFFF00FF#) or Unsigned64(Unsigned16(Val) * 256));
   end writeRegHigh8;

   function writeRegHigh8Post(RegOld : in Unsigned64; RegNew: in Unsigned64; Val : in Unsigned8)
                              return Boolean is
     ((readRegHigh8(RegNew) = Val) and ((RegNew and 16#FFFFFFFFFFFF00FF#) = (RegOld and 16#FFFFFFFFFFFF00FF#)));

   function readReg16 (Reg : in Unsigned64) return Unsigned16 is
   begin
      return Unsigned16(Reg and 16#000000000000FFFF#);
   end readReg16;

   procedure writeReg16(Reg : in out Unsigned64; Val : in Unsigned16) is
   begin
      Reg := (Reg and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end writeReg16;

   function writeReg16Post(RegOld : in Unsigned64; RegNew: in Unsigned64; Val : in Unsigned16)
                           return Boolean is
     ((readReg16(RegNew) = Val) and ((RegNew and 16#FFFFFFFFFFFF0000#) = (RegOld and 16#FFFFFFFFFFFF0000#)));

   function readReg32(Reg : in Unsigned64) return Unsigned32 is
   begin
      return Unsigned32(Reg and 16#00000000FFFFFFFF#);
   end readReg32;

   procedure writeReg32(Reg : in out Unsigned64; Val : in Unsigned32) is
   begin
      Reg := Unsigned64(Val);
   end writeReg32;

   function writeReg32Post(RegNew: in Unsigned64; Val : in Unsigned32)
                           return Boolean is
     ((readReg32(RegNew) = Val) and ((RegNew and 16#FFFFFFFF00000000#) = (16#0000000000000000#)));

   -----------------------------------------------------------------------
   --		 Implementation of AL, AH, AX, EAX, and RAX		--
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
      return Unsigned8((RAX and 16#000000000000FF00#) / 256);
   end AH;

   procedure Write_AH(Val : in Unsigned8) is
   begin
      RAX := ((RAX and 16#FFFFFFFFFFFF00FF#) or Unsigned64(Unsigned16(Val) * 256));
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
      RAX := Unsigned64(Val);
   end Write_EAX;

   -----------------------------------------------------------------------
   --		 Implementation of CL, CH, CX, ECX, and RCX		--
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
      return Unsigned8((RCX and 16#000000000000FF00#) / 256);
   end CH;

   procedure Write_CH(Val : in Unsigned8) is
   begin
      RCX := ((RCX and 16#FFFFFFFFFFFF00FF#) or Unsigned64(Unsigned16(Val) * 256));
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
      RCX := Unsigned64(Val);
   end Write_ECX;

   -----------------------------------------------------------------------
   --		 Implementation of DL, DH, DX, EDX, and RDX		--
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
      return Unsigned8((RDX and 16#000000000000FF00#) / 256);
   end DH;

   procedure Write_DH(Val : in Unsigned8) is
   begin
      RDX := ((RDX and 16#FFFFFFFFFFFF00FF#) or Unsigned64(Unsigned16(Val) * 256));
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
      RDX :=  Unsigned64(Val);
   end Write_EDX;

   -----------------------------------------------------------------------
   --		 Implementation of BL, BH, BX, EBX, and RBX		--
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
      return Unsigned8((RBX and 16#000000000000FF00#) / 256);
   end BH;

   procedure Write_BH(Val : in Unsigned8) is
   begin
      RBX := ((RBX and 16#FFFFFFFFFFFF00FF#) or Unsigned64(Unsigned16(Val) * 256));
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
      RBX :=  Unsigned64(Val);
   end Write_EBX;

   -----------------------------------------------------------------------
   --		     Implementation of SP, ESP, and RSP 		--
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
      RSP := Unsigned64(Val);
   end Write_ESP;

   -----------------------------------------------------------------------
   --		     Implementation of BP, EBP, and RBP 		--
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
      RBP := Unsigned64(Val);
   end Write_EBP;

   -----------------------------------------------------------------------
   --		     Implementation of SI, ESI, and RSI 		--
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
      RSI :=  Unsigned64(Val);
   end Write_ESI;

   -----------------------------------------------------------------------
   --		     Implementation of DI, EDI, and RDI 		--
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
      RDI := Unsigned64(Val);
   end Write_EDI;

   -----------------------------------------------------------------------
   --		     Implementation of R8 and R8L			--
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
   --		     Implementation of R9 and R9L			--
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
   --		     Implementation of R10 and R10L			  --
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
   --		     Implementation of R11 and R11L			  --
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
   --		     Implementation of R12 and R12L			  --
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
   --		     Implementation of R13 and R13L			  --
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
   --		     Implementation of R14 and R14L			  --
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
   --		     Implementation of R15 and R15L			  --
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
   --			      Read/Write Memory 			--
   -----------------------------------------------------------------------

   function ReadMem8(addr : in Unsigned64) return Unsigned8
   is
   begin
      return Memory(addr);
   end ReadMem8;

   procedure WriteMem8(addr : in Unsigned64; Val : in Unsigned8)
   is
   begin
      Memory(addr) := Val;
   end WriteMem8;

   -- Note that if addr is Unsigned64'Last, this will take the last byte in
   -- Memory as the "low" byte and the first byte in Memory as the "high" byte
   function ReadMem16(addr: in Unsigned64) return Unsigned16
   is
   begin
      return (Unsigned16(ReadMem8(addr)) or Shift_Left(Unsigned16(ReadMem8(addr+1)),8));
   end ReadMem16;

   procedure WriteMem16(addr : in Unsigned64; Val : in Unsigned16)
   is
   begin
      WriteMem8(addr,     Unsigned8(Val                 and 16#00FF#));
      WriteMem8(addr + 1, Unsigned8(Shift_Right(Val, 8) and 16#00FF#));
   end WriteMem16;


   -- See note for ReadMem16, but this can wrap around 3 different ways
   function ReadMem32(addr: in Unsigned64) return Unsigned32
   is
   begin
      return (Unsigned32(ReadMem8(addr))                     or
                Shift_Left(Unsigned32(ReadMem8(addr+1)), 8)  or
                Shift_Left(Unsigned32(ReadMem8(addr+2)), 16) or
                Shift_Left(Unsigned32(ReadMem8(addr+3)), 24));
   end ReadMem32;

   -- Saves a 32-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-3
   procedure WriteMem32(addr : in Unsigned64; Val : in Unsigned32)
   is
   begin
      WriteMem8(addr,     Unsigned8(Val                  and 16#000000FF#));
      WriteMem8(addr + 1, Unsigned8(Shift_Right(Val,  8) and 16#000000FF#));
      WriteMem8(addr + 2, Unsigned8(Shift_Right(Val, 16) and 16#000000FF#));
      WriteMem8(addr + 3, Unsigned8(Shift_Right(Val, 24) and 16#000000FF#));
   end WriteMem32;

   -- See note for ReadMem32
   function ReadMem64(addr: in Unsigned64) return Unsigned64
   is
      Result : Unsigned64;
   begin
      Result := (Unsigned64(ReadMem8(addr))                    or
                   Shift_Left(Unsigned64(ReadMem8(addr+1)),8)  or
                   Shift_Left(Unsigned64(ReadMem8(addr+2)),16) or
                   Shift_Left(Unsigned64(ReadMem8(addr+3)),24) or
                   Shift_Left(Unsigned64(ReadMem8(addr+4)),32) or
                   Shift_Left(Unsigned64(ReadMem8(addr+5)),40) or
                   Shift_Left(Unsigned64(ReadMem8(addr+6)),48) or
                   Shift_Left(Unsigned64(ReadMem8(addr+7)),56));
      return Result;
   end ReadMem64;

   -- Saves a 64-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-7
   procedure WriteMem64(addr : in Unsigned64; Val : in Unsigned64)
   is
   begin
      WriteMem8(addr,   Unsigned8(Val                  and 16#00000000000000FF#));
      WriteMem8(addr+1, Unsigned8(Shift_Right(Val, 8)  and 16#00000000000000FF#));
      WriteMem8(addr+2, Unsigned8(Shift_Right(Val, 16) and 16#00000000000000FF#));
      WriteMem8(addr+3, Unsigned8(Shift_Right(Val, 24) and 16#00000000000000FF#));
      WriteMem8(addr+4, Unsigned8(Shift_Right(Val, 32) and 16#00000000000000FF#));
      WriteMem8(addr+5, Unsigned8(Shift_Right(Val, 40) and 16#00000000000000FF#));
      WriteMem8(addr+6, Unsigned8(Shift_Right(Val, 48) and 16#00000000000000FF#));
      WriteMem8(addr+7, Unsigned8(Shift_Right(Val, 56) and 16#00000000000000FF#));
   end WriteMem64;

   -----------------------------------------------------------------------
   --			    Comparison functions			--
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
   --			      Sign extensions                           --
   -----------------------------------------------------------------------

   function SignExtend8To16(Val : in Unsigned8) return Unsigned16
   is
      Retval: Unsigned16;
   begin
      if (Val > 16#7F#) then
         Retval := 16#FF00# or Unsigned16(Val);
      else
         Retval := Unsigned16(Val);
      end if;
      return Retval;
   end SignExtend8To16;

   function SignExtend16To32(Val : in Unsigned16) return Unsigned32
   is
      Retval: Unsigned32;
   begin
      if (Val > 16#7FFF#) then
         Retval := 16#FFFF0000# or Unsigned32(Val);
      else
         Retval := Unsigned32(Val);
      end if;
      return Retval;
   end SignExtend16To32;

   function SignExtend32To64(Val : in Unsigned32) return Unsigned64
   is
      Retval: Unsigned64;
   begin
      if (Val > 16#7FFFFFFF#) then
         Retval := 16#FFFFFFFF00000000# or Unsigned64(Val);
      else
         Retval := Unsigned64(Val);
      end if;
      return Retval;
   end SignExtend32To64;

   -----------------------------------------------------------------------
   --			      Semi-complex X86				--
   -----------------------------------------------------------------------

   procedure rep_stosq
   is
      RCX_Start : constant Unsigned64 := RCX with Ghost;
      RDI_Start : constant Unsigned64 := RDI with Ghost;
      Mem       : Mem_Array with Ghost;

      pragma Warnings (GNATprove, Off, "subprogram * has no effect",
                       Reason => "ghost procedures have no effect");

      procedure Previous_RAX_Element (I : Unsigned64) with
        Ghost,
        Pre  =>  --  Property of interest prior to writing to Memory
                HasMem64(Mem, RDI_Start+(I*8), RAX) and then
                --  State the relevant part of the context
                NoOverlap8Equal (Memory, Mem, RDI) and then
                --  State property inferred from context which helps proof
                NoOverlap8 (RDI_Start+(I*8), RDI) and then
                (for all J in Unsigned64 range 0 .. 7 =>
                   Memory (RDI_Start+(I*8)+J) = Mem (RDI_Start+(I*8)+J)),
        Post => --  Property of interest after writing to Memory
                HasMem64(Memory, RDI_Start+(I*8), RAX)
      is
      begin
         null;
      end Previous_RAX_Element;

      procedure Previous_RAX with
        Ghost,
        Pre  => --  Property of interest prior to writing to Memory
                (for all I in 0 .. (RCX_Start - RCX) =>
                   (if I /= RCX_Start - RCX then
                      HasMem64(Mem, RDI_Start+(I*8), RAX))) and then
                --  State the relevant part of the context
                RDI = RDI_Start + (RCX_Start - RCX)*8 and then
                RCX <= RCX_Start and then
                RCX_Start < Unsigned64'Last/8 and then
                NoOverlap8Equal (Memory, Mem, RDI) and then
                --  State property inferred from context which helps proof
                (for all I in 0 .. (RCX_Start - RCX) =>
                   (if I /= RCX_Start - RCX then
                      NoOverlap8 (RDI_Start+(I*8), RDI))),
        Post => --  Property of interest after writing to Memory
                (for all I in 0 .. (RCX_Start - RCX) =>
                   (if I /= RCX_Start - RCX then
                      ReadMem64(RDI_Start+(I*8)) = RAX))
      is
      begin
         for I in 0 .. (RCX_Start - RCX) loop
            if I /= RCX_Start - RCX then
               pragma Assert (for all J in Unsigned64 range 0 .. 7 =>
                                Memory (RDI_Start+(I*8)+J) = Mem (RDI_Start+(I*8)+J));
               Previous_RAX_Element (I);
            end if;
            pragma Loop_Invariant (for all J in 0 .. I =>
                                     (if J /= RCX_Start - RCX then
                                        HasMem64(Memory, RDI_Start+(J*8), RAX)));
         end loop;
      end Previous_RAX;

      procedure Current_RAX with
        Ghost,
        Pre  => (ReadMem64(RDI) = RAX) and then
                (RDI = RDI_Start + ((RCX_Start - RCX)*8)),
        Post => ReadMem64(RDI_Start + ((RCX_Start - RCX)*8)) = RAX
      is
      begin
         null;
      end Current_RAX;

   begin
      --pragma Assume(RCX < Unsigned64'Last/8);

      while (RCX /= 0) loop

         pragma Assert (for all I in 0 .. (RCX'Loop_Entry - RCX) =>
                          (if I /= RCX'Loop_Entry - RCX then
                              ReadMem64(RDI'Loop_Entry+(I*8)) = RAX));

         Mem := Memory;

         WriteMem64(RDI, RAX);

         pragma Assert (for all I in 0 .. (RCX_Start - RCX) =>
                          (if I /= RCX_Start - RCX then
                             HasMem64(Mem, RDI_Start+(I*8), RAX)));
         Previous_RAX;
         Current_RAX;

         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 ( if (not InRange64(i,RDI'Loop_Entry,RCX'Loop_Entry*8)) then
                                      Memory'Loop_Entry(i) = Memory(i)));
         pragma Loop_Invariant(RDI = RDI'Loop_Entry + ((RCX'Loop_Entry - RCX)*8));
         pragma Loop_Invariant(InRange64(RDI, RDI'Loop_Entry, RCX'Loop_Entry*8));
         pragma Loop_Invariant(RCX <= RCX'Loop_Entry);
         pragma Loop_Invariant(ReadMem64(RDI) = RAX);
         pragma Loop_Invariant(ReadMem64(RDI'Loop_Entry + ((RCX'Loop_Entry - RCX)*8)) = RAX);

         --Can't prove this invariant
         pragma Loop_Invariant(for all i in 0 .. (RCX'Loop_Entry - RCX) =>
                                 ReadMem64(RDI'Loop_Entry+(i*8)) = RAX);

         RDI := RDI + 8;
         RCX := RCX - 1;

      end loop;

      pragma Assert (if RCX_Start /= 0 then
                        All_Equal_RAX (RDI_Start, RCX_Start-1));
   end rep_stosq;


   -- repe32 uses ESI and EDI as the location of memory addresses to compare
   -- and ECX as the counter
   procedure repe32_cmpsb
   is
      Val1, Val2: Unsigned8;
   begin
      repe_loop:
      while (ECX > 0) loop
         pragma Loop_Variant (Decreases => ECX);
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
      --	  pragma Assert ((ECX = 0) or (not ZeroFlag));
   end repe32_cmpsb;

   -- repe64 uses RSI and RDI as the location of memory addresses to compare
   -- and RCX as the counter
   procedure repe64_cmpsb
   is
      Val1, Val2: Unsigned8;
   begin
      repe_loop:
      while (RCX > 0) loop
         pragma Loop_Variant (Decreases => RCX);
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
      --	  pragma Assert ((RCX = 0) or (not ZeroFlag));
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

   -----------------------------------------------------------------------

   function ReadMem64Ghost(mem: in Mem_Array; addr: in Unsigned64)
                           return Unsigned64 is
     (Unsigned64(mem(addr))                      or
        Shift_Left(Unsigned64(mem(addr+1)),8)    or
          Shift_Left(Unsigned64(mem(addr+2)),16) or
          Shift_Left(Unsigned64(mem(addr+3)),24) or
          Shift_Left(Unsigned64(mem(addr+4)),32) or
          Shift_Left(Unsigned64(mem(addr+5)),40) or
          Shift_Left(Unsigned64(mem(addr+6)),48) or
          Shift_Left(Unsigned64(mem(addr+7)),56));

   function ReadMem8Ghost(mem: in Mem_Array; addr: in Unsigned64)
                          return Unsigned8 is (mem(addr));


end X86;
