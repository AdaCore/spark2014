with Interfaces;
use Interfaces;

with X86;

package Dumbledore
  with SPARK_Mode
is

   subtype Unsigned64 is X86.Unsigned64;
   subtype Unsigned32 is X86.Unsigned32;
   subtype Unsigned16 is X86.Unsigned16;
   subtype Unsigned8 is X86.Unsigned8;

   procedure readString with
     Global => (In_Out => (X86.Memory, X86.RAX, X86.RDX, X86.RCX, X86.RBX,
                           X86.RSP, X86.RDI, X86.RBP, X86.RSI, X86.R8,
                           X86.Exit_Called,
                           X86.SignFlag, X86.OverflowFlag,
                           X86.ZeroFlag, X86.CarryFlag),
                Input  => (X86.StackAddressSize, X86.FS, X86.GS)),
       --Should we have as much information about incoming parameters as possible?
     Pre => (X86.RSP > 16#FFFFFFFF00000000# and X86.RSP<16#FFFFFFFFFFFFFF00# and
               ((X86.RSI > X86.RSP+8 and X86.RSP < 16#FFFFFFFFFFFFFF00#) or (X86.RSI<16#FFFF000000000000# and X86.RSI > 16#100#)));

end Dumbledore;
