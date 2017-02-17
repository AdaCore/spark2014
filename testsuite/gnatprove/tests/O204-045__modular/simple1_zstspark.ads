with X86;
use type X86.Unsigned64;
use type X86.Unsigned32;

package Simple1_Zstspark
  with SPARK_Mode
is

   subtype Unsigned64 is X86.Unsigned64;
   subtype Unsigned32 is X86.Unsigned32;

   procedure main with
     Global => (In_Out => (X86.Memory, X86.RAX, X86.RDX,
                           X86.RSP, X86.RDI, X86.RBP, X86.RSI,
                            X86.SignFlag, X86.OverflowFlag,
                           X86.ZeroFlag, X86.CarryFlag)),
     Post   => (X86.RSP = X86.RSP'Old + 8);

end Simple1_Zstspark;
