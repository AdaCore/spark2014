with Interfaces;
use Interfaces;
with X86;

Package memcpy
with SPARK_Mode
is

   subtype Unsigned64 is X86.Unsigned64;
   subtype Unsigned32 is X86.Unsigned32;
   subtype Unsigned16 is X86.Unsigned16;
   subtype Unsigned8  is X86.Unsigned8;

   procedure memcpy2 with
     --Removed DummyVar
     Global => (In_Out => (X86.Memory, X86.Exit_Called, X86.CarryFlag,
                           X86.OverflowFlag, X86.SignFlag, X86.ZeroFlag,
                           X86.RAX,  X86.RCX,  X86.RDX,  X86.RBX,
                           X86.RSP,  X86.RBP,  X86.RSI,  X86.RDI,
                           X86.R8,  X86.R9,  X86.R10,  X86.R11,
                           X86.R12,  X86.R13,  X86.R14,  X86.R15),
                Input => (X86.StackAddressSize, X86.FS, X86.GS)),
     Pre =>
       (for all i in Unsigned64 => (if X86.InMemoryRange(i, X86.RDI, X86.RDI+X86.RDX) then
                                      X86.InSafeRegion64(i,X86.RSP))),
     Post =>
       (X86.RSP = (X86.RSP'Old + 8)) and
       (X86.Memory(X86.RSP'Old)     = X86.Memory'Old(X86.RSP'Old)) and
       (X86.Memory(X86.RSP'Old + 1) = X86.Memory'Old(X86.RSP'Old + 1)) and
       (X86.Memory(X86.RSP'Old + 2) = X86.Memory'Old(X86.RSP'Old + 2)) and
       (X86.Memory(X86.RSP'Old + 3) = X86.Memory'Old(X86.RSP'Old + 3)) and
       (X86.Memory(X86.RSP'Old + 4) = X86.Memory'Old(X86.RSP'Old + 4)) and
       (X86.Memory(X86.RSP'Old + 5) = X86.Memory'Old(X86.RSP'Old + 5)) and
       (X86.Memory(X86.RSP'Old + 6) = X86.Memory'Old(X86.RSP'Old + 6)) and
       (X86.Memory(X86.RSP'Old + 7) = X86.Memory'Old(X86.RSP'Old + 7)) and
       (X86.RBP = X86.RBP'Old)	and
     (for all i in Unsigned64 => (if not X86.InMemoryRange(i,  X86.RDI'Old, X86.RDI'Old + X86.RDX'Old)
                                  and X86.InSafeRegion64(i, X86.RSP'Old) then
                                    (X86.Memory(i) = X86.Memory'Old(i))));


end memcpy;
