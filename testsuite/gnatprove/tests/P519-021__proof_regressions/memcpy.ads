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

   procedure printf with
     Global => (In_Out => X86.RSP),
     Post => (X86.RSP = X86.RSP'Old + 8);

   procedure strlen with
     Global => (In_Out => X86.RSP),
     Post => (X86.RSP = X86.RSP'Old + 8);

   procedure memcpy2 with
     Global => (In_Out => (X86.Memory, X86.CarryFlag,
                           X86.OverflowFlag, X86.SignFlag, X86.ZeroFlag,
                           X86.RAX,  X86.RCX,  X86.RDX,
                           X86.RSP,  X86.RBP,  X86.RSI,  X86.RDI)),
     Pre => (for all i in Unsigned64 => (if X86.InRange64(i, X86.RDI, X86.RDX) then
                                           X86.InSafeRegion64(i,X86.RSP))),

     Post => (X86.RSP = (X86.RSP'Old + 8)) and
     (X86.Memory(X86.RSP'Old) = X86.Memory'Old(X86.RSP'Old)) and
     (X86.Memory(X86.RSP'Old + 1) = X86.Memory'Old(X86.RSP'Old + 1)) and
     (X86.Memory(X86.RSP'Old + 2) = X86.Memory'Old(X86.RSP'Old + 2)) and
     (X86.Memory(X86.RSP'Old + 3) = X86.Memory'Old(X86.RSP'Old + 3)) and
     (X86.Memory(X86.RSP'Old + 4) = X86.Memory'Old(X86.RSP'Old + 4)) and
     (X86.Memory(X86.RSP'Old + 5) = X86.Memory'Old(X86.RSP'Old + 5)) and
     (X86.Memory(X86.RSP'Old + 6) = X86.Memory'Old(X86.RSP'Old + 6)) and
     (X86.Memory(X86.RSP'Old + 7) = X86.Memory'Old(X86.RSP'Old + 7)) and
     (X86.RBP = X86.RBP'Old) and
     (for all i in Unsigned64 =>
        (if (not X86.InRange64(i, X86.RDI'Old, X86.RDX'Old)) and  X86.InSafeRegion64(i, X86.RSP'Old)
             then
           (X86.Memory(i) = X86.Memory'Old(i))));


   procedure ZSTLoopProc_400605 with
     Global => (Input => (X86.RSP, X86.RBP),
                Output => (X86.RAX, X86.CarryFlag, X86.SignFlag, X86.OverflowFlag, X86.ZeroFlag),
                In_Out => (X86.RCX, X86.RDX, X86.Memory)),
     Pre => ((X86.RBP = X86.RSP) and
                 (X86.ReadMem64(X86.RBP - 8) = 0) and
               (for all i in Unsigned64 =>
                    (if X86.InRange64(i, X86.ReadMem64( X86.RBP -16 ), X86.ReadMem64( X86.RBP -72 )) then
                         X86.InSafeRegion64(i,X86.RSP+8)))),
       Post => (for all i in Unsigned64 =>
                  (if (not X86.InRange64(i, X86.ReadMem64( X86.RBP -16 ),X86.ReadMem64( X86.RBP -72 )) and
                       (not X86.InRange64(i, X86.RBP-8,8))) then
                     (X86.Memory(i) = X86.Memory'Old(i)))) and

     --X86.ReadMem64Ghost(X86.Memory'Old,X86.RBP-16) = X86.ReadMem64Ghost(X86.Memory,X86.RBP-16) and
     (X86.Memory(X86.RBP'Old-16) = X86.Memory'Old(X86.RBP'Old-16)) and
     (X86.Memory(X86.RBP'Old-16+1) = X86.Memory'Old(X86.RBP'Old-16+1)) and
     (X86.Memory(X86.RBP'Old-16+2) = X86.Memory'Old(X86.RBP'Old-16+2)) and
     (X86.Memory(X86.RBP'Old-16+3) = X86.Memory'Old(X86.RBP'Old-16+3)) and
     (X86.Memory(X86.RBP'Old-16+4) = X86.Memory'Old(X86.RBP'Old-16+4)) and
     (X86.Memory(X86.RBP'Old-16+5) = X86.Memory'Old(X86.RBP'Old-16+5)) and
     (X86.Memory(X86.RBP'Old-16+6) = X86.Memory'Old(X86.RBP'Old-16+6)) and
     (X86.Memory(X86.RBP'Old-16+7) = X86.Memory'Old(X86.RBP'Old-16+7)) and

     --X86.ReadMem64Ghost(X86.Memory'Old,X86.RBP-72) = X86.ReadMem64Ghost(X86.Memory,X86.RBP-72) and
     (X86.Memory(X86.RBP'Old-72) = X86.Memory'Old(X86.RBP'Old-72)) and
     (X86.Memory(X86.RBP'Old-72+1) = X86.Memory'Old(X86.RBP'Old-72+1)) and
     (X86.Memory(X86.RBP'Old-72+2) = X86.Memory'Old(X86.RBP'Old-72+2)) and
     (X86.Memory(X86.RBP'Old-72+3) = X86.Memory'Old(X86.RBP'Old-72+3)) and
     (X86.Memory(X86.RBP'Old-72+4) = X86.Memory'Old(X86.RBP'Old-72+4)) and
     (X86.Memory(X86.RBP'Old-72+5) = X86.Memory'Old(X86.RBP'Old-72+5)) and
     (X86.Memory(X86.RBP'Old-72+6) = X86.Memory'Old(X86.RBP'Old-72+6)) and
     (X86.Memory(X86.RBP'Old-72+7) = X86.Memory'Old(X86.RBP'Old-72+7)) and

     --Not necessary but part of the heuristic
     X86.ReadMem64Ghost(X86.Memory,X86.RBP-8)  >= X86.ReadMem64Ghost(X86.Memory,X86.RBP-72)/8 and

     --X86.ReadMem64Ghost(X86.Memory'Old,X86.RBP) = X86.ReadMem64Ghost(X86.Memory,X86.RBP) and
     (X86.Memory(X86.RBP'Old) = X86.Memory'Old(X86.RBP'Old)) and
     (X86.Memory(X86.RBP'Old+1) = X86.Memory'Old(X86.RBP'Old+1)) and
     (X86.Memory(X86.RBP'Old+2) = X86.Memory'Old(X86.RBP'Old+2)) and
     (X86.Memory(X86.RBP'Old+3) = X86.Memory'Old(X86.RBP'Old+3)) and
     (X86.Memory(X86.RBP'Old+4) = X86.Memory'Old(X86.RBP'Old+4)) and
     (X86.Memory(X86.RBP'Old+5) = X86.Memory'Old(X86.RBP'Old+5)) and
     (X86.Memory(X86.RBP'Old+6) = X86.Memory'Old(X86.RBP'Old+6)) and
     (X86.Memory(X86.RBP'Old+7) = X86.Memory'Old(X86.RBP'Old+7)) and

     --X86.ReadMem64Ghost(X86.Memory'Old,X86.RSP+8) = X86.ReadMem64Ghost(X86.Memory,X86.RSP+8)
     (X86.Memory(X86.RSP'Old+8) = X86.Memory'Old(X86.RSP'Old+8)) and
     (X86.Memory(X86.RSP'Old+8 + 1) = X86.Memory'Old(X86.RSP'Old+8 + 1)) and
     (X86.Memory(X86.RSP'Old+8 + 2) = X86.Memory'Old(X86.RSP'Old+8 + 2)) and
     (X86.Memory(X86.RSP'Old+8 + 3) = X86.Memory'Old(X86.RSP'Old+8 + 3)) and
     (X86.Memory(X86.RSP'Old+8 + 4) = X86.Memory'Old(X86.RSP'Old+8 + 4)) and
     (X86.Memory(X86.RSP'Old+8 + 5) = X86.Memory'Old(X86.RSP'Old+8 + 5)) and
     (X86.Memory(X86.RSP'Old+8 + 6) = X86.Memory'Old(X86.RSP'Old+8 + 6)) and
     (X86.Memory(X86.RSP'Old+8 + 7) = X86.Memory'Old(X86.RSP'Old+8 + 7))
   ;


   procedure ZSTLoopProc_40064f with
     Global => (Input => (X86.RSP,X86.RBP),
                Output => (X86.ZeroFlag, X86.SignFlag, X86.CarryFlag,  X86.OverflowFlag),
                In_Out => (X86.Memory, X86.RCX, X86.RDX, X86.RAX)),
     Pre => ((X86.RBP = X86.RSP) and
                 (X86.ReadMem64(X86.RBP - 8) = 0) and --if known, increases efficiency
             --must use InRange to avoid wrapping concerns
               (for all i in Unsigned64 =>
                    (if X86.InRange64(i, X86.ReadMem64( X86.RBP -32 ), X86.ReadMem64( X86.RBP -72 )) then
                         X86.InSafeRegion64(i,X86.RSP+8)))),
       Post => (for all i in Unsigned64 =>
                  (if (not X86.InRange64(i, X86.ReadMem64( X86.RBP -32 ),X86.ReadMem64( X86.RBP -72 )) and
                       (not X86.InRange64(i, X86.RBP-8,8))) then
                     (X86.Memory(i) = X86.Memory'Old(i)))) and
     --X86.ReadMem64Ghost(X86.Memory'Old,X86.RBP-32) = X86.ReadMem64Ghost(X86.Memory,X86.RBP-32) and
     (X86.Memory(X86.RBP'Old-32) = X86.Memory'Old(X86.RBP'Old-32)) and
     (X86.Memory(X86.RBP'Old-32+1) = X86.Memory'Old(X86.RBP'Old-32+1)) and
     (X86.Memory(X86.RBP'Old-32+2) = X86.Memory'Old(X86.RBP'Old-32+2)) and
     (X86.Memory(X86.RBP'Old-32+3) = X86.Memory'Old(X86.RBP'Old-32+3)) and
     (X86.Memory(X86.RBP'Old-32+4) = X86.Memory'Old(X86.RBP'Old-32+4)) and
     (X86.Memory(X86.RBP'Old-32+5) = X86.Memory'Old(X86.RBP'Old-32+5)) and
     (X86.Memory(X86.RBP'Old-32+6) = X86.Memory'Old(X86.RBP'Old-32+6)) and
     (X86.Memory(X86.RBP'Old-32+7) = X86.Memory'Old(X86.RBP'Old-32+7)) and
     --X86.ReadMem64Ghost(X86.Memory'Old,X86.RBP-72) = X86.ReadMem64Ghost(X86.Memory,X86.RBP-72) and
     (X86.Memory(X86.RBP'Old-72) = X86.Memory'Old(X86.RBP'Old-72)) and
     (X86.Memory(X86.RBP'Old-72+1) = X86.Memory'Old(X86.RBP'Old-72+1)) and
     (X86.Memory(X86.RBP'Old-72+2) = X86.Memory'Old(X86.RBP'Old-72+2)) and
     (X86.Memory(X86.RBP'Old-72+3) = X86.Memory'Old(X86.RBP'Old-72+3)) and
     (X86.Memory(X86.RBP'Old-72+4) = X86.Memory'Old(X86.RBP'Old-72+4)) and
     (X86.Memory(X86.RBP'Old-72+5) = X86.Memory'Old(X86.RBP'Old-72+5)) and
     (X86.Memory(X86.RBP'Old-72+6) = X86.Memory'Old(X86.RBP'Old-72+6)) and
     (X86.Memory(X86.RBP'Old-72+7) = X86.Memory'Old(X86.RBP'Old-72+7)) and

     --Not necessary but part of the heuristic
     X86.ReadMem64Ghost(X86.Memory,X86.RBP-8)  >= X86.ReadMem64Ghost(X86.Memory,X86.RBP-72) and

     --X86.ReadMem64Ghost(X86.Memory'Old,X86.RBP) = X86.ReadMem64Ghost(X86.Memory,X86.RBP) and
     (X86.Memory(X86.RBP'Old) = X86.Memory'Old(X86.RBP'Old)) and
     (X86.Memory(X86.RBP'Old+1) = X86.Memory'Old(X86.RBP'Old+1)) and
     (X86.Memory(X86.RBP'Old+2) = X86.Memory'Old(X86.RBP'Old+2)) and
     (X86.Memory(X86.RBP'Old+3) = X86.Memory'Old(X86.RBP'Old+3)) and
     (X86.Memory(X86.RBP'Old+4) = X86.Memory'Old(X86.RBP'Old+4)) and
     (X86.Memory(X86.RBP'Old+5) = X86.Memory'Old(X86.RBP'Old+5)) and
     (X86.Memory(X86.RBP'Old+6) = X86.Memory'Old(X86.RBP'Old+6)) and
     (X86.Memory(X86.RBP'Old+7) = X86.Memory'Old(X86.RBP'Old+7)) and

     --X86.ReadMem64Ghost(X86.Memory'Old,X86.RSP+8) = X86.ReadMem64Ghost(X86.Memory,X86.RSP+8)
     (X86.Memory(X86.RSP'Old+8) = X86.Memory'Old(X86.RSP'Old+8)) and
     (X86.Memory(X86.RSP'Old+8 + 1) = X86.Memory'Old(X86.RSP'Old+8 + 1)) and
     (X86.Memory(X86.RSP'Old+8 + 2) = X86.Memory'Old(X86.RSP'Old+8 + 2)) and
     (X86.Memory(X86.RSP'Old+8 + 3) = X86.Memory'Old(X86.RSP'Old+8 + 3)) and
     (X86.Memory(X86.RSP'Old+8 + 4) = X86.Memory'Old(X86.RSP'Old+8 + 4)) and
     (X86.Memory(X86.RSP'Old+8 + 5) = X86.Memory'Old(X86.RSP'Old+8 + 5)) and
     (X86.Memory(X86.RSP'Old+8 + 6) = X86.Memory'Old(X86.RSP'Old+8 + 6)) and
     (X86.Memory(X86.RSP'Old+8 + 7) = X86.Memory'Old(X86.RSP'Old+8 + 7))
   ;


      procedure main with
        Global => (In_Out => (X86.Memory, X86.CarryFlag,
                              X86.OverflowFlag, X86.SignFlag, X86.ZeroFlag,
                              X86.RAX,  X86.RCX,  X86.RDX,
                              X86.RSP,  X86.RBP,  X86.RSI,  X86.RDI)),
        Post => (X86.RSP = (X86.RSP'Old + 8))
        and
        (X86.Memory(X86.RSP'Old) = X86.Memory'Old(X86.RSP'Old)) and
        (X86.Memory(X86.RSP'Old + 1) = X86.Memory'Old(X86.RSP'Old + 1)) and
        (X86.Memory(X86.RSP'Old + 2) = X86.Memory'Old(X86.RSP'Old + 2)) and
        (X86.Memory(X86.RSP'Old + 3) = X86.Memory'Old(X86.RSP'Old + 3)) and
        (X86.Memory(X86.RSP'Old + 4) = X86.Memory'Old(X86.RSP'Old + 4)) and
        (X86.Memory(X86.RSP'Old + 5) = X86.Memory'Old(X86.RSP'Old + 5)) and
        (X86.Memory(X86.RSP'Old + 6) = X86.Memory'Old(X86.RSP'Old + 6)) and
        (X86.Memory(X86.RSP'Old + 7) = X86.Memory'Old(X86.RSP'Old + 7));


end memcpy;
