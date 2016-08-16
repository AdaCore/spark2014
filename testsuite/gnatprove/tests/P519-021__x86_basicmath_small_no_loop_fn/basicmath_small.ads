with Interfaces;
use Interfaces;
with X86;

Package basicmath_small
with SPARK_Mode
is

	subtype Unsigned64 is X86.Unsigned64;
	subtype Unsigned32 is X86.Unsigned32;
	subtype Unsigned16 is X86.Unsigned16;
	subtype Unsigned8  is X86.Unsigned8;

	Dummy_Var : Unsigned64 := 0;

procedure printf with
	Global => (In_Out => X86.RSP),
	Post => (X86.RSP = X86.RSP'Old + 8);

procedure puts with
	Global => (In_Out => X86.RSP),
	Post => (X86.RSP = X86.RSP'Old + 8);

procedure putchar with
	Global => (In_Out => X86.RSP),
	Post => (X86.RSP = X86.RSP'Old + 8);

procedure SolveCubic with
	Global => (In_Out => X86.RSP),
	Post => (X86.RSP = X86.RSP'Old + 8);

   procedure loop_6 with
     Global => (Output => (X86.RSI,
                           X86.ZeroFlag, X86.SignFlag, X86.CarryFlag, X86.OverflowFlag),
                In_Out => (X86.RBP, X86.RDI, X86.RAX, X86.RBX, X86.RCX, X86.RDX,
                           X86.R8, X86.RSP, X86.Memory, X86.Exit_Called)),
     Post => ((for all i in Unsigned64 =>
                (if ((i /= X86.RSP + 16#98# - 16#68#) and
                     (i /= X86.RSP + 16#98# - 16#68# + 1) and
                     (i /= X86.RSP + 16#98# - 16#68# + 2) and
                     (i /= X86.RSP + 16#98# - 16#68# + 3) and
                     (i /= X86.RSP + 16#98# - 16#68# + 4) and
                     (i /= X86.RSP + 16#98# - 16#68# + 5) and
                     (i /= X86.RSP + 16#98# - 16#68# + 6) and
                     (i /= X86.RSP + 16#98# - 16#68# + 7)) then
                       (X86.Memory(i) = X86.Memory'Old(i)))) and
                  (X86.RSP = X86.RSP'Old));

   procedure loop_7 with
     Global => (Output => (X86.XMM0, X86.XMM1, X86.ZeroFlag),
                In_Out => (X86.XMM2, X86.RBP, X86.RDI, X86.RAX, X86.RBX, X86.RSP, X86.Memory)),
     Post => ((for all i in Unsigned64 =>
                (if ((i /= X86.RSP) and (i /= X86.RSP + 1) and
                     (i /= X86.RSP + 2) and (i /= X86.RSP + 3) and
                     (i /= X86.RSP + 4) and (i /= X86.RSP + 5) and
                     (i /= X86.RSP + 6) and (i /= X86.RSP + 7)) then
                       (X86.Memory(i) = X86.Memory'Old(i)))) and
                  (X86.RSP = X86.RSP'Old));

   procedure loop_8 with
     Global => (Output => (X86.XMM0, X86.XMM1, X86.ZeroFlag),
                In_Out => (X86.XMM2, X86.RBP, X86.RDI, X86.RAX, X86.RBX, X86.RSP, X86.Memory)),
     Post => ((for all i in Unsigned64 =>
                (if ((i /= X86.RSP) and (i /= X86.RSP + 1) and
                     (i /= X86.RSP + 2) and (i /= X86.RSP + 3) and
                     (i /= X86.RSP + 4) and (i /= X86.RSP + 5) and
                     (i /= X86.RSP + 6) and (i /= X86.RSP + 7)) then
                       (X86.Memory(i) = X86.Memory'Old(i)))) and
                  (X86.RSP = X86.RSP'Old));

procedure main with
	Global => (In_Out => (Dummy_Var, X86.Memory, X86.Exit_Called, X86.CarryFlag,
		X86.OverflowFlag, X86.SignFlag, X86.ZeroFlag,
		 X86.RAX,  X86.RCX,  X86.RDX,  X86.RBX,
		 X86.RSP,  X86.RBP,  X86.RSI,  X86.RDI,
		 X86.R8,  X86.R9,  X86.R10,  X86.R11,
		 X86.R12,  X86.R13,  X86.R14,  X86.R15,
		 X86.XMM0,  X86.XMM1,  X86.XMM2,  X86.XMM3,
		 X86.XMM4,  X86.XMM5,  X86.XMM6,  X86.XMM7),
		Input => (X86.StackAddressSize, X86.FS, X86.GS, X86.SS, X86.DS)),
	Post => ((X86.RSP = (X86.RSP'Old + 8)) and
		(X86.Memory(X86.RSP'Old) = X86.Memory'Old(X86.RSP'Old)) and
		(X86.Memory(X86.RSP'Old + 1) = X86.Memory'Old(X86.RSP'Old + 1)) and
		(X86.Memory(X86.RSP'Old + 2) = X86.Memory'Old(X86.RSP'Old + 2)) and
		(X86.Memory(X86.RSP'Old + 3) = X86.Memory'Old(X86.RSP'Old + 3)) and
		(X86.Memory(X86.RSP'Old + 4) = X86.Memory'Old(X86.RSP'Old + 4)) and
		(X86.Memory(X86.RSP'Old + 5) = X86.Memory'Old(X86.RSP'Old + 5)) and
		(X86.Memory(X86.RSP'Old + 6) = X86.Memory'Old(X86.RSP'Old + 6)) and
		(X86.Memory(X86.RSP'Old + 7) = X86.Memory'Old(X86.RSP'Old + 7)) and
		(X86.RBX = X86.RBX'Old) and
		(X86.RBP = X86.RBP'Old) and
		(X86.R12 = X86.R12'Old) and
		(X86.R13 = X86.R13'Old) and
		(X86.R14 = X86.R14'Old) and
		(X86.R15 = X86.R15'Old));
procedure rad2deg with
	Global => (In_Out => (X86.RSP, X86.XMM0),
		Input => (X86.StackAddressSize, X86.Memory, X86.FS, X86.GS, X86.RDI)),
	Post => (X86.RSP = (X86.RSP'Old + 8));
procedure deg2rad with
	Global => (In_Out => (X86.RSP, X86.XMM0),
		Input => (X86.StackAddressSize, X86.Memory, X86.FS, X86.GS, X86.RDI)),
	Post => (X86.RSP = (X86.RSP'Old + 8));

   procedure usqrt_loop with
     Global => (Output => (X86.RCX,
                           X86.ZeroFlag, X86.SignFlag, X86.CarryFlag, X86.OverflowFlag),
                In_Out => (X86.RDI, X86.RAX, X86.RDX, X86.R8, X86.RSP)),
     Post => (X86.RSP = X86.RSP'Old);

procedure usqrt with
  Global => (In_Out => (X86.Memory, X86.Exit_Called, X86.RAX,  X86.RCX,
                        X86.RDX,  X86.RSP, X86.RDI,  X86.R8),
            Input  => (X86.RSI),
            Output => (X86.ZeroFlag, X86.SignFlag, X86.CarryFlag, X86.OverflowFlag)),
     Pre => (not X86.InRange64(X86.RSI,X86.RSP-7,15)),

             --(X86.RSP <= (X86.RSI - 8)) or (X86.RSP >= (X86.RSI + 8)))),
	Post => (X86.RSP = (X86.RSP'Old + 8)) and
		(X86.Memory(X86.RSP'Old) = X86.Memory'Old(X86.RSP'Old)) and
		(X86.Memory(X86.RSP'Old + 1) = X86.Memory'Old(X86.RSP'Old + 1)) and
		(X86.Memory(X86.RSP'Old + 2) = X86.Memory'Old(X86.RSP'Old + 2)) and
		(X86.Memory(X86.RSP'Old + 3) = X86.Memory'Old(X86.RSP'Old + 3)) and
		(X86.Memory(X86.RSP'Old + 4) = X86.Memory'Old(X86.RSP'Old + 4)) and
		(X86.Memory(X86.RSP'Old + 5) = X86.Memory'Old(X86.RSP'Old + 5)) and
		(X86.Memory(X86.RSP'Old + 6) = X86.Memory'Old(X86.RSP'Old + 6)) and
                (X86.Memory(X86.RSP'Old + 7) = X86.Memory'Old(X86.RSP'Old + 7)) and
                (for all i in Unsigned64 =>
                   (if (not X86.InRange64(i, X86.RSI, 8)) then
                      (X86.Memory(i) = X86.Memory'Old(i))));

end basicmath_small;
