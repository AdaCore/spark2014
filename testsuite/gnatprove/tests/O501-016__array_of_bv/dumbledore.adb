
Package body Dumbledore
with SPARK_Mode
is

   procedure readString
   is
   begin

      --------------------------------------------------------------------------
      -- Step 1: Function prologue: Push previous base pointer on the stack and set up
      -- new base pointer to point (set base pointer equal to stack pointer)
      --------------------------------------------------------------------------
      --push   rbp
      X86.WriteMem64(X86.RSP -8, X86.RBP);
      X86.RSP := X86.RSP - 8;

      --mov    rbp,rsp
      X86.RBP := X86.RSP;

      --------------------------------------------------------------------------
      -- Step 2: Write contents of RSI register (X86.RSI) into memory location
      -- at RBP-16#10#
      -- note that memory is represented as an array of unsigned 8 bit integers
      -- note that the value stored in RSI is bounded by a precondition for this procedure
      --------------------------------------------------------------------------

      --mov    QWORD PTR [rbp-0x10],rsi
      X86.WriteMem64((X86.RBP - 16#10#), X86.RSI);

      pragma Assert(X86.ReadMem64(X86.RBP - 16#10#) = X86.RSI);

      --------------------------------------------------------------------------
      -- Step 3: Write the value 0 into memory at location RBP-16#34#
      --------------------------------------------------------------------------

      --mov    DWORD PTR [rbp-0x34],0x0
      X86.WriteMem32((X86.RBP - 16#34#), 0);

      pragma Assert(X86.ReadMem64(X86.RBP - 16#10#) = X86.RSI); --Assert fails

      --------------------------------------------------------------------------
      -- Step 4: Function epilogue, pop saved base pointer, and return stack pointer
      -- to pre-call location (as per standard calling conventions)
      --------------------------------------------------------------------------

      --pop    rbp
      X86.RBP := X86.ReadMem64(X86.RSP);
      X86.RSP := X86.RSP + 8;

      --ret
      X86.RSP := X86.RSP + 8;

      return;

   end readString;

end Dumbledore;
