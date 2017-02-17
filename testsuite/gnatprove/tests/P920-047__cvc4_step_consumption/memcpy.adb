Package body memcpy
with SPARK_Mode
is


   procedure memcpy2
   is
      RDX_400586 : Unsigned64 := X86.RDX;
      RDI_400586 : Unsigned64 := X86.RDI;

   begin
      pragma Assume(X86.RSP = X86.DummyRSP);

      -- 400586  push    rbp
      X86.WriteMem64(( X86.RSP -8 ),  X86.RBP);
      X86.RSP := ( X86.RSP -  16#8# );

      -- 400587  mov     rbp, rsp
      X86.RBP :=  X86.RSP;

      -- 40058a  mov     [rbp+var_38], rdi
      X86.WriteMem64(( X86.RBP -56 ),  X86.RDI);

      -- 40058e  mov     [rbp+var_40], rsi
      X86.WriteMem64(( X86.RBP -64 ),  X86.RSI);

      -- 400592  mov     [rbp+var_48], rdx
      X86.WriteMem64(( X86.RBP -72 ),  X86.RDX);

      -- 400596  mov     rax, [rbp+var_38]
      X86.RAX :=  X86.ReadMem64(( X86.RBP -56 )) ;

      -- 40059a  and     eax, 7
      X86.Write_EAX(( X86.EAX and 16#7# ));

      -- 40059d  test    rax, rax
      X86.ZeroFlag := (( X86.RAX) = 0);
      X86.SignFlag := (( X86.RAX) > X86.MaxSignedInt64);
      X86.CarryFlag := false;
      X86.OverflowFlag := false;

      -- 4005a0  jnz     short loc_400615
      if not ( ( X86.RAX /=  0 ) or else  ( ( X86.ReadMem64(( X86.RBP -64 ))  and  16#7# )  /=  0 ) or else  ( ( X86.ReadMem64(( X86.RBP -72 ))  and  16#7# )  /=  0 ) ) then

         -- 4005ba  mov     rax, [rbp+var_38]
         X86.RAX :=  X86.ReadMem64(( X86.RBP -56 )) ;

         -- 4005be  mov     [rbp+var_10], rax
         X86.WriteMem64(( X86.RBP -16 ),  X86.RAX);

         -- 4005c2  mov     rax, [rbp+var_40]
         X86.RAX :=  X86.ReadMem64(( X86.RBP -64 )) ;

         -- 4005c6  mov     [rbp+var_18], rax
         X86.WriteMem64(( X86.RBP -24 ),  X86.RAX);

         -- 4005ca  mov     [rbp+var_8], 0
         X86.WriteMem64(( X86.RBP -8 ),  16#0# );

         --ZSTLoopProc_400605(RDX_400586, RDI_400586);

         -- 400613  jmp     short loc_400659
      else

         -- 400615  mov     rax, [rbp+var_38]
         X86.RAX :=  X86.ReadMem64(( X86.RBP -56 )) ;

         -- 400619  mov     [rbp+var_20], rax
         X86.WriteMem64(( X86.RBP -32 ),  X86.RAX);

         -- 40061d  mov     rax, [rbp+var_40]
         X86.RAX :=  X86.ReadMem64(( X86.RBP -64 )) ;

         -- 400621  mov     [rbp+var_28], rax
         X86.WriteMem64(( X86.RBP -40 ),  X86.RAX);

         -- 400625  mov     [rbp+var_8], 0
         X86.WriteMem64(( X86.RBP -8 ),  16#0# );

         --ZSTLoopProc_40064f(RDX_400586, RDI_400586);
      end if;

      -- 400659  mov     rax, [rbp+var_38]
      X86.RAX :=  X86.ReadMem64(( X86.RBP -56 )) ;

      -- 40065d  pop     rbp
      X86.RBP :=  X86.ReadMem64(( X86.RSP )) ;
      X86.RSP := ( X86.RSP +  16#8# );

      -- 40065e  retn
      X86.RSP := X86.RSP + 8;
      return;

   end memcpy2;


end memcpy;
