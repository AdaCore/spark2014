Package body basicmath_small
with SPARK_Mode
is

   procedure printf is
   begin
      X86.RSP := X86.RSP + 8;
   end printf;

   procedure puts is
   begin
      X86.RSP := X86.RSP + 8;
   end puts;

   procedure putchar is
   begin
      X86.RSP := X86.RSP + 8;
   end putchar;

   procedure SolveCubic is
   begin
      X86.RSP := X86.RSP + 8;
   end SolveCubic;

   procedure loop_1 is
   begin
      while (not X86.ZeroFlag) and (X86.SignFlag = X86.OverflowFlag) loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);

         -- 400712  movsd   xmm0, qword ptr [rbp+0]
         X86.XMM0 :=  X86.ReadMem64(X86.RBP);

         -- 400717  mov     edi, offset asc_40112B; " %f"
         X86.Write_EDI(16#40112B#);

         -- 40071c  mov     eax, 1
         X86.Write_EAX(16#1#);

         -- 400721  add     ebx, 1
         X86.Write_EBX(X86.EBX + 1);

         -- 400724  add     rbp, 8
         X86.RBP := X86.RBP + 8;

         -- 400728  call    _printf
--           X86.WriteMem64(X86.RSP - 8, 16#40072d#);
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 40072d  cmp     [rsp+98h+var_6C], ebx
         X86.ZeroFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) = 0);
         X86.SignFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) > X86.MaxSignedInt32);
         X86.CarryFlag := (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) < X86.EBX );
         X86.OverflowFlag := ((X86.SignFlag and then
                                (X86.EBX > X86.MaxSignedInt32) and then
                                (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) <= X86.MaxSignedInt32)) or ((not X86.SignFlag) and then
                                      (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) > X86.MaxSignedInt32) and then
                                    (X86.EBX <= X86.MaxSignedInt32)));

         -- 400731  jg      short loc_400712
      end loop;
   end loop_1;

   procedure loop_2 is
   begin
      while ((not X86.ZeroFlag) and (X86.SignFlag = X86.OverflowFlag)) loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);

         -- 400712  movsd   xmm0, qword ptr [rbp+0]
         X86.XMM0 :=  X86.ReadMem64(X86.RBP);

         -- 400717  mov     edi, offset asc_40112B; " %f"
         X86.Write_EDI(16#40112B#);

         -- 40071c  mov     eax, 1
         X86.Write_EAX(16#1#);

         -- 400721  add     ebx, 1
         X86.Write_EBX(X86.EBX + 1);

         -- 400724  add     rbp, 8
         X86.RBP := X86.RBP + 8;

         -- 400728  call    _printf
--           X86.WriteMem64(X86.RSP - 8, 16#4007a2#);
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 40072d  cmp     [rsp+98h+var_6C], ebx
         X86.ZeroFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) = 0);
         X86.SignFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) > X86.MaxSignedInt32);
         X86.CarryFlag := (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) < X86.EBX );
         X86.OverflowFlag := ((X86.SignFlag and then
                                (X86.EBX > X86.MaxSignedInt32) and then
                                (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) <= X86.MaxSignedInt32)) or ((not X86.SignFlag) and then
                                      (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) > X86.MaxSignedInt32) and then
                                    (X86.EBX <= X86.MaxSignedInt32)));

         -- 400731  jg      short loc_400712
      end loop;
   end loop_2;

   procedure loop_3 is
   begin
      while ((not X86.ZeroFlag) and (X86.SignFlag = X86.OverflowFlag))  loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);

         -- 400712  movsd   xmm0, qword ptr [rbp+0]
         X86.XMM0 :=  X86.ReadMem64(X86.RBP);

         -- 400717  mov     edi, offset asc_40112B; " %f"
         X86.Write_EDI(16#40112B#);

         -- 40071c  mov     eax, 1
         X86.Write_EAX(16#1#);

         -- 400721  add     ebx, 1
         X86.Write_EBX(X86.EBX + 1);

         -- 400724  add     rbp, 8
         X86.RBP := X86.RBP + 8;

         -- 400728  call    _printf
--           X86.WriteMem64(X86.RSP - 8, 16#400817#);
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 40072d  cmp     [rsp+98h+var_6C], ebx
         X86.ZeroFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) = 0);
         X86.SignFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) > X86.MaxSignedInt32);
         X86.CarryFlag := (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) < X86.EBX );
         X86.OverflowFlag := ((X86.SignFlag and then
                                (X86.EBX > X86.MaxSignedInt32) and then
                                (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) <= X86.MaxSignedInt32)) or ((not X86.SignFlag) and then
                                      (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) > X86.MaxSignedInt32) and then
                                    (X86.EBX <= X86.MaxSignedInt32)));

         -- 400731  jg      short loc_400712
      end loop;
   end loop_3;

   procedure loop_4 is
   begin
      while ((not X86.ZeroFlag) and (X86.SignFlag = X86.OverflowFlag)) loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);


         -- 400712  movsd   xmm0, qword ptr [rbp+0]
         X86.XMM0 :=  X86.ReadMem64(X86.RBP);

         -- 400717  mov     edi, offset asc_40112B; " %f"
         X86.Write_EDI(16#40112B#);

         -- 40071c  mov     eax, 1
         X86.Write_EAX(16#1#);

         -- 400721  add     ebx, 1
         X86.Write_EBX(X86.EBX + 1);

         -- 400724  add     rbp, 8
         X86.RBP := X86.RBP + 8;

         -- 400728  call    _printf
--           X86.WriteMem64(X86.RSP - 8, 16#400888#);
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 40072d  cmp     [rsp+98h+var_6C], ebx
         X86.ZeroFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) = 0);
         X86.SignFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) > X86.MaxSignedInt32);
         X86.CarryFlag := (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) < X86.EBX );
         X86.OverflowFlag := ((X86.SignFlag and then
                                (X86.EBX > X86.MaxSignedInt32) and then
                                (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) <= X86.MaxSignedInt32)) or ((not X86.SignFlag) and then
                                      (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) > X86.MaxSignedInt32) and then
                                    (X86.EBX <= X86.MaxSignedInt32)));

         -- 400731  jg      short loc_400712
      end loop;
   end loop_4;

   procedure loop_5d is
   begin
      while ((not X86.ZeroFlag) and (X86.SignFlag = X86.OverflowFlag)) loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);

         -- 400931  movsd   xmm0, qword ptr [rbp+0]
         X86.XMM0 :=  X86.ReadMem64(X86.RBP);

         -- 400936  mov     edi, offset asc_40112B; " %f"
         X86.Write_EDI(16#40112B#);

         -- 40071c  mov     eax, 1
         X86.Write_EAX(16#1#);

         -- 400721  add     ebx, 1
         X86.Write_EBX(X86.EBX + 1);

         -- 400724  add     rbp, 8
         X86.RBP := X86.RBP + 8;

         -- 400728  call    _printf
--           X86.WriteMem64(X86.RSP - 8, 16#40094c#);
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 40072d  cmp     [rsp+98h+var_6C], ebx
         X86.ZeroFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) = 0);
         X86.SignFlag := ((X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) - X86.EBX) > X86.MaxSignedInt32);
         X86.CarryFlag := (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) < X86.EBX );
         X86.OverflowFlag := ((X86.SignFlag and then
                                (X86.EBX > X86.MaxSignedInt32) and then
                                (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) <= X86.MaxSignedInt32)) or ((not X86.SignFlag) and then
                                      (X86.ReadMem32(X86.RSP + 16#98# - 16#6C#) > X86.MaxSignedInt32) and then
                                    (X86.EBX <= X86.MaxSignedInt32)));

         -- 400731  jg      short loc_400712
      end loop;
   end loop_5d;

   procedure loop_5c is
   begin
      loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);
         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 (if ((i /= X86.RSP) and (i /= X86.RSP + 1) and
                                    (i /= X86.RSP + 2) and (i /= X86.RSP + 3) and
                                    (i /= X86.RSP + 4) and (i /= X86.RSP + 5) and
                                    (i /= X86.RSP + 6) and (i /= X86.RSP + 7)) then
                                    (X86.Memory(i) = X86.Memory'Loop_Entry(i))));
         -- 4008f0  lea     rsi, [rsp+98h+var_58]
         X86.RSI := X86.RSP + 16#98# - 16#58#;

         -- 4008f5  lea     rdi, [rsp+98h+var_6C]
         X86.RDI := X86.RSP + 16#98# - 16#6C#;

         -- 4008fa  xor     ebx, ebx
         X86.Write_EBX(0);

         -- 4008fc  movsd   xmm3, [rsp+98h+var_98]
         X86.XMM3 :=  X86.ReadMem64(X86.RSP) ;

         -- 400901  lea     rbp, [rsp+98h+var_58]
         X86.RBP := X86.RSP + 16#98# - 16#58#;

         -- 400906  movsd   xmm2, [rsp+98h+var_90]
         X86.XMM2 :=  X86.ReadMem64(X86.RSP + 16#98# - 16#90#);

         -- 40090c  movsd   xmm1, [rsp+98h+var_88]
         X86.XMM1 :=  X86.ReadMem64(X86.RSP + 16#98# - 16#88#);

         -- 400912  movsd   xmm0, [rsp+98h+var_80]
         X86.XMM0 :=  X86.ReadMem64(X86.RSP + 16#98# - 16#80#);

         -- 400918  call    SolveCubic
--           X86.WriteMem64(X86.RSP - 8, 16#40091d# );
         X86.RSP := X86.RSP - 8;
         SolveCubic ;

         -- 40091d  xor     eax, eax
         X86.Write_EAX(0);

         -- 40091f  mov     edi, offset format; "Solutions:"
         X86.Write_EDI(4198688);

         -- 400924  call    _printf
--           X86.WriteMem64(X86.RSP - 8, 16#400929# );
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 400929  mov     eax, [rsp+98h+var_6C]
         X86.Write_EAX(X86.ReadMem32(X86.RSP + 16#98# - 16#6C#));

         -- 40092d  test    eax, eax
         X86.ZeroFlag := (X86.EAX = 0);
         X86.SignFlag := (X86.EAX > X86.MaxSignedInt32);
         X86.CarryFlag := False;
         X86.OverflowFlag := False;

         -- 40092f  jle     short loc_400952
         loop_5d;

         -- 400952  mov     edi, 0Ah        ; c
         X86.Write_EDI(16#A#);

         -- 400957  call    _putchar
--           X86.WriteMem64(X86.RSP - 8, 16#40095c# );
         X86.RSP := X86.RSP - 8;
         putchar ;

         -- 40095c  movsd   xmm4, [rsp+98h+var_98]
         X86.XMM4 :=  X86.ReadMem64(X86.RSP) ;

         -- 400961  sub     r12d, 1
         X86.R12 := ( X86.R12 - 16#1#);

         --FIXME: where is the zero flag set?
         X86.ZeroFlag := X86.R12 = 0;

         -- 400965  subsd   xmm4, cs:qword_401170
         X86.XMM4 := (X86.XMM4 - X86.ReadMem64(16#401170#));

         -- 40096d  movsd   [rsp+98h+var_98], xmm4
         X86.WriteMem64(X86.RSP, X86.XMM4);

         -- 400972  jnz     loc_4008F0
         exit when (X86.ZeroFlag);
      end loop;
   end loop_5c;

   procedure loop_5b is
   begin
      loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);
         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 (if ((i /= X86.RSP) and (i /= X86.RSP + 1) and
                                    (i /= X86.RSP + 2) and (i /= X86.RSP + 3) and
                                    (i /= X86.RSP + 4) and (i /= X86.RSP + 5) and
                                    (i /= X86.RSP + 6) and (i /= X86.RSP + 7) and
                                    (i /= X86.RSP + 8) and (i /= X86.RSP + 9) and
                                    (i /= X86.RSP + 10) and (i /= X86.RSP + 11) and
                                    (i /= X86.RSP + 12) and (i /= X86.RSP + 13) and
                                    (i /= X86.RSP + 14) and (i /= X86.RSP + 15)) then
                                    (X86.Memory(i) = X86.Memory'Loop_Entry(i))));
         -- 4008d8  movsd   xmm7, cs:qword_401158
         X86.XMM7 := X86.ReadMem64(16#401158#) ;

         -- 4008e0  mov     r12d, 0Ah
         X86.R12 := 16#A#;

         -- 4008e6  movsd   [rsp+98h+var_98], xmm7
         X86.WriteMem64(X86.RSP, X86.XMM7);

         loop_5c;

         -- 400978  movsd   xmm5, cs:qword_4011C8
         X86.XMM5 := X86.ReadMem64(Unsigned64( 16#4011c8# )) ;

         -- 400980  sub     r13d, 1
         X86.R13 := (X86.R13 - 16#1#);

         --FIXME: where is the zero flag set?
         X86.ZeroFlag := X86.R13 = 0;

         -- 400984  addsd   xmm5, [rsp+98h+var_90]
         X86.XMM5 := (X86.XMM5 + X86.ReadMem64(X86.RSP + 16#98# - 16#90#));

         -- 40098a  movsd   [rsp+98h+var_90], xmm5
         X86.WriteMem64(X86.RSP + 16#98# - 16#90#, X86.XMM5);

         -- 400990  jnz     loc_4008D8
         exit when (X86.ZeroFlag);
      end loop;
   end loop_5b;

   procedure loop_5a is
   begin
      loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);
         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 (if ((i /= X86.RSP) and (i /= X86.RSP + 1) and
                                    (i /= X86.RSP + 2) and (i /= X86.RSP + 3) and
                                    (i /= X86.RSP + 4) and (i /= X86.RSP + 5) and
                                    (i /= X86.RSP + 6) and (i /= X86.RSP + 7) and
                                    (i /= X86.RSP + 8) and (i /= X86.RSP + 9) and
                                    (i /= X86.RSP + 10) and (i /= X86.RSP + 11) and
                                    (i /= X86.RSP + 12) and (i /= X86.RSP + 13) and
                                    (i /= X86.RSP + 14) and (i /= X86.RSP + 15) and
                                    (i /= X86.RSP + 16) and (i /= X86.RSP + 17) and
                                    (i /= X86.RSP + 18) and (i /= X86.RSP + 19) and
                                    (i /= X86.RSP + 20) and (i /= X86.RSP + 21) and
                                    (i /= X86.RSP + 22) and (i /= X86.RSP + 23)) then
                                    (X86.Memory(i) = X86.Memory'Loop_Entry(i))));
         -- 4008c0  movsd   xmm7, cs:qword_401160
         X86.XMM7 :=  X86.ReadMem64(16#401160#) ;

         -- 4008c8  mov     r13d, 14h
         X86.R13 := 16#14#;

         -- 4008ce  movsd   [rsp+98h+var_90], xmm7
         X86.WriteMem64(X86.RSP + 16#98# - 16#90#, X86.XMM7);

         loop_5b;

         -- 400996  movsd   xmm6, [rsp+98h+var_88]
         X86.XMM6 := X86.ReadMem64(X86.RSP + 16#98# - 16#88#);

         -- 40099c  sub     r14d, 1
         X86.R14 := (X86.R14 - 16#1#);

         --FIXME: where is the zero flag set?
         X86.ZeroFlag := X86.R14 = 0;

         -- 4009a0  subsd   xmm6, cs:qword_401170
         X86.XMM6 := (X86.XMM6 - X86.ReadMem64(16#401170#));

         -- 4009a8  movsd   [rsp+98h+var_88], xmm6
         X86.WriteMem64(X86.RSP + 16#98# - 16#88#, X86.XMM6);

         -- 4009ae  jnz     loc_4008C0
         exit when (X86.ZeroFlag);
      end loop;
   end loop_5a;

   procedure loop_5 is
   begin
      loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);
         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 (if ((i /= X86.RSP) and (i /= X86.RSP + 1) and
                                    (i /= X86.RSP + 2) and (i /= X86.RSP + 3) and
                                    (i /= X86.RSP + 4) and (i /= X86.RSP + 5) and
                                    (i /= X86.RSP + 6) and (i /= X86.RSP + 7) and
                                    (i /= X86.RSP + 8) and (i /= X86.RSP + 9) and
                                    (i /= X86.RSP + 10) and (i /= X86.RSP + 11) and
                                    (i /= X86.RSP + 12) and (i /= X86.RSP + 13) and
                                    (i /= X86.RSP + 14) and (i /= X86.RSP + 15) and
                                    (i /= X86.RSP + 16) and (i /= X86.RSP + 17) and
                                    (i /= X86.RSP + 18) and (i /= X86.RSP + 19) and
                                    (i /= X86.RSP + 20) and (i /= X86.RSP + 21) and
                                    (i /= X86.RSP + 22) and (i /= X86.RSP + 23) and
                                    (i /= X86.RSP + 24) and (i /= X86.RSP + 25) and
                                    (i /= X86.RSP + 26) and (i /= X86.RSP + 27) and
                                    (i /= X86.RSP + 28) and (i /= X86.RSP + 29) and
                                    (i /= X86.RSP + 30) and (i /= X86.RSP + 31)) then
                                    (X86.Memory(i) = X86.Memory'Loop_Entry(i))));
         -- 4008ac  movsd   xmm7, cs:qword_401168
         X86.XMM7 :=  X86.ReadMem64(16#401168#);

         -- 4008b4  mov     r14d, 0Ah
         X86.R14 := 16#A#;

         -- 4008ba  movsd   [rsp+98h+var_88], xmm7
         X86.WriteMem64(X86.RSP + 16#98# - 16#88#, X86.XMM7);

         loop_5a;

         -- 4009b4  movsd   xmm7, cs:qword_401170
         X86.XMM7 :=  X86.ReadMem64(Unsigned64( 16#401170# )) ;

         -- 4009bc  sub     r15d, 1
         X86.R15 := (X86.R15 - 16#1#);

         --FIXME: where is the zero flag set?
         X86.ZeroFlag := X86.R15 = 0;

         -- 4009c0  addsd   xmm7, [rsp+98h+var_80]
         X86.XMM7 := (X86.XMM7 + X86.ReadMem64(X86.RSP + 16#98# - 16#80#));

         -- 4009c6  movsd   [rsp+98h+var_80], xmm7
         X86.WriteMem64(X86.RSP + 16#98# - 16#80#, X86.XMM7);

         -- 4009cc  jnz     loc_4008AC
         exit when (X86.ZeroFlag);
      end loop;
   end loop_5;

   procedure loop_6 is
   begin
      loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);
         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 (if ((i /=  X86.RSP + 16#98# - 16#68#) and
                                    (i /= X86.RSP + 16#98# - 16#68# + 1) and
                                    (i /= X86.RSP + 16#98# - 16#68# + 2) and
                                    (i /= X86.RSP + 16#98# - 16#68# + 3) and
                                    (i /= X86.RSP + 16#98# - 16#68# + 4) and
                                    (i /= X86.RSP + 16#98# - 16#68# + 5) and
                                    (i /= X86.RSP + 16#98# - 16#68# + 6) and
                                    (i /= X86.RSP + 16#98# - 16#68# + 7)) then
                                    (X86.Memory(i) = X86.Memory'Loop_Entry(i))));

         -- 4009de  lea     rsi, [rsp+98h+var_68]
         X86.RSI := (X86.RSP + 16#98# - 16#68#);

         -- 4009e3  mov     rdi, rbx
         X86.RDI := X86.RBX ;

         -- 4009e6  call    usqrt
--           X86.WriteMem64(X86.RSP - 8, 16#4009eb#);
         X86.RSP := X86.RSP - 8;
         usqrt;

         -- 4009eb  mov     edx, [rsp+98h+var_68]
         X86.Write_EDX(X86.ReadMem32(X86.RSP + 16#98# - 16#68#));

         -- 4009ef  mov     esi, ebx
         X86.Write_ESI(X86.EBX);

         -- 4009f1  xor     eax, eax
         X86.Write_EAX(0);

         -- 4009f3  mov     edi, offset aSqrt3d2d; "sqrt(%3d) = %2d\n"
         X86.Write_EDI(4198703);

         -- 4009f8  add     rbx, 1
         X86.RBX := (X86.RBX + 16#1#);

         -- 4009fc  call    _printf
--           X86.WriteMem64(X86.RSP - 8, 16#400a01#);
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 400a01  cmp     rbx, 3E9h
         X86.ZeroFlag := ((X86.RBX - 16#3E9#) = 0);
         X86.SignFlag := ((X86.RBX - 16#3E9#) > X86.MaxSignedInt64);
         X86.CarryFlag := (X86.RBX < 16#3E9#);
         X86.OverflowFlag := ((X86.SignFlag and then
                                (16#3E9#  > X86.MaxSignedInt64) and then
                                (X86.RBX  <= X86.MaxSignedInt64)) or ((not X86.SignFlag) and then
                                  (X86.RBX  > X86.MaxSignedInt64) and then
                                  (16#3E9# <= X86.MaxSignedInt64)));

         -- 400a08  jnz     short loc_4009DE
         exit when (X86.ZeroFlag);
      end loop;
   end loop_6;

   procedure loop_7 is
   begin
      loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);
         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 (if ((i /= X86.RSP) and (i /= X86.RSP + 1) and
                                    (i /= X86.RSP + 2) and (i /= X86.RSP + 3) and
                                    (i /= X86.RSP + 4) and (i /= X86.RSP + 5) and
                                    (i /= X86.RSP + 6) and (i /= X86.RSP + 7)) then
                                    (X86.Memory(i) = X86.Memory'Loop_Entry(i))));

         -- 400a40  movsd   xmm1, cs:qword_4011D0
         X86.XMM1 :=  X86.ReadMem64(16#4011d0#) ;

         -- 400a48  movapd  xmm0, xmm2
         X86.XMM0 :=  X86.XMM2 ;

         -- 400a4c  mov     edi, offset a3_0fDegrees_12; "%3.0f degrees = %.12f radians\n"
         X86.Write_EDI(4198624);

         -- 400a51  mov     eax, 2
         X86.Write_EAX(16#2#);

         -- 400a56  movsd   [rsp+98h+var_98], xmm2
         X86.WriteMem64(X86.RSP, X86.XMM2);

         -- 400a5b  mulsd   xmm1, xmm2
         X86.XMM1 := (X86.XMM1 * X86.XMM2);

         -- 400a5f  divsd   xmm1, cs:qword_4011D8
         X86.XMM1 := X86.SafeDivision64(X86.XMM1, X86.ReadMem64(16#4011d8#));

         -- 400a67  call    _printf
--           X86.WriteMem64(X86.RSP - 8, 16#400a6c# );
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 400a6c  movsd   xmm2, [rsp+98h+var_98]
         X86.XMM2 := X86.ReadMem64(X86.RSP);

         -- 400a71  sub     ebx, 1
         X86.Write_EBX(X86.EBX - 16#1#);

         --FIXME: where is the zero flag set?
         X86.ZeroFlag := X86.EBX = 0;

         -- 400a74  addsd   xmm2, cs:qword_401170
         X86.XMM2 := (X86.XMM2 + X86.ReadMem64(16#401170#));

         -- 400a7c  jnz     short loc_400A40
         exit when (X86.ZeroFlag);
      end loop;
   end loop_7;

   procedure loop_8 is
   begin
      loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);
         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 (if ((i /= X86.RSP) and (i /= X86.RSP + 1) and
                                    (i /= X86.RSP + 2) and (i /= X86.RSP + 3) and
                                    (i /= X86.RSP + 4) and (i /= X86.RSP + 5) and
                                    (i /= X86.RSP + 6) and (i /= X86.RSP + 7)) then
                                    (X86.Memory(i) = X86.Memory'Loop_Entry(i))));
         -- 400a91  movsd   xmm1, cs:qword_4011D8
         X86.XMM1 :=  X86.ReadMem64(Unsigned64( 16#4011d8# )) ;

         -- 400a99  movapd  xmm0, xmm2
         X86.XMM0 :=  X86.XMM2 ;

         -- 400a9d  mov     edi, offset a_12fRadians3_0; "%.12f radians = %3.0f degrees\n"
         X86.Write_EDI(4198656);

         -- 400aa2  mov     eax, 2
         X86.Write_EAX(16#2#);

         -- 400aa7  movsd   [rsp+98h+var_98], xmm2
         X86.WriteMem64(X86.RSP, X86.XMM2);

         -- 400aac  mulsd   xmm1, xmm2
         X86.XMM1 := ( X86.XMM1  *  X86.XMM2 );

         -- 400ab0  divsd   xmm1, cs:qword_4011D0
         X86.XMM1 := X86.SafeDivision64(X86.XMM1, X86.ReadMem64(16#4011d0#));

         -- 400ab8  call    _printf
--           X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#400abd# );
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 400abd  movsd   xmm2, [rsp+98h+var_98]
         X86.XMM2 := X86.ReadMem64(X86.RSP) ;

         -- 400ac2  sub     ebx, 1
         X86.Write_EBX(X86.EBX - 16#1#);

         --FIXME: where is the zero flag set?
         X86.ZeroFlag := X86.EBX = 0;

         -- 400ac5  addsd   xmm2, cs:qword_4011E0
         X86.XMM2 := X86.XMM2 + X86.ReadMem64(16#4011e0#);

         -- 400acd  jnz     short loc_400A91
         exit when (X86.ZeroFlag);
      end loop;
   end loop_8;

   procedure main
   is
      SaveStackPtr : Unsigned64 := X86.RSP with Ghost;
      ra0 : Unsigned8 := X86.ReadMem8(X86.RSP) with Ghost;
      ra1 : Unsigned8 := X86.ReadMem8(X86.RSP + 1) with Ghost;
      ra2 : Unsigned8 := X86.ReadMem8(X86.RSP + 2) with Ghost;
      ra3 : Unsigned8 := X86.ReadMem8(X86.RSP + 3) with Ghost;
      ra4 : Unsigned8 := X86.ReadMem8(X86.RSP + 4) with Ghost;
      ra5 : Unsigned8 := X86.ReadMem8(X86.RSP + 5) with Ghost;
      ra6 : Unsigned8 := X86.ReadMem8(X86.RSP + 6) with Ghost;
      ra7 : Unsigned8 := X86.ReadMem8(X86.RSP + 7) with Ghost;
      SaveRBX : Unsigned64 := X86.RBX with Ghost;
      SaveRBP : Unsigned64 := X86.RBP with Ghost;
      SaveR12 : Unsigned64 := X86.R12 with Ghost;
      SaveR13 : Unsigned64 := X86.R13 with Ghost;
      SaveR14 : Unsigned64 := X86.R14 with Ghost;
      SaveR15 : Unsigned64 := X86.R15 with Ghost;
   begin

      pragma Assume(X86.RSP = X86.DummyRSP);

      -- 4006b0  push    r15
      X86.WriteMem64(Unsigned64( X86.RSP -8 ), Unsigned64( X86.R15 ));
      X86.RSP := ( X86.RSP  -  8 );

      -- 4006b2  push    r14
      X86.WriteMem64(Unsigned64( X86.RSP -8 ), Unsigned64( X86.R14 ));
      X86.RSP := ( X86.RSP  -  8 );

      -- 4006b4  mov     edi, offset s   ; "********* CUBIC FUNCTIONS ***********"
      X86.Write_EDI( 4198504 );

      -- 4006b9  push    r13
      X86.WriteMem64(Unsigned64( X86.RSP -8 ), Unsigned64( X86.R13 ));
      X86.RSP := ( X86.RSP  -  8 );

      -- 4006bb  push    r12
      X86.WriteMem64(Unsigned64( X86.RSP -8 ), Unsigned64( X86.R12 ));
      X86.RSP := ( X86.RSP  -  8 );

      -- 4006bd  push    rbp
      X86.WriteMem64(Unsigned64( X86.RSP -8 ), Unsigned64( X86.RBP ));
      X86.RSP := ( X86.RSP  -  8 );

      -- 4006be  push    rbx
      X86.WriteMem64(Unsigned64( X86.RSP -8 ), Unsigned64( X86.RBX ));
      X86.RSP := ( X86.RSP  -  8 );

      -- 4006bf  xor     ebx, ebx
      X86.Write_EBX( 0 );

      -- 4006c1  sub     rsp, 68h
      X86.RSP := ( X86.RSP  -  104 );

      -- 4006c5  call    _puts
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#4006ca# );
      X86.RSP := X86.RSP - 8;
      puts ;

      -- 4006ca  lea     rsi, [rsp+98h+var_58]
      X86.RSI := ( X86.RSP  +  64 );

      -- 4006cf  lea     rdi, [rsp+98h+var_6C]
      X86.RDI := ( X86.RSP  +  44 );

      -- 4006d4  lea     rbp, [rsp+98h+var_58]
      X86.RBP := ( X86.RSP  +  64 );

      -- 4006d9  movsd   xmm3, cs:qword_401178
      X86.XMM3 :=  X86.ReadMem64(Unsigned64( 16#401178# )) ;

      -- 4006e1  movsd   xmm2, cs:qword_401180
      X86.XMM2 :=  X86.ReadMem64(Unsigned64( 16#401180# )) ;

      -- 4006e9  movsd   xmm1, cs:qword_401188
      X86.XMM1 :=  X86.ReadMem64(Unsigned64( 16#401188# )) ;

      -- 4006f1  movsd   xmm0, cs:qword_401170
      X86.XMM0 :=  X86.ReadMem64(Unsigned64( 16#401170# )) ;

      -- 4006f9  call    SolveCubic
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#4006fe# );
      X86.RSP := X86.RSP - 8;
      SolveCubic ;


      -- 4006fe  mov     edi, offset format; "Solutions:"
      X86.Write_EDI( 4198688 );

      -- 400703  xor     eax, eax
      X86.Write_EAX( 0 );

      -- 400705  call    _printf
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#40070a# );
      X86.RSP := X86.RSP - 8;
      printf;

      -- 40070a  mov     edi, [rsp+98h+var_6C]
      X86.Write_EDI( X86.ReadMem32(Unsigned64(  (X86.ESP+44 ))) );

      -- 40070e  test    edi, edi
      X86.ZeroFlag := (( X86.EDI  and  X86.EDI ) = 0);
      X86.SignFlag := (( X86.EDI  and  X86.EDI ) > X86.MaxSignedInt32);
      X86.CarryFlag := False;
      X86.OverflowFlag := False;

      -- 400710  jle     short loc_400733
      loop_1;

      -- 400733  mov     edi, 0Ah        ; c
      X86.Write_EDI( 10 );

      -- 400738  xor     ebx, ebx
      X86.Write_EBX( 0 );

      -- 40073a  lea     rbp, [rsp+98h+var_58]
      X86.RBP := ( X86.RSP  +  64 );

      -- 40073f  call    _putchar
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#400744# );
      X86.RSP := X86.RSP - 8;
      putchar ;

      -- 400744  lea     rsi, [rsp+98h+var_58]
      X86.RSI := ( X86.RSP  +  64 );

      -- 400749  lea     rdi, [rsp+98h+var_6C]
      X86.RDI := ( X86.RSP  +  44 );

      -- 40074e  movsd   xmm3, cs:qword_401178
      X86.XMM3 :=  X86.ReadMem64(Unsigned64( 16#401178# )) ;

      -- 400756  movsd   xmm2, cs:qword_401190
      X86.XMM2 :=  X86.ReadMem64(Unsigned64( 16#401190# )) ;

      -- 40075e  movsd   xmm1, cs:qword_401198
      X86.XMM1 :=  X86.ReadMem64(Unsigned64( 16#401198# )) ;

      -- 400766  movsd   xmm0, cs:qword_401170
      X86.XMM0 :=  X86.ReadMem64(Unsigned64( 16#401170# )) ;

      -- 40076e  call    SolveCubic
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#400773# );
      X86.RSP := X86.RSP - 8;
      SolveCubic ;

      -- 400773  xor     eax, eax
      X86.Write_EAX( 0 );

      -- 400775  mov     edi, offset format; "Solutions:"
      X86.Write_EDI( 4198688 );

      -- 40077a  call    _printf
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#40077f# );
      X86.RSP := X86.RSP - 8;
      printf ;

      -- 40077f  mov     esi, [rsp+98h+var_6C]
      X86.Write_ESI( X86.ReadMem32(Unsigned64(  (X86.ESP+44 ))) );

      -- 400783  test    esi, esi
      X86.ZeroFlag := (( X86.ESI  and  X86.ESI ) = 0);
      X86.SignFlag := (( X86.ESI  and  X86.ESI ) > X86.MaxSignedInt32);
      X86.CarryFlag := False;
      X86.OverflowFlag := False;

      -- 400785  jle     short loc_4007A8
      loop_2;


      -- 4007a8  mov     edi, 0Ah        ; c
      X86.Write_EDI( 10 );

      -- 4007ad  xor     ebx, ebx
      X86.Write_EBX( 0 );

      -- 4007af  lea     rbp, [rsp+98h+var_58]
      X86.RBP := ( X86.RSP  +  64 );

      -- 4007b4  call    _putchar
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#4007b9# );
      X86.RSP := X86.RSP - 8;
      putchar;

      -- 4007b9  lea     rsi, [rsp+98h+var_58]
      X86.RSI := ( X86.RSP  +  64 );

      -- 4007be  lea     rdi, [rsp+98h+var_6C]
      X86.RDI := ( X86.RSP  +  44 );

      -- 4007c3  movsd   xmm3, cs:qword_4011A0
      X86.XMM3 :=  X86.ReadMem64(Unsigned64( 16#4011a0# )) ;

      -- 4007cb  movsd   xmm2, cs:qword_4011A8
      X86.XMM2 :=  X86.ReadMem64(Unsigned64( 16#4011a8# )) ;

      -- 4007d3  movsd   xmm1, cs:qword_4011B0
      X86.XMM1 :=  X86.ReadMem64(Unsigned64( 16#4011b0# )) ;

      -- 4007db  movsd   xmm0, cs:qword_401170
      X86.XMM0 :=  X86.ReadMem64(Unsigned64( 16#401170# )) ;

      -- 4007e3  call    SolveCubic
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#4007e8# );
      X86.RSP := X86.RSP - 8;
      SolveCubic ;

      -- 4007e8  xor     eax, eax
      X86.Write_EAX( 0 );

      -- 4007ea  mov     edi, offset format; "Solutions:"
      X86.Write_EDI( 4198688 );

      -- 4007ef  call    _printf
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#4007f4# );
      X86.RSP := X86.RSP - 8;
      printf ;

      -- 4007f4  mov     ecx, [rsp+98h+var_6C]
      X86.Write_ECX( X86.ReadMem32(Unsigned64(  (X86.ESP+44 ))) );

      -- 4007f8  test    ecx, ecx
      X86.ZeroFlag := (( X86.ECX  and  X86.ECX ) = 0);
      X86.SignFlag := (( X86.ECX  and  X86.ECX ) > X86.MaxSignedInt32);
      X86.CarryFlag := False;
      X86.OverflowFlag := False;

      -- 4007fa  jle     short loc_40081D
      loop_3;

      -- 40081d  mov     edi, 0Ah        ; c
      X86.Write_EDI( 10 );

      -- 400822  xor     ebx, ebx
      X86.Write_EBX( 0 );

      -- 400824  lea     rbp, [rsp+98h+var_58]
      X86.RBP := ( X86.RSP  +  64 );

      -- 400829  call    _putchar
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#40082e# );
      X86.RSP := X86.RSP - 8;
      putchar ;

      -- 40082e  movsd   xmm2, cs:qword_401170
      X86.XMM2 :=  X86.ReadMem64(Unsigned64( 16#401170# )) ;

      -- 400836  lea     rsi, [rsp+98h+var_58]
      X86.RSI := ( X86.RSP  +  64 );

      -- 40083b  lea     rdi, [rsp+98h+var_6C]
      X86.RDI := ( X86.RSP  +  44 );

      -- 400840  movsd   xmm3, cs:qword_4011B8
      X86.XMM3 :=  X86.ReadMem64(Unsigned64( 16#4011b8# )) ;

      -- 400848  movsd   xmm1, cs:qword_4011C0
      X86.XMM1 :=  X86.ReadMem64(Unsigned64( 16#4011c0# )) ;

      -- 400850  movapd  xmm0, xmm2
      X86.XMM0 :=  X86.XMM2 ;

      -- 400854  call    SolveCubic
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#400859# );
      X86.RSP := X86.RSP - 8;
      SolveCubic ;

      -- 400859  xor     eax, eax
      X86.Write_EAX( 0 );

      -- 40085b  mov     edi, offset format; "Solutions:"
      X86.Write_EDI( 4198688 );

      -- 400860  call    _printf
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#400865# );
      X86.RSP := X86.RSP - 8;
      printf ;

      -- 400865  mov     edx, [rsp+98h+var_6C]
      X86.Write_EDX( X86.ReadMem32(Unsigned64(  (X86.ESP+44 ))) );

      -- 400869  test    edx, edx
      X86.ZeroFlag := (( X86.EDX  and  X86.EDX ) = 0);
      X86.SignFlag := (( X86.EDX  and  X86.EDX ) > X86.MaxSignedInt32);
      X86.CarryFlag := False;
      X86.OverflowFlag := False;

      -- 40086b  jle     short loc_40088E
      loop_4;

      -- 40088e  mov     edi, 0Ah        ; c
      X86.Write_EDI( 10 );

      -- 400893  mov     r15d, 9
      X86.R15 :=  9 ;

      -- 400899  call    _putchar
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#40089e# );
      X86.RSP := X86.RSP - 8;
      putchar ;

      -- 40089e  movsd   xmm6, cs:qword_401170
      X86.XMM6 :=  X86.ReadMem64(Unsigned64( 16#401170# )) ;

      -- 4008a6  movsd   [rsp+98h+var_80], xmm6
      X86.WriteMem64(Unsigned64(  (X86.ESP+24 )), Unsigned64( X86.XMM6 ));

      loop_5;


      -- 4009d2  mov     edi, offset aIntegerSqrRoot; "********* INTEGER SQR ROOTS ***********"
      X86.Write_EDI( 4198544 );

      -- 4009d7  xor     ebx, ebx
      X86.Write_EBX( 0 );

      loop_6;

      -- 400a0a  lea     rsi, [rsp+98h+var_68]
      X86.RSI := ( X86.RSP  +  48 );

      -- 400a0f  mov     edi, 3FED0169h
      X86.Write_EDI( 1072497001 );

      -- 400a14  mov     bx, 169h
      X86.Write_BX( 361 );

      -- 400a18  call    usqrt
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#400a1d# );
      X86.RSP := X86.RSP - 8;
      usqrt ;

      -- 400a1d  mov     edx, [rsp+98h+var_68]
      X86.Write_EDX( X86.ReadMem32(Unsigned64(  (X86.ESP+48 ))) );

      -- 400a21  mov     esi, 3FED0169h
      X86.Write_ESI( 1072497001 );

      -- 400a26  mov     edi, offset aSqrtLxX; "\nsqrt(%lX) = %X\n"
      X86.Write_EDI( 4198720 );

      -- 400a2b  xor     eax, eax
      X86.Write_EAX( 0 );

      -- 400a2d  call    _printf
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#400a32# );
      X86.RSP := X86.RSP - 8;
      printf ;

      -- 400a32  mov     edi, offset aAngleConversio; "********* ANGLE CONVERSION ***********"
      X86.Write_EDI( 4198584 );

      -- 400a37  call    _puts
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#400a3c# );
      X86.RSP := X86.RSP - 8;
      puts ;

      -- 400a3c  pxor    xmm2, xmm2
      X86.XMM2 := ( X86.XMM2 xor X86.XMM2 );

      loop_7;

      -- 400a7e  mov     edi, (offset aSqrtLxX+10h); s
      X86.Write_EDI( 4198736 );

      -- 400a83  mov     ebx, 169h
      X86.Write_EBX( 361 );

      -- 400a88  call    _puts
--        X86.WriteMem64(Unsigned64(X86.RSP - 8), 16#400a8d# );
      X86.RSP := X86.RSP - 8;
      puts ;

      -- 400a8d  pxor    xmm2, xmm2
      X86.XMM2 := ( X86.XMM2 xor X86.XMM2 );

      loop_8;

      -- 400acf  add     rsp, 68h
      X86.RSP := ( X86.RSP  +  104 );

      -- 400ad3  xor     eax, eax
      X86.Write_EAX( 0 );

      -- 400ad5  pop     rbx
      X86.RBX :=  X86.ReadMem64(Unsigned64( X86.RSP + 0 )) ;
      X86.RSP := ( X86.RSP  +  8 );

      -- 400ad6  pop     rbp
      X86.RBP :=  X86.ReadMem64(Unsigned64( X86.RSP + 0 )) ;
      X86.RSP := ( X86.RSP  +  8 );

      -- 400ad7  pop     r12
      X86.R12 :=  X86.ReadMem64(Unsigned64( X86.RSP + 0 )) ;
      X86.RSP := ( X86.RSP  +  8 );

      -- 400ad9  pop     r13
      X86.R13 :=  X86.ReadMem64(Unsigned64( X86.RSP + 0 )) ;
      X86.RSP := ( X86.RSP  +  8 );

      -- 400adb  pop     r14
      X86.R14 :=  X86.ReadMem64(Unsigned64( X86.RSP + 0 )) ;
      X86.RSP := ( X86.RSP  +  8 );

      -- 400add  pop     r15
      X86.R15 :=  X86.ReadMem64(Unsigned64( X86.RSP + 0 )) ;
      X86.RSP := ( X86.RSP  +  8 );

      -- 400adf  retn
      X86.RSP := X86.RSP + 8;

      return;

   end main;

   procedure rad2deg
   is
   begin
      pragma Assume(X86.RSP = X86.DummyRSP);

      -- 400be0  mulsd   xmm0, cs:qword_4011D8
      X86.XMM0 := ( X86.XMM0  *  X86.ReadMem64(Unsigned64( 16#4011d8# )) );

      -- 400be8  divsd   xmm0, cs:qword_4011D0
      X86.XMM0 := X86.SafeDivision64( X86.XMM0, X86.ReadMem64(Unsigned64( 16#4011d0# )) );

      -- 400bf0  retn
      X86.RSP := X86.RSP + 8;
      return;

   end rad2deg;

   procedure deg2rad
   is
   begin
      pragma Assume(X86.RSP = X86.DummyRSP);

      -- 400c00  mulsd   xmm0, cs:qword_4011D0
      X86.XMM0 := ( X86.XMM0  *  X86.ReadMem64(Unsigned64( 16#4011d0# )) );

      -- 400c08  divsd   xmm0, cs:qword_4011D8
      X86.XMM0 := X86.SafeDivision64( X86.XMM0, X86.ReadMem64(Unsigned64( 16#4011d8# )) );

      -- 400c10  retn
      X86.RSP := X86.RSP + 8;
      return;

   end deg2rad;

   procedure usqrt_loop
   is
   begin
      pragma Assume(X86.RSP = X86.DummyRSP);
      loop
         pragma Loop_Invariant(X86.RSP = X86.RSP'Loop_Entry);
         -- 400fa0  mov     rcx, rdi
         X86.RCX :=  X86.RDI ;

         -- 400fa3  add     rax, rax
         X86.RAX := (X86.RAX + X86.RAX);

         -- 400fa6  shl     rdi, 2
         X86.RDI := Interfaces.Shift_Left(X86.RDI, 2);

         -- 400faa  and     ecx, 0C0000000h
         X86.Write_ECX(X86.ECX and 16#C0000000#);

         -- 400fb0  shr     rcx, 1Eh
         X86.RCX := Interfaces.Shift_Right(X86.RCX, 16#1E#);

         -- 400fb4  lea     rdx, [rcx+rdx*4]
         X86.RDX := X86.RCX + Interfaces.Shift_Left(X86.RDX, 2);

         -- 400fb8  lea     rcx, [rax+rax+1]
         X86.RCX := ( X86.RAX + (1 + X86.RAX));

         -- 400fbd  cmp     rdx, rcx
         X86.ZeroFlag := ((X86.RDX - X86.RCX ) = 0);
         X86.SignFlag := ((X86.RDX - X86.RCX ) > X86.MaxSignedInt64);
         X86.CarryFlag := (X86.RDX < X86.RCX );
         X86.OverflowFlag := ((X86.SignFlag and then
                                (X86.RCX  > X86.MaxSignedInt64) and then
                                (X86.RDX  <= X86.MaxSignedInt64)) or ((not X86.SignFlag) and then
                                  (X86.RDX  > X86.MaxSignedInt64) and then
                                  (X86.RCX  <= X86.MaxSignedInt64)));

         -- 400fc0  jb      short loc_400FC9
         if (not X86.CarryFlag) then

            -- 400fc2  sub     rdx, rcx
            X86.RDX := X86.RDX - X86.RCX;

            -- 400fc5  add     rax, 1
            X86.RAX := X86.RAX + 16#1#;
         end if;

         -- 400fc9  sub     r8d, 1
         X86.R8 := X86.R8 - 16#1#;

         -- 400fcd  jnz     short loc_400FA0
         exit when (X86.ZeroFlag);
      end loop;
   end usqrt_loop;

   procedure usqrt
   is
      SaveStackPtr : Unsigned64 := X86.RSP with Ghost;
      ra0 : Unsigned8 := X86.ReadMem8(X86.RSP) with Ghost;
      ra1 : Unsigned8 := X86.ReadMem8(X86.RSP + 1) with Ghost;
      ra2 : Unsigned8 := X86.ReadMem8(X86.RSP + 2) with Ghost;
      ra3 : Unsigned8 := X86.ReadMem8(X86.RSP + 3) with Ghost;
      ra4 : Unsigned8 := X86.ReadMem8(X86.RSP + 4) with Ghost;
      ra5 : Unsigned8 := X86.ReadMem8(X86.RSP + 5) with Ghost;
      ra6 : Unsigned8 := X86.ReadMem8(X86.RSP + 6) with Ghost;
      ra7 : Unsigned8 := X86.ReadMem8(X86.RSP + 7) with Ghost;

   begin

      pragma Assume(X86.RSP = X86.DummyRSP);

      -- 400f90  mov     r8d, 20h
      X86.R8 := 32 ;

      -- 400f96  xor     eax, eax
      X86.Write_EAX(0);

      -- 400f98  xor     edx, edx
      X86.Write_EDX(0);

      usqrt_loop;

      -- 400fcf  mov     [rsi], rax
      X86.WriteMem64(X86.RSI, X86.RAX);

      -- 400fd2  retn
      X86.RSP := X86.RSP + 8;
      return;

   end usqrt;


end basicmath_small;
