Package body memcpy
with SPARK_Mode
is

   procedure printf is
   begin
      X86.RSP := X86.RSP + 8;
   end printf;

   procedure strlen is
   begin
      X86.RSP := X86.RSP + 8;
   end strlen;

   procedure memcpy2
   is
      SaveStackPtr : Unsigned64 := X86.RSP with Ghost;
      SaveMem: X86.Mem_Array := X86.Memory with Ghost;
      saved_ra : Unsigned64 := X86.ReadMem64(X86.RSP) with Ghost;
      ra0 : Unsigned8 := X86.ReadMem8(X86.RSP) with Ghost;
      ra1 : Unsigned8 := X86.ReadMem8(X86.RSP + 1) with Ghost;
      ra2 : Unsigned8 := X86.ReadMem8(X86.RSP + 2) with Ghost;
      ra3 : Unsigned8 := X86.ReadMem8(X86.RSP + 3) with Ghost;
      ra4 : Unsigned8 := X86.ReadMem8(X86.RSP + 4) with Ghost;
      ra5 : Unsigned8 := X86.ReadMem8(X86.RSP + 5) with Ghost;
      ra6 : Unsigned8 := X86.ReadMem8(X86.RSP + 6) with Ghost;
      ra7 : Unsigned8 := X86.ReadMem8(X86.RSP + 7) with Ghost;
      saved_rbp : Unsigned64 := X86.RBP with Ghost;
      saved_rdi : Unsigned64 := X86.RDI with Ghost;
      saved_rdx : Unsigned64 := X86.RDX with Ghost;
   begin
      pragma Assume(X86.RSP = X86.DummyRSP);

      -- 400586  push    rbp
      X86.WriteMem64(( X86.RSP -8 ),  X86.RBP );
      X86.RSP := ( X86.RSP  -  16#8# );

      -- 400587  mov     rbp, rsp
      X86.RBP :=  X86.RSP ;

      -- 40058a  mov     [rbp+var_38], rdi
      X86.WriteMem64(( X86.RBP -56 ),  X86.RDI );

      -- 40058e  mov     [rbp+var_40], rsi
      X86.WriteMem64(( X86.RBP -64 ),  X86.RSI );

      -- 400592  mov     [rbp+var_48], rdx
      X86.WriteMem64(( X86.RBP -72 ),  X86.RDX );

      -- 400596  mov     rax, [rbp+var_38]
      X86.RAX :=  X86.ReadMem64(( X86.RBP -56 )) ;

      -- 40059a  and     eax, 7
      X86.Write_EAX(( X86.EAX and 16#7# ));

      -- 40059d  test    rax, rax
      X86.ZeroFlag := (( X86.RAX ) = 0);
      X86.SignFlag := (( X86.RAX ) > X86.MaxSignedInt64);
      X86.CarryFlag := False;
      X86.OverflowFlag := False;

      -- 4005a0  jnz     short loc_400615
      if (X86.ZeroFlag) then

         -- 4005a2  mov     rax, [rbp+var_40]
         X86.RAX :=  X86.ReadMem64(( X86.RBP -64 )) ;

         -- 4005a6  and     eax, 7
         X86.Write_EAX(( X86.EAX and 16#7# ));

         -- 4005a9  test    rax, rax
         X86.ZeroFlag := (( X86.RAX ) = 0);
         X86.SignFlag := (( X86.RAX ) > X86.MaxSignedInt64);
         X86.CarryFlag := False;
         X86.OverflowFlag := False;

         -- 4005ac  jnz     short loc_400615
         if (X86.ZeroFlag) then

            -- 4005ae  mov     rax, [rbp+var_48]
            X86.RAX :=  X86.ReadMem64(( X86.RBP -72 )) ;

            -- 4005b2  and     eax, 7
            X86.Write_EAX(( X86.EAX and 16#7# ));

            -- 4005b5  test    rax, rax
            X86.ZeroFlag := (( X86.RAX ) = 0);
            X86.SignFlag := (( X86.RAX ) > X86.MaxSignedInt64);
            X86.CarryFlag := False;
            X86.OverflowFlag := False;

            -- 4005b8  jnz     short loc_400615
            if (X86.ZeroFlag) then

               -- 4005ba  mov     rax, [rbp+var_38]
               X86.RAX :=  X86.ReadMem64(( X86.RBP -56 )) ;

               -- 4005be  mov     [rbp+var_10], rax
               X86.WriteMem64(( X86.RBP -16 ),  X86.RAX );

               -- 4005c2  mov     rax, [rbp+var_40]
               X86.RAX :=  X86.ReadMem64(( X86.RBP -64 )) ;

               -- 4005c6  mov     [rbp+var_18], rax
               X86.WriteMem64(( X86.RBP -24 ),  X86.RAX );

               -- 4005ca  mov     [rbp+var_8], 0
               X86.WriteMem64(( X86.RBP -8 ),  16#0# );

               ZSTLoopProc_400605;

               -- 400613  jmp     short loc_400659
            else

               -- 400615  mov     rax, [rbp+var_38]
               X86.RAX :=  X86.ReadMem64(( X86.RBP -56 )) ;

               -- 400619  mov     [rbp+var_20], rax
               X86.WriteMem64(( X86.RBP -32 ),  X86.RAX );

               -- 40061d  mov     rax, [rbp+var_40]
               X86.RAX :=  X86.ReadMem64(( X86.RBP -64 )) ;

               -- 400621  mov     [rbp+var_28], rax
               X86.WriteMem64(( X86.RBP -40 ),  X86.RAX );

               -- 400625  mov     [rbp+var_8], 0
               X86.WriteMem64(( X86.RBP -8 ),  16#0# );

               --pragma Assert (X86.ReadMem64(X86.RSP) = saved_rbp);
               ZSTLoopProc_40064f;
               --pragma Assert (X86.ReadMem64(X86.RSP) = saved_rbp);

            end if;

            --		else
         end if;
         --	else
      end if;

      -- 400659  mov     rax, [rbp+var_38]
      X86.RAX :=  X86.ReadMem64(( X86.RBP -56 )) ;

      -- 40065d  pop     rbp
      X86.RBP :=  X86.ReadMem64(( X86.RSP )) ;
      X86.RSP := ( X86.RSP  +  16#8# );

      -- 40065e  retn
      X86.RSP := X86.RSP + 8;

      pragma Assert(X86.RSP = (SaveStackPtr + 8));
      pragma Assert((X86.Memory(SaveStackPtr) = SaveMem(SaveStackPtr)) and
        (X86.Memory(SaveStackPtr + 1) = SaveMem(SaveStackPtr + 1)) and
        (X86.Memory(SaveStackPtr + 2) = SaveMem(SaveStackPtr + 2)) and
        (X86.Memory(SaveStackPtr + 3) = SaveMem(SaveStackPtr + 3)) and
        (X86.Memory(SaveStackPtr + 4) = SaveMem(SaveStackPtr + 4)) and
        (X86.Memory(SaveStackPtr + 5) = SaveMem(SaveStackPtr + 5)) and
        (X86.Memory(SaveStackPtr + 6) = SaveMem(SaveStackPtr + 6)) and
        (X86.Memory(SaveStackPtr + 7) = SaveMem(SaveStackPtr + 7)));
      pragma Assert(X86.RBP = saved_rbp);
      pragma Assert(for all i in Unsigned64 =>
        (if (not X86.InRange64(i, saved_rdi, saved_rdx)) and  X86.InSafeRegion64(i, SaveStackPtr)
             then
           (X86.Memory(i) = SaveMem(i))));
      return;

   end memcpy2;

 procedure ZSTLoopProc_400605
   is
      saved_rbp_16 : Unsigned64 := X86.ReadMem64(X86.RBP -16) with Ghost;
      saved_rbp_72 : Unsigned64 := X86.ReadMem64(X86.RBP-72) with Ghost;
      tmp_register : Unsigned64 := X86.ReadMem64(X86.RBP - 8);

      saved_rbp : Unsigned64 := X86.ReadMem64(X86.RBP) with Ghost;
      saved_ra : Unsigned64 := X86.ReadMem64(X86.RSP+8) with Ghost;
      saved_mem: X86.Mem_Array := X86.Memory with Ghost;
   begin
      pragma Assume(X86.RSP = X86.DummyRSP+8);

      -- 400605  mov     rax, [rbp+var_48]
      loop
         -- RAX = len
         X86.RAX :=  X86.ReadMem64(( X86.RBP -72 )) ;

         -- RAX = len / sizeof(long)
         -- 400609  shr     rax, 3
         --X86.RAX := ( Interfaces.Shift_Right( X86.RAX  ,  16#3# ));
         X86.RAX := X86.RAX/8;

         -- [RBP - 8] = i
         -- 40060d  cmp     rax, [rbp+var_8]
--           X86.ZeroFlag := (( X86.RAX  -  X86.ReadMem64(( X86.RBP -8 )) ) = 0);
--           X86.SignFlag := (( X86.RAX  -  X86.ReadMem64(( X86.RBP -8 )) ) > X86.MaxSignedInt64);
--           X86.CarryFlag := ( X86.RAX  <  X86.ReadMem64(( X86.RBP -8 )) );
--           X86.OverflowFlag := ((X86.SignFlag and then ( X86.ReadMem64(( X86.RBP -8 ))  > X86.MaxSignedInt64) and then ( X86.RAX  <= X86.MaxSignedInt64)) or ((not X86.SignFlag) and then ( X86.RAX  > X86.MaxSignedInt64) and then ( X86.ReadMem64(( X86.RBP -8 ))  <= X86.MaxSignedInt64)));

         X86.ZeroFlag := (( X86.RAX  -  tmp_register) = 0);
         X86.SignFlag := (( X86.RAX  -  tmp_register ) > X86.MaxSignedInt64);
         X86.CarryFlag := ( X86.RAX  <  tmp_register );
         X86.OverflowFlag := ((X86.SignFlag and then ( tmp_register  > X86.MaxSignedInt64) and then ( X86.RAX  <= X86.MaxSignedInt64)) or ((not X86.SignFlag) and then ( X86.RAX  > X86.MaxSignedInt64) and then ( tmp_register  <= X86.MaxSignedInt64)));

         -- 400611  ja      short loc_4005D4
         exit when (X86.CarryFlag or X86.ZeroFlag);


         pragma Loop_Invariant(for all i in saved_rbp_16..(saved_rbp_16+saved_rbp_72-1) =>
                                 X86.InSafeRegion64(i,X86.RSP+8));

         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 (if (not X86.InRange64(i, saved_rbp_16, saved_rbp_72) and
                                    (not X86.InRange64(i, X86.RBP-8,8))) then
                                      (X86.Memory(i) = X86.Memory'Loop_Entry(i))));


         pragma Loop_Invariant(saved_rbp_16 = X86.ReadMem64(X86.RBP - 16));
         pragma Loop_Invariant(saved_rbp_72 = X86.ReadMem64(X86.RBP - 72));
         --pragma Loop_Invariant(X86.ReadMem64( X86.RBP -8 ) < saved_72);
         pragma Loop_Invariant(tmp_register < saved_rbp_72/8);


         pragma Loop_Invariant(X86.ReadMem64(X86.RBP) = saved_rbp);
         pragma Loop_Invariant(X86.ReadMem64(X86.RSP+8) = saved_ra);


         -- RAX = i
         -- 4005d4  mov     rax, [rbp+var_8]
         --X86.RAX :=  X86.ReadMem64(( X86.RBP -8 )) ;
         X86.RAX := tmp_register;

         -- RDX = i * 8
         -- 4005d8  lea     rdx, ds:0[rax*8]
         --X86.RDX := ( Interfaces.Shift_Left( X86.RAX  ,  16#3# ));
         X86.RDX := X86.RAX * 8;

         -- RAX = dst
         -- 4005e0  mov     rax, [rbp+var_10]
         X86.RAX :=  X86.ReadMem64(( X86.RBP -16 )) ;

         -- RDX = dst[i]
         -- 4005e4  add     rdx, rax
         X86.ZeroFlag := (( X86.RDX  +  X86.RAX ) = 0);
         X86.SignFlag := (( X86.RDX  +  X86.RAX ) > X86.MaxSignedInt64);
         X86.RDX := ( X86.RDX  +  X86.RAX );

         -- RAX = i
         -- 4005e7  mov     rax, [rbp+var_8]
         --X86.RAX :=  X86.ReadMem64(( X86.RBP -8 )) ;
         X86.RAX := tmp_register;

         -- RCX = i * 8
         -- 4005eb  lea     rcx, ds:0[rax*8]
         --X86.RCX := ( Interfaces.Shift_Left( X86.RAX  ,  16#3# ));
         X86.RCX := X86.RAX * 8;

         -- RAX = src
         -- 4005f3  mov     rax, [rbp+var_18]
         X86.RAX :=  X86.ReadMem64(( X86.RBP -24 )) ;

         -- RAX = src[i]
         -- 4005f7  add     rax, rcx
         X86.ZeroFlag := (( X86.RAX  +  X86.RCX ) = 0);
         X86.SignFlag := (( X86.RAX  +  X86.RCX ) > X86.MaxSignedInt64);
         X86.RAX := ( X86.RAX  +  X86.RCX );

         -- RAX = [src[i]]
         -- 4005fa  mov     rax, [rax]
         X86.RAX :=  X86.ReadMem64(( X86.RAX )) ;


         pragma Assert(for all i in saved_rbp_16..(saved_rbp_16+saved_rbp_72-1) =>
                                 X86.InSafeRegion64(i,X86.RSP+8));

         pragma Assert(for all i in Unsigned64 =>
                                 (if (not X86.InRange64(i, saved_rbp_16, saved_rbp_72) and
                                    (not X86.InRange64(i, X86.RBP-8,8))) then
                                      (X86.Memory(i) = X86.Memory'Loop_Entry(i))));


         pragma Assert(saved_rbp_16 = X86.ReadMem64(X86.RBP - 16));
         pragma Assert(saved_rbp_72 = X86.ReadMem64(X86.RBP - 72));
         --pragma Loop_Invariant(X86.ReadMem64( X86.RBP -8 ) < saved_72);
         pragma Assert(tmp_register < saved_rbp_72/8);

         pragma Assert(X86.InRange64(X86.RDX, saved_rbp_16, saved_rbp_72));
         pragma Assert(X86.InRange64(X86.RDX+1, saved_rbp_16, saved_rbp_72));
         pragma Assert(X86.InRange64(X86.RDX+2, saved_rbp_16, saved_rbp_72));
         pragma Assert(X86.InRange64(X86.RDX+3, saved_rbp_16, saved_rbp_72));
         pragma Assert(X86.InRange64(X86.RDX+4, saved_rbp_16, saved_rbp_72));
         pragma Assert(X86.InRange64(X86.RDX+5, saved_rbp_16, saved_rbp_72));
         pragma Assert(X86.InRange64(X86.RDX+6, saved_rbp_16, saved_rbp_72));
         pragma Assert(X86.InRange64(X86.RDX+7, saved_rbp_16, saved_rbp_72));


         -- [dst[i]] = [src[i]]
         -- 4005fd  mov     [rdx], rax
         X86.WriteMem64(( X86.RDX ),  X86.RAX );

         -- i = i + 1
         -- 400600  add     [rbp+var_8], 1
         --X86.ZeroFlag := (( X86.ReadMem64(( X86.RBP -8 ))  +  16#1# ) = 0);
         --X86.SignFlag := (( X86.ReadMem64(( X86.RBP -8 ))  +  16#1# ) > X86.MaxSignedInt64);
         --X86.WriteMem64(( X86.RBP -8 ), ( X86.ReadMem64(( X86.RBP -8 ))  +  16#1# ));
         tmp_register := tmp_register + 1;
      end loop;

      X86.WriteMem64(( X86.RBP -8 ), tmp_register);

      pragma Assert(for all i in Unsigned64 =>
                              (if (not X86.InRange64(i, saved_rbp_16, saved_rbp_72) and
                                 (not X86.InRange64(i, X86.RBP-8,8))) then
                                   (X86.Memory(i) = saved_mem(i))));

      pragma Assert(saved_rbp_16 = X86.ReadMem64(X86.RBP - 16));
      pragma Assert(saved_rbp_72 = X86.ReadMem64(X86.RBP - 72));

      pragma Assert(X86.ReadMem64(X86.RBP-8) >= X86.ReadMem64(X86.RBP - 72)/8);

      pragma Assert(X86.ReadMem64(X86.RBP) = saved_rbp);
      pragma Assert(X86.ReadMem64(X86.RSP+8) = saved_ra);

   end ZSTLoopProc_400605;

   procedure ZSTLoopProc_40064f
   is
      saved_32 : Unsigned64 := X86.ReadMem64(X86.RBP - 32) with Ghost;
      saved_72 : Unsigned64 := X86.ReadMem64( X86.RBP -72 ) with Ghost;
      tmp_register : Unsigned64 := X86.ReadMem64(X86.RBP-8);

      saved_rbp : Unsigned64 := X86.ReadMem64(X86.RBP) with Ghost;
      saved_ra : Unsigned64 := X86.ReadMem64(X86.RSP+8) with Ghost;
      saved_mem: X86.Mem_Array := X86.Memory with Ghost;
   begin
      pragma Assume(X86.RSP = X86.DummyRSP+8);

      -- 40064f  mov     rax, [rbp+var_8]
      loop

         -- RAX = i
         --X86.RAX := X86.ReadMem64( X86.RBP -8 );
         X86.RAX :=  tmp_register;

         -- 400653  cmp     rax, [rbp+var_48]
         X86.ZeroFlag := (( X86.RAX  -  X86.ReadMem64(( X86.RBP -72 )) ) = 0);
         X86.SignFlag := (( X86.RAX  -  X86.ReadMem64(( X86.RBP -72 )) ) > X86.MaxSignedInt64);
         X86.CarryFlag := ( X86.RAX  <  X86.ReadMem64(( X86.RBP -72 )) );
         X86.OverflowFlag := ((X86.SignFlag and then ( X86.ReadMem64(( X86.RBP -72 ))  > X86.MaxSignedInt64) and then ( X86.RAX  <= X86.MaxSignedInt64)) or ((not X86.SignFlag) and then ( X86.RAX  > X86.MaxSignedInt64) and then ( X86.ReadMem64(( X86.RBP -72 ))  <= X86.MaxSignedInt64)));

         -- 400657  jb      short loc_40062F
         exit when (not X86.CarryFlag);
         --exit when (X86.RAX >= X86.ReadMem64(X86.RBP-72));

         pragma Loop_Invariant(for all i in saved_32..(saved_32+saved_72-1) =>
                                 X86.InSafeRegion64(i,X86.RSP+8));

         pragma Loop_Invariant(for all i in Unsigned64 =>
                                 (if (not X86.InRange64(i, saved_32, saved_72) and
                                    (not X86.InRange64(i, X86.RBP-8,8))) then
                                      (X86.Memory(i) = X86.Memory'Loop_Entry(i))));


         pragma Loop_Invariant(saved_32 = X86.ReadMem64(X86.RBP - 32));
         pragma Loop_Invariant(saved_72 = X86.ReadMem64(X86.RBP - 72));
         --pragma Loop_Invariant(X86.ReadMem64( X86.RBP -8 ) < saved_72);
         pragma Loop_Invariant(tmp_register < saved_72);



         pragma Loop_Invariant(X86.ReadMem64(X86.RBP) = saved_rbp);

         pragma Loop_Invariant(X86.ReadMem64(X86.RSP+8) = saved_ra);


         -- RDX = dst
         -- 40062f  mov     rdx, [rbp+var_20]
         X86.RDX :=  X86.ReadMem64(( X86.RBP -32 )) ;

         -- RAX = i
         -- 400633  mov     rax, [rbp+var_8]
         --X86.RAX := X86.ReadMem64( X86.RBP -8 ) ;
         X86.RAX :=  tmp_register;

         -- RDX = dst[i]
         -- 400637  add     rdx, rax
         X86.ZeroFlag := (( X86.RDX  +  X86.RAX ) = 0);
         X86.SignFlag := (( X86.RDX  +  X86.RAX ) > X86.MaxSignedInt64);

         X86.RDX := ( X86.RDX  +  X86.RAX );

         -- RCX = src
         -- 40063a  mov     rcx, [rbp+var_28]
         X86.RCX :=  X86.ReadMem64(( X86.RBP -40 )) ;

         -- RAX = i
         -- 40063e  mov     rax, [rbp+var_8]
         --X86.RAX := X86.ReadMem64( X86.RBP -8 );
         X86.RAX := tmp_register;

         -- RAX = src[i]
         -- 400642  add     rax, rcx
         X86.ZeroFlag := (( X86.RAX  +  X86.RCX ) = 0);
         X86.SignFlag := (( X86.RAX  +  X86.RCX ) > X86.MaxSignedInt64);
         X86.RAX := ( X86.RAX  +  X86.RCX );

         -- EAX = [src[i]]
         -- 400645  movzx   eax, byte ptr [rax]
         X86.Write_EAX(Unsigned32(( X86.ReadMem8(Unsigned64( X86.RAX )) )));


         --Re-assert invariants
         pragma Assert(for all i in saved_32..(saved_32+saved_72-1) =>
                         X86.InSafeRegion64(i,X86.RSP+8));

         pragma Assert(for all i in Unsigned64 =>
                         (if (not X86.InRange64(i, saved_32, saved_72) and
                            (not X86.InRange64(i, X86.RBP-8,8))) then
                              (X86.Memory(i) = X86.Memory'Loop_Entry(i))));


         pragma Assert(saved_32 = X86.ReadMem64(X86.RBP - 32));
         pragma Assert(saved_72 = X86.ReadMem64(X86.RBP - 72));
         --pragma Assert(X86.ReadMem64( X86.RBP -8 ) < saved_72);
         pragma Assert(tmp_register < saved_72);

         --Assert about index into memory
         pragma Assert(X86.InRange64(X86.RDX, saved_32, saved_72));

         -- [dst[i]] = [src[i]]
         -- 400648  mov     [rdx], al
         X86.WriteMem8(Unsigned64( X86.RDX ), Unsigned8( X86.AL ));


         -- i = i + 1
         -- 40064a  add     [rbp+var_8], 1
         --X86.ZeroFlag := (( X86.ReadMem64(( X86.RBP -8 ))  +  16#1# ) = 0);
         --X86.SignFlag := (( X86.ReadMem64(( X86.RBP -8 ))  +  16#1# ) > X86.MaxSignedInt64);
         --X86.WriteMem64(( X86.RBP -8 ), ( X86.ReadMem64(( X86.RBP -8 ))  +  16#1# ));
         tmp_register := tmp_register +1;
      end loop;

      X86.WriteMem64(( X86.RBP -8 ), tmp_register);

      --Assert prologue necessary in this case, but this heuristic was necessary for Loop1
      pragma Assert(for all i in Unsigned64 =>
                              (if (not X86.InRange64(i, saved_32, saved_72) and
                                 (not X86.InRange64(i, X86.RBP-8,8))) then
                                   (X86.Memory(i) = saved_mem(i))));

      pragma Assert(saved_32 = X86.ReadMem64(X86.RBP - 32));
      pragma Assert(saved_72 = X86.ReadMem64(X86.RBP - 72));

      pragma Assert(X86.ReadMem64(X86.RBP-8) >= X86.ReadMem64(X86.RBP - 72)/8);

      pragma Assert(X86.ReadMem64(X86.RBP) = saved_rbp);
      pragma Assert(X86.ReadMem64(X86.RSP+8) = saved_ra);


   end ZSTLoopProc_40064f;


      procedure main
      is
         saved_ra : Unsigned64 := X86.ReadMem64(X86.RSP) with Ghost;
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

         -- 40065f  push    rbp
         X86.WriteMem64(( X86.RSP -8 ),  X86.RBP );
         X86.RSP := ( X86.RSP  -  16#8# );

         -- 400660  mov     rbp, rsp
         X86.RBP :=  X86.RSP ;

         -- 400663  sub     rsp, 90h
         X86.ZeroFlag := (( X86.RSP  -  16#90# ) = 0);
         X86.SignFlag := (( X86.RSP  -  16#90# ) > X86.MaxSignedInt64);
         X86.RSP := ( X86.RSP  -  16#90# );

         -- 40066a  mov     [rbp+var_84], edi
         X86.WriteMem32(Unsigned64( X86.RBP -132 ), Unsigned32( X86.EDI ));

         -- 400670  mov     [rbp+var_90], rsi
         X86.WriteMem64(( X86.RBP -144 ),  X86.RSI );

         -- 400677  mov     qword ptr [rbp+s], 637273h
         X86.WriteMem64(( X86.RBP -64 ),  16#637273# );

         -- 40067f  lea     rdx, [rbp+var_38]
         X86.RDX := ( X86.RBP  +  (-56) );

         -- 400683  mov     eax, 0
         X86.Write_EAX( 16#0# );

         -- 400688  mov     ecx, 5
         X86.Write_ECX( 16#5# );

         -- 40068d  mov     rdi, rdx
         X86.RDI :=  X86.RDX ;

         -- 400690  rep stosq
         X86.WriteMem64(( X86.RDI ),  X86.RAX );
         --  	 X86.RCX := ( X86.RCX ERROR);

         -- 400693  mov     rdx, rdi
         X86.RDX :=  X86.RDI ;

         -- 400696  mov     [rdx], ax
         X86.WriteMem16(Unsigned64( X86.RDX ), Unsigned16( X86.AX ));

         -- 400699  add     rdx, 2
         X86.ZeroFlag := (( X86.RDX  +  16#2# ) = 0);
         X86.SignFlag := (( X86.RDX  +  16#2# ) > X86.MaxSignedInt64);
         X86.RDX := ( X86.RDX  +  16#2# );

         -- 40069d  lea     rax, [rbp+var_80]
         X86.RAX := ( X86.RBP  +  (-128) );

         -- 4006a1  mov     rsi, rax
         X86.RSI :=  X86.RAX ;

         -- 4006a4  mov     edi, offset format; "Before: %s\n"
         X86.Write_EDI( 16#400784# );

         -- 4006a9  mov     eax, 0
         X86.Write_EAX( 16#0# );

         -- 4006ae  call    _printf
         -- X86.WriteMem64((X86.RSP - 8), 16#4006b3# );
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 4006b3  lea     rax, [rbp+s]
         X86.RAX := ( X86.RBP  +  (-64) );

         -- 4006b7  mov     rdi, rax        ; s
         X86.RDI :=  X86.RAX ;

         -- 4006ba  call    _strlen
         -- X86.WriteMem64((X86.RSP - 8), 16#4006bf# );
         X86.RSP := X86.RSP - 8;
         strlen ;
         -- Manually coding what should be the result of strlen
         X86.RAX := 50;

         -- 4006bf  lea     rdx, [rax+1]
         X86.RDX := ( X86.RAX  +  16#1# );

         -- 4006c3  lea     rcx, [rbp+s]
         X86.RCX := ( X86.RBP  +  (-64) );

         -- 4006c7  lea     rax, [rbp+var_80]
         X86.RAX := ( X86.RBP  +  (-128) );

         -- 4006cb  mov     rsi, rcx
         X86.RSI :=  X86.RCX ;

         -- 4006ce  mov     rdi, rax
         X86.RDI :=  X86.RAX ;

         -- 4006d1  call    memcpy2
         -- X86.WriteMem64((X86.RSP - 8), 16#4006d6# );
         X86.RSP := X86.RSP - 8;

         memcpy2 ;

         -- 4006d6  lea     rax, [rbp+var_80]
         X86.RAX := ( X86.RBP  +  (-128) );

         -- 4006da  mov     rsi, rax
         X86.RSI :=  X86.RAX ;

         -- 4006dd  mov     edi, offset aAfterS; "After: %s\n"
         X86.Write_EDI( 16#400790# );

         -- 4006e2  mov     eax, 0
         X86.Write_EAX( 16#0# );

         -- 4006e7  call    _printf
         -- X86.WriteMem64((X86.RSP - 8), 16#4006ec# );
         X86.RSP := X86.RSP - 8;
         printf ;

         -- 4006ec  mov     eax, 0
         X86.Write_EAX( 16#0# );

         -- 4006f1  leave
         X86.RSP := ( X86.RBP  +  16#8# );
         X86.RBP :=  X86.ReadMem64(( X86.RBP )) ;

         -- 4006f2  retn
         X86.RSP := X86.RSP + 8;
         return;

      end main;


end memcpy;
