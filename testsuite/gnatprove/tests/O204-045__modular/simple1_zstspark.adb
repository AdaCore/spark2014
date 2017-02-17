Package body Simple1_Zstspark
with SPARK_Mode
is

   procedure main
   is
      SaveRSP: Unsigned64 := X86.RSP with Ghost;
   begin

      -- 4004f6  push    rbp
      X86.WriteMem64(Unsigned64( X86.RSP -8 ), Unsigned64( X86.RBP ));
      X86.RSP := ( X86.RSP  -  8 );
      pragma Assert (X86.RSP = SaveRSP - 8);

      -- 4004f7  mov     rbp, rsp
      X86.RBP :=  X86.RSP ;

      -- 4004fa  mov     [rbp+var_14], edi
      X86.WriteMem32(Unsigned64( X86.RBP -20 ), Unsigned32( X86.EDI ));

      -- 4004fd  mov     [rbp+var_20], rsi
      X86.WriteMem64(Unsigned64( X86.RBP -32 ), Unsigned64( X86.RSI ));

      -- 400501  mov     eax, [rbp+var_14]
      X86.Write_EAX( X86.ReadMem32(Unsigned64( X86.RBP -20 )) );

      -- 400504  mov     [rbp+var_8], eax
      X86.WriteMem32(Unsigned64( X86.RBP -8 ), Unsigned32( X86.EAX ));

      -- 400507  mov     [rbp+var_C], 2
      X86.WriteMem32(Unsigned64( X86.RBP -12 ), Unsigned32( 2 ));

      -- 40050e  mov     [rbp+var_4], 0Dh
      X86.WriteMem32(Unsigned64( X86.RBP -4 ), Unsigned32( 13 ));

      -- 400515  mov     eax, [rbp+var_8]
      X86.Write_EAX( X86.ReadMem32(Unsigned64( X86.RBP -8 )) );

      -- 400518  cmp     eax, [rbp+var_4]
      X86.ZeroFlag := (( X86.EAX  -  X86.ReadMem32(Unsigned64( X86.RBP -4 )) ) = 0);
      X86.SignFlag := (( X86.EAX  -  X86.ReadMem32(Unsigned64( X86.RBP -4 )) ) > X86.MaxSignedInt32);
      X86.CarryFlag := ( X86.EAX  <  X86.ReadMem32(Unsigned64( X86.RBP -4 )) );
      X86.OverflowFlag := ((X86.SignFlag and then ( X86.ReadMem32(Unsigned64( X86.RBP -4 ))  > X86.MaxSignedInt32) and then ( X86.EAX  <= X86.MaxSignedInt32)) or ((not X86.SignFlag) and then ( X86.EAX  > X86.MaxSignedInt32) and then ( X86.ReadMem32(Unsigned64( X86.RBP -4 ))  <= X86.MaxSignedInt32)));

      -- 40051b  jge     short loc_400528
      if (X86.ZeroFlag /= X86.OverflowFlag) then

         -- 40051d  mov     eax, [rbp+var_4]
         X86.Write_EAX( X86.ReadMem32(Unsigned64( X86.RBP -4 )) );

         -- 400520  sub     eax, [rbp+var_8]
         X86.Write_EAX(( X86.EAX  -  X86.ReadMem32(Unsigned64( X86.RBP -8 )) ));

         -- 400523  mov     [rbp+var_C], eax
         X86.WriteMem32(Unsigned64( X86.RBP -12 ), Unsigned32( X86.EAX ));

         -- 400526  jmp     short loc_400538
      else

         -- 400528  mov     eax, [rbp+var_8]
         X86.Write_EAX( X86.ReadMem32(Unsigned64( X86.RBP -8 )) );

         -- 40052b  sub     eax, [rbp+var_C]
         X86.Write_EAX(( X86.EAX  -  X86.ReadMem32(Unsigned64( X86.RBP -12 )) ));

         -- 40052e  mov     edx, eax
         X86.Write_EDX( X86.EAX );

         -- 400530  mov     eax, [rbp+var_4]
         X86.Write_EAX( X86.ReadMem32(Unsigned64( X86.RBP -4 )) );

         -- 400533  add     eax, edx
         X86.Write_EAX(( X86.EAX  +  X86.EDX ));

         -- 400535  mov     [rbp+var_C], eax
         X86.WriteMem32(Unsigned64( X86.RBP -12 ), Unsigned32( X86.EAX ));

         -- 400538  mov     eax, [rbp+var_8]
      end if;
      X86.Write_EAX( X86.ReadMem32(Unsigned64( X86.RBP -8 )) );

      -- 40053b  cmp     eax, [rbp+var_4]
      X86.ZeroFlag := (( X86.EAX  -  X86.ReadMem32(Unsigned64( X86.RBP -4 )) ) = 0);
      X86.SignFlag := (( X86.EAX  -  X86.ReadMem32(Unsigned64( X86.RBP -4 )) ) > X86.MaxSignedInt32);
      X86.CarryFlag := ( X86.EAX  <  X86.ReadMem32(Unsigned64( X86.RBP -4 )) );
      X86.OverflowFlag := ((X86.SignFlag and then ( X86.ReadMem32(Unsigned64( X86.RBP -4 ))  > X86.MaxSignedInt32) and then ( X86.EAX  <= X86.MaxSignedInt32)) or ((not X86.SignFlag) and then ( X86.EAX  > X86.MaxSignedInt32) and then ( X86.ReadMem32(Unsigned64( X86.RBP -4 ))  <= X86.MaxSignedInt32)));

      -- 40053e  jge     short loc_400546
      if (X86.ZeroFlag /= X86.OverflowFlag) then


         -- 400540  mov     eax, [rbp+var_C]
         X86.Write_EAX( X86.ReadMem32(Unsigned64( X86.RBP -12 )) );

         -- 400543  add     [rbp+var_8], eax
         X86.WriteMem32(Unsigned64( X86.RBP -8 ), Unsigned32(( X86.ReadMem32(Unsigned64( X86.RBP -8 ))  +  X86.EAX )));

         -- 400546  mov     eax, 0
      end if;
      X86.Write_EAX( 0 );

      -- 40054b  pop     rbp
      pragma Assert (X86.RSP = SaveRSP - 8);
      X86.RBP :=  X86.ReadMem64(Unsigned64( X86.RSP + 0 )) ;
      X86.RSP := ( X86.RSP  +  8 );
      pragma Assert (X86.RSP = (SaveRSP - 8) + 8);
      pragma Assert (X86.RSP = SaveRSP + (-8 + 8));
      pragma Assert (X86.RSP = SaveRSP);

      -- 40054c  retn
      X86.RSP := X86.RSP + 8;
      return;
   end main;

end Simple1_Zstspark;
