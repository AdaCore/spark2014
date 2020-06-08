procedure Test_Goto with SPARK_Mode is
   type Enum is (E1, E2, E3);
   function B (I : Integer) return Boolean with Import;
   function E return Enum with Import;

   X : Integer := 0;
begin
   for I in 1 .. 2 loop
      if B (1) then
         case E is
         when E2 =>
            if B (3) then
               declare
                  Y : Integer := 10;
               begin
                  for I in 1 .. Y loop
                     X := X + 1; --@OVERFLOW_CHECK:FAIL
                     if B (32) then
                        goto L8;
                     elsif B (33) then
                        goto L7;
                     end if;
                     <<L8>>
                  end loop;

                  if B (30) then
                     goto L5;
                  elsif B (31) then
                     goto L7;
                  end if;
                  <<L7>>
               end;
            elsif B (4) then
               goto L1;
            end if;
            goto L5;
            <<L5>>
            X := 5;
         when others =>
            if B (3) then
               goto L6;
            elsif B (4) then
               goto L1;
            end if;
            goto L6;
            <<L6>>
            X := 6;
         end case;
         if B (5) then
            goto L2;
         elsif B (6) then
            goto L0;
         end if;
         goto L2;
         <<L2>>
      elsif B (2) then
         if B (7) then
            goto L0;
         elsif B (8) then
            goto L3;
         end if;
         goto L3;
         <<L3>>
         X := 3;
      else
         if B (7) then
            goto L1;
         elsif B (8) then
            goto L0;
         end if;
         goto L4;
         <<L4>>
         X := 4;
      end if;
      if B (9) then
         goto L1;
      elsif B (10) then
         goto L0;
      end if;
      goto L1;
      <<L1>>
      pragma Loop_Invariant (True);
      X := 1;
   end loop;
   if B (11) then
      goto L0;
   end if;
   goto L0;
   <<L0>>
   pragma Assert (B (X)); --@ASSERT:FAIL
   null;
end Test_Goto;
