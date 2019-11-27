procedure Test_Bad_Goto with SPARK_Mode is
   type Enum is (E1, E2, E3);
   function B (I : Integer) return Boolean with Import;
   function E return Enum with Import;

   X : Integer := 0;
begin
   <<L0>>
   for I in 1 .. 2 loop
      if B (1) then
         <<L2>>
         case E is
         when E2 =>
            <<L5>>
            if B (3) then
               declare
                  Y : Integer := 10;
               begin
                  <<L7>>
                  for I in 1 .. Y loop
                     <<L8>>
                     X := X + 1;
                     if B (32) then
                        goto L8;
                     elsif B (33) then
                        goto L1;
                     end if;
                  end loop;

                  if B (30) then
                     goto L1;
                  elsif B (31) then
                     goto L7;
                  end if;
               end;
            elsif B (4) then
               goto L5;
            end if;
            X := 5;
         when others =>
            <<L6>>
            if B (3) then
               goto L6;
            elsif B (4) then
               goto L1;
            end if;
            X := 6;
         end case;
         if B (5) then
            goto L2;
         elsif B (6) then
            goto L1;
         end if;
         goto L2;
      elsif B (2) then
         <<L3>>
         if B (7) then
            goto L1;
         elsif B (8) then
            goto L3;
         end if;
         X := 3;
      else
         <<L4>>
         if B (7) then
            goto L1;
         elsif B (8) then
            goto L4;
         end if;
         X := 4;
      end if;
      if B (9) then
         goto L1;
      elsif B (10) then
         goto L0;
      end if;
      goto L1;
      pragma Loop_Invariant (True);
      <<L1>>
      X := 1;
   end loop;
   if B (11) then
      goto L0;
   end if;
end Test_Bad_Goto;
