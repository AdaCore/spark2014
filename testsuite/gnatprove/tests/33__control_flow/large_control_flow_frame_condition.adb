
procedure Large_Control_Flow_Frame_Condition with SPARK_Mode is
   E : exception;
   F : exception;
   G : exception;
   function Nested return Boolean is
      Seed : Integer := 0;
      procedure Twist
        with Import, Global => (In_Out => Seed),
        Always_Terminates;
      function Random (I : Integer := 0) return Boolean
        with Import, Global => (Input => Seed);
      function RandInt (I : Integer := 0) return Integer
        with Import, Global => (Input => Seed);
      MD0 : Integer := 0;
      MD1 : Integer := 0;
      MD2 : Integer := 0;
      MD3 : Integer := 0;
      MD4 : Integer := 0;
      MD5 : Integer := 0;
      MD6 : Integer := 0;
      MD7 : Integer := 0;
      MD8 : Integer := 0;
      MD9 : Integer := 0;
      MD10 : Integer := 0;
      MD11 : Integer := 0;
      MD12 : Integer := 0;
      MD13 : Integer := 0;
      MD14 : Integer := 0;
      MD15 : Integer := 0;
      MD16 : Integer := 0;
      MD17 : Integer := 0;
      MD18 : Integer := 0;
      MD19 : Integer := 0;

      PR0 : Integer := 0;
      PR1 : Integer := 0;
      PR2 : Integer := 0;
      PR3 : Integer := 0;
      PR4 : Integer := 0;
      PR5 : Integer := 0;
      PR6 : Integer := 0;
      PR7 : Integer := 0;
      PR8 : Integer := 0;
      PR9 : Integer := 0;
      PR10 : Integer := 0;
      PR11 : Integer := 0;
      PR12 : Integer := 0;
      PR13 : Integer := 0;
      PR14 : Integer := 0;
      PR15 : Integer := 0;
      PR16 : Integer := 0;
      PR17 : Integer := 0;
      PR18 : Integer := 0;
   begin
      Outer: while Random loop
         Twist;

         MD9 := MD9 + 1; --@OVERFLOW_CHECK:FAIL

         while Random loop
            Twist;
            PR12 := PR12 + 1;
            exit Outer; -- EXITS
            Twist;
         end loop;
         Twist;

         MD10 := MD10 + 1; --@OVERFLOW_CHECK:FAIL

         begin
            pragma Loop_Invariant (True);
         end;
         begin
            Mid: while Random loop
               Twist;
               Inner : while Random loop
                  Twist;
                  MD6 := MD6 + 1; --@OVERFLOW_CHECK:FAIL
                  if Random then
                     Twist;
                     MD5 := MD5 + 1; --@OVERFLOW_CHECK:FAIL
                     exit Mid;
                     Twist;
                  end if;
                  Twist;
                  if Random then
                     Twist;
                     MD11 := MD11 + 1; --@OVERFLOW_CHECK:FAIL
                     exit Mid when Random;
                     Twist;
                     return True;
                  end if;
                  Twist;
                  if Random then
                     Twist;
                     MD12 := MD12 + 1; --@OVERFLOW_CHECK:FAIL
                     exit Outer when Random;
                     Twist;
                  end if;
                  Twist;

                  if Random then
                     Twist;
                     goto LM;
                     Twist;
                  end if;
                  Twist;

                  if Random then
                     begin
                        case RandInt is
                        when 0 =>
                           Twist;
                           raise E;
                           Twist;
                        when 1 =>
                           Twist;
                           raise F;
                           Twist;
                        when 2 =>
                           Twist;
                           raise G;
                           Twist;
                        when others =>
                           Twist;
                        end case;
                     exception
                        when E =>
                           MD17 := MD17 + 1; --@OVERFLOW_CHECK:FAIL
                           raise;
                           Twist;
                        when others =>
                           PR17 := PR17 + 1;
                           raise;
                           Twist;
                     end;
                  end if;
                  Twist;

                  begin
                     case RandInt is
                        when 0 =>
                           Twist;
                           MD13 := MD13 + 1; --@OVERFLOW_CHECK:FAIL
                           raise F;
                           Twist;
                        when 1 =>
                           Twist;
                           PR13 := PR13 + 1;
                           case RandInt is -- EXITS
                              when 0 =>
                                 Twist;
                                 exit Inner; -- EXITS
                                 Twist;
                              when 1 =>
                                 Twist;
                              when others =>
                                 Twist;
                                 return (Seed = 0); -- EXITS
                                 Twist;
                           end case;
                           PR14 := PR14 + 1;
                           raise E;
                           Twist;
                        when 2 =>
                           Twist;
                           MD14 := MD14 + 1; --@OVERFLOW_CHECK:FAIL
                           raise G;
                           Twist;
                        when others =>
                           Twist;
                     end case;

                     begin
                        case RandInt is
                           when 0 =>
                              Twist;
                              MD19 := MD19 + 1; --@OVERFLOW_CHECK:FAIL
                              raise F;
                              Twist;
                           when 1 =>
                              Twist;
                              MD15 := MD15 + 1; --@OVERFLOW_CHECK:FAIL
                              raise E; -- Actually exits, but inacurrately
                                       -- detected as not exiting.
                              Twist;
                           when 2 =>
                              Twist;
                              PR18 := PR18 + 1;
                              raise G;
                              Twist;
                           when others =>
                              Twist;
                        end case;
                     exception
                        when E | F =>
                           MD18 := MD18 + 1; --@OVERFLOW_CHECK:FAIL
                           raise;
                           Twist;
                           -- keep outer behavior (E exits, F does not) ?
                           -- inaccurate, in fact neither exits
                           -- since behavior of the full handler is
                           -- abstracted as single Boolean.
                        when others =>
                           exit Outer;
                           Twist;
                           --  G exits.
                     end;

                     PR15 := PR15 + 1; -- EXITS
                     case RandInt is
                        when 0 =>
                           Twist;
                           exit Outer;
                           Twist;
                        when 1 =>
                           Twist;
                           return Seed = 1;
                           Twist;
                        when 2 =>
                           Twist;
                        when others =>
                           Twist;
                           raise E;
                           Twist;
                     end case;

                  exception
                     when F | G =>
                        MD16 := MD16 + 1; --@OVERFLOW_CHECK:FAIL
                        raise E;
                        Twist; -- F/G do not exit
                     when E =>
                        PR16 := PR16 + 1;
                        Twist; -- E exits
                  end;

                  PR9 := PR9 + 1;
                  if Random (0) then -- EXITS
                     Twist;
                     PR8 := PR8 + 1;
                     exit; -- EXITS
                     Twist;
                  elsif Random (1) then
                     Twist;
                     PR7 := PR7 + 1;
                     raise G; -- EXITS
                     Twist;
                  elsif Random (2) then
                     Twist;
                     PR6 := PR6 + 1;
                     exit Outer; -- EXITS
                     Twist;
                  elsif Random (3) then
                     Twist;
                     raise F; -- EXITS;
                     Twist;
                  else
                     Twist;
                     PR5 := PR5 + 1;
                     goto LI; -- EXITS
                     Twist;
                  end if;
                  <<LM>>
                  MD4 := MD4 + 1; --@OVERFLOW_CHECK:FAIL
               end loop Inner;
               Twist;
               PR10 := PR10 + 1;
               <<LI>>
               return B : Boolean := True do -- EXITS
                  if Random then
                     Twist;
                     PR4 := PR4 + 1;
                     raise G; -- EXITS
                     Twist;
                  end if;
                  Twist;
               end return;
               Twist;
            end loop Mid;
            Twist;
            MD8 := MD8 + 1; --@OVERFLOW_CHECK:FAIL
            if Random (0) then
               Twist;
               MD3 := MD3 + 1; --@OVERFLOW_CHECK:FAIL
               raise E;
               Twist;
            elsif Random (1) then
               Twist;
               PR3 := PR3 + 1;
               raise G; -- EXITS
               Twist;
            else
               Twist;
               MD7 := MD7 + 1; --@OVERFLOW_CHECK:FAIL
               return B : Boolean := False do
                  goto L;
                  Twist;
               end return;
               Twist;
            end if;
         exception
            when E => MD2 := MD2 + 1; --@OVERFLOW_CHECK:FAIL
            when F =>
               PR2 := PR2 + 1;
               exit Outer;
               Twist;
            when others =>
               PR11 := PR11 + 1;
               raise; Twist;
         end;
         if Random (0) then
            Twist;
            PR1 := PR1 + 1;
            exit; -- EXITS
            Twist;
         elsif Random (1) then
            Twist;
            MD1 := MD1 + 1; --@OVERFLOW_CHECK:FAIL
            goto L;
            Twist;
         end if;
         Twist;
         PR0 := PR0 + 1;
         return True; -- EXITS
         Twist;
         <<L>>
         MD0 := MD0 + 1; --@OVERFLOW_CHECK:FAIL
         Twist;
      end loop Outer;
      Twist;
      --  Pretend that we care about the final values to suppress some
      --  warnings.
      return (MD0 = 0
              and MD1 = 0
              and MD2 = 0
              and MD3 = 0
              and MD4 = 0
              and MD5 = 0
              and MD6 = 0
              and MD7 = 0
              and MD8 = 0
              and MD9 = 0
              and MD10 = 0
              and MD11 = 0
              and MD12 = 0
              and MD13 = 0
              and MD14 = 0
              and MD15 = 0
              and MD16 = 0
              and MD17 = 0
              and MD18 = 0
              and MD19 = 0
              and PR0 = 0
              and PR1 = 0
              and PR2 = 0
              and PR3 = 0
              and PR4 = 0
              and PR5 = 0
              and PR6 = 0
              and PR7 = 0
              and PR8 = 0
              and PR9 = 0
              and PR10 = 0
              and PR11 = 0
              and PR12 = 0
              and PR13 = 0
              and PR14 = 0
              and PR15 = 0
              and PR16 = 0
              and PR17 = 0
              and PR18 = 0
              and Seed = 0);
   exception
      when others =>
         return True;
   end Nested;
begin
   if Nested then
      null;
   end if;
end Large_Control_Flow_Frame_Condition;
