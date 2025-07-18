procedure Finally_Range with SPARK_Mode is

   Fatal : exception;
   E : exception;

   Low : Integer;
   High : Integer;
   function Test (X : Integer) return Boolean
     with Side_Effects,
     Global => (Output => (Low, High)),
     Post => Test'Result and (case X is
              when 0 => Low = 1 and High = 2,
              when 2 => Low = 2 and High = 3,
              when 3 => Low = 3 and High = 4,
              when 4 => Low = 2 and High = 4,
              when 5 => Low = 1 and High = 4,
              when 6 => Low = 0 and High = 4,
              when 7 => Low = 2 and High = 4,
              when 8 => Low = 1 and High = 4,
              when 9 => Low = 2 and High = 3,
              when 10 => Low = 1 and High = 3,
              when 11 => Low = 2 and High = 3,
              when 12 => Low = 1 and High = 3,
              when 13 => Low = 0 and High = 3,
              when 14 => Low = 1 and High = 2,
              when 15 => Low = 2 and High = 2,
              when 16 => Low = 1 and High = 2,
              when 17 => Low = 0 and High = 2,
              when 18 => Low = 1 and High = 3,
              when 19 => Low = 0 and High = 1,
              when 20 => Low = 2 and High = 4,
              when 21 => Low = 1 and High = 3,
              when 22 => Low = 4 and High = 5,
              when 23 => Low = 6 and High = 7,
              when 24 => Low = 3 and High = 5,
              when 25 => Low = 7 and High = 7,
              when others => True),
       Exceptional_Cases => (Fatal => Low = 0 and High = 2),
     Exit_Cases => (X = 1 => (Exception_Raised => Fatal),
                    others => Normal_Return);
   function Test (X : Integer) return Boolean is
      Main_Jump : Boolean := False;
      High_Assigned : Boolean := False;
      Depth : Integer := 0;
      procedure Enter;
      procedure Enter is
      begin
         Depth := Depth + 1;
      end Enter;
      procedure Final_Section;
      procedure Final_Section is
      begin
         if Main_Jump and not High_Assigned then
            High := Depth;
            High_Assigned := True;
         end if;
         Depth := Depth - 1;
      end Final_Section;
      procedure Register;
      procedure Register is
      begin
         if Main_Jump then
            if not High_Assigned then
               High := Depth;
               High_Assigned := True;
            end if;
            Main_Jump := False;
            Low := Depth;
         end if;
      end Register;
   begin
      pragma Assert (not Main_Jump);
      Enter;
      Low := -42;
      High := -42;
      begin
         Enter;

         if X = 1 then
            Main_Jump := True;
            raise Fatal;
         end if;
         loop
            begin
               Enter;
               Main_Jump := (X = 2);
               exit;
            finally
               Final_Section;
            end;
            pragma Loop_Invariant (False);
         end loop;
         Register;


         Main_Jump := (X = 0);
      finally
         Final_Section;
      end;
      Register;

      Outer: while Depth >= 0 loop
         begin
            Enter;
            Midway : loop
               begin
                  Enter;
                  Inner: for I in 4 .. 1000000 loop
                     begin
                        Enter;
                        Main_Jump := (X in 3 .. 8) or X = 20;
                        case X is
                           when 3 =>
                              exit Inner;
                           when 4 =>
                              exit Midway;
                           when 5 =>
                              exit Outer;
                           when 6 =>
                              return True;
                           when 7 =>
                              raise Fatal;
                           when 8 =>
                              raise E;
                           when 20 =>
                              goto L;
                           when others =>
                              null;
                        end case;
                     finally
                       Final_Section;
                     end;
                     exit;
                     pragma Loop_Invariant (False);
                  end loop Inner;
                  Register;
                  Main_Jump := (X in 9 .. 13);
                  case X is
                     when 9 =>
                        exit Midway;
                     when 10 =>
                        exit Outer;
                     when 11 =>
                        raise Fatal;
                     when 12 =>
                        raise E;
                     when 13 =>
                        return True;
                     when others =>
                        null;
                  end case;
               finally
                    Final_Section;
               end;
               exit;
               <<L>>
               Register;
               exit;
               pragma Loop_Invariant (False);
            end loop Midway;
            Register;
            Main_Jump := (X in 14 .. 17);
            case X is
               when 14 =>
                  exit Outer;
               when 15 =>
                  raise Fatal;
               when 16 =>
                  raise E;
               when 17 =>
                  return True;
               when others =>
                  null;
            end case;
         exception
            when Fatal =>
               Register;
         finally
            Final_Section;
         end;
         exit;
         pragma Loop_Invariant (False);
      end loop Outer;
      Register;

      if X in 18 | 19 then
         return B : Boolean := False do
            Enter;
            begin
               Enter;
               if X = 18 then
                  Main_Jump := True;
                  return;
               end if;
               finally
                 Final_Section;
            end;
         finally
            Final_Section;
            Register;
            Main_Jump := (X = 19);
            B := True;
         end return;
      end if;

      begin
         Enter;
         loop
            begin
               Enter;
               if X in 21 .. 23 then
                  Main_Jump := (X = 21);
                  goto L2;
               end if;
            finally
               Final_Section;
            end;
            exit;
            pragma Loop_Invariant (False);
         end loop;
         Register;
      finally
         begin
            Enter;
            begin
               Enter;
               begin
                  Enter;
                  if X in 22 | 23 then
                     Main_Jump := (X = 22);
                     raise E;
                  elsif X in 24 | 25 then
                     Main_Jump := (X = 24);
                     raise Fatal;
                  end if;
               finally
                  Final_Section;
               end;
            exception
               when others =>
                  begin
                     Enter;
                  finally
                     begin
                        Enter;
                        begin
                           Enter;
                           if X in 23 | 25 then
                              Main_Jump := True;
                              raise;
                           end if;
                        exception
                           when Fatal =>
                              Register;
                        finally
                           Final_Section;
                        end;
                     exception
                        when E => Register;
                     finally
                       Final_Section;
                     end;
                     Final_Section;
                  end;
                  if X = 24 then
                     raise;
                  elsif X = 22 then
                     Register;
                  end if;
            finally
               Final_Section;
            end;
         exception
            when Fatal => Register;
         finally
            Final_Section;
         end;
         Final_Section;
      end;
      <<L2>>
      Register;

      return True;
   exception
      when E =>
         Register;
         return True;

   finally
      Final_Section;
      Register;
      pragma Assert (if X in 0 .. 25 then High_Assigned);
      pragma Assert (not Main_Jump);
   end Test;

begin
   Dummy : Boolean := Test (42);
end Finally_Range;
