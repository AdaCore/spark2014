procedure Finally_Structural_Variants with SPARK_Mode is
   E : exception;
   type Cell;
   type List is access Cell;
   type Cell is record
      Head : Integer;
      Tail : List;
   end record;
   procedure Sink with
     Post => False,
     Global => null,
     Import,
     Always_Terminates => True;
   procedure Test (X : List)
     with Subprogram_Variant => (Structural => X);
   procedure Test (X : List) is
   begin
      if X /= null then
         if X.Head = 1 then
            Test (X.Tail);
         else
            begin
               if X.Head = 0 then
                  begin
                     loop
                        pragma Loop_Variant (Decreases => 0);
                        Sink;
                     end loop;
                     finally
                       X.Tail := null;
                  end;
               end if;
               finally
                 Test (X.Tail); --@SUBPROGRAM_VARIANT:FAIL
            end;
         end if;
      end if;
   end Test;
   procedure Test2 (X : List);
   procedure Test2 (X : List) is
      Y : access Cell := X;
   begin
      while Y /= null loop
         pragma Loop_Variant (Structural => Y); --@LOOP_VARIANT:PASS
         begin
            loop
               pragma Loop_Invariant (Y /= null);
               begin
                  case Y.Head is
                     when 0 =>
                        goto L;
                     when 1 =>
                        raise E;
                     when 2 =>
                        exit;
                     when others =>
                        null;
                  end case;
               finally
                  Y := Y.Tail;
               end;
               <<L>>
               exit;
            end loop;
         exception
            when others =>
              null;
         end;
      end loop;
   end Test2;
begin
   null;
end Finally_Structural_Variants;
