
procedure Finally_Frame_Condition with SPARK_Mode is

   procedure Write_Detection;
   procedure Write_Detection is
      X : Natural := 0;
   begin
      --  Write in finally are detected, relevant variables are not assumed
      --  invariant across the loop.

      for I in 1 .. 100000 loop
         begin
            goto L;
         finally
            X := X + 1; --@OVERFLOW_CHECK:FAIL
         end;
         <<L>>
      end loop;
      pragma Assert (X = 0); --@ASSERT:FAIL
   end Write_Detection;

   procedure Loop_Needing_Accurate_Analysis;
   procedure Loop_Needing_Accurate_Analysis is
      X : Natural := 0;
      Y : Natural := 0;
   begin
      loop
         begin
            X := X + 1;
            if X = 42 then
               Y := Y + 1;
               exit;
            end if;
         finally
              X := 2 * X;
         end;
      end loop;
      --  A precise CFG analysis could detect Y is unchanged on loop
      --  iterations. An imprecise analysis do not, because the graph of
      --  finally create a join point for the exiting and iteration path.

      pragma Assert (Y = 1);
   end Loop_Needing_Accurate_Analysis;

begin
   null;
end Finally_Frame_Condition;
