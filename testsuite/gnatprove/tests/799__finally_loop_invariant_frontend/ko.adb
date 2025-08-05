
--  Loop invariants are illegal under a finally-containing handled sequence
--  of statements. This one is currently rejected by front-end.

procedure KO with SPARK_Mode is
   B : Boolean;
begin
   loop
      begin
         null;
      finally
         pragma Loop_Invariant (B);
      end;
   end loop;
end KO;
