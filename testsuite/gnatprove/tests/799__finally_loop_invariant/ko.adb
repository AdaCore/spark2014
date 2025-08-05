procedure KO with SPARK_Mode is
   B : Boolean;
begin
   loop
      begin
         pragma Loop_Invariant (B); -- Illegal because of finally
      finally
         null;
      end;
   end loop;
end KO;
