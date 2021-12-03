procedure Repro is
   I : Integer := 0 ;
begin
   While I < 100 loop
      pragma Loop_Invariant (I < 43);  --  @COUNTEREXAMPLE
      I := I + 1;
   end loop;
end;
