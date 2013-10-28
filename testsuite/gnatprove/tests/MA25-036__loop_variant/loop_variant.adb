pragma SPARK_Mode (On);
procedure Loop_Variant_Example (Result : out Integer) is
   type Total is range 1 .. 100;
   subtype T is Total range 1 .. 10;
   I : T := 1;
   R : Total := 100;
begin
   while I < 10 and R > 10 loop
       pragma Loop_Variant (Increases => I,
                            Decreases => R);
       R := R - I;     -- 100, 99, 97, 94, 90, 85, 80, 75, 70...
       if I < 5 then
          I := I + 1;  -- 1, 2, 3, 4, 5, 5, 5, 5, 5...
       end if;
   end loop;
   Result := Integer (I + R); -- produce a result to avoid flow errors
end Loop_Variant_Example;
