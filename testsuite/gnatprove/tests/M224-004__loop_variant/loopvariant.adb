pragma Ada_2012;
pragma Assertion_Policy (Loop_Variant => Check);
procedure LoopVariant is
   I, J : Integer;
begin
   I := 1;
   J := 3;
   while I < 3 loop
      if J > 0  then
         J := J - 1;
      else
         J := 3;
         I := I + 1;
      end if;
      pragma Loop_Variant (Increases => I, Decreases => J);
   end loop;
   I := 1;
   J := 3;
   while I < 3 loop
      if J > 0  then
         J := J - 1;
      else
         J := 3;
         I := I - 1;
      end if;
      pragma Loop_Variant (Increases => I, Decreases => J);
      exit when I not in 0 .. 3;
   end loop;
end LoopVariant;
