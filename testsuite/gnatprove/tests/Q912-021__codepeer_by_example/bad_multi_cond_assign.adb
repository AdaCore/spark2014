procedure Bad_Multi_Cond_Assign (X : out Integer; Y : in Integer; B1, B2 : in Boolean) is
begin
   if B1 or Y < 10 then
      X := Y + 1;
   else
      if B2 and not (Y > 0) then
	 X := Y - 1;
      else
	 X := Y * 2;
      end if;
   end if;
end Bad_Multi_Cond_Assign;
