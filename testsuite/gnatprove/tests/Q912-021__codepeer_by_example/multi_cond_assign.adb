procedure Multi_Cond_Assign (X : out Integer; Y : in Integer; B1, B2 : in Boolean) is
begin
   if B1 then
      X := Y + 1;
   else
      if B2 then
	 X := Y - 1;
      else
	 X := Y * 2;
      end if;
   end if;
end Multi_Cond_Assign;
