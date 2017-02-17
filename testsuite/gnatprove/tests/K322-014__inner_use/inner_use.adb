package body Inner_Use is
   procedure P (B : Boolean) is
   begin
      if B then
	 X := 4;
      else
	 X := 3;
      end if;
   end;
end Inner_Use;

