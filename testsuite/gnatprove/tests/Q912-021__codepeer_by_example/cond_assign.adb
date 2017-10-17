procedure Cond_Assign (X : out Integer; Y : in Integer; B : in Boolean) is
begin
   if B then
      X := Y + 1;
   else
      X := Y - 1;
   end if;
end Cond_Assign;
