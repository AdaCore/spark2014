package body Pack is

   procedure Get_Paid (S : Salary := Default_Salary) is
   begin
      if Stash > Money (S) then
         Stash := Stash - S;
         Pocket := Pocket + S;
      end if;
   end Get_Paid;

end Pack;
