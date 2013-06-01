procedure Choice (X : Boolean) is
begin
   if X in True | False then
      null;
   end if;
   if X in Boolean then
      null;
   end if;
   case X is
      when True | False =>
	 null;
   end case;
end Choice;
