procedure P is
   S : String := "This is a string that contains more than 24 characters.";
begin
   S (10 .. 24) (19 .. 24) := (others => ' ');
end P;
