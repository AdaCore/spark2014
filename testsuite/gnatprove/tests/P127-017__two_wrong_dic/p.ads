package P is

   function Really_False return Boolean is (False);

   type Wrong is private with Default_Initial_Condition => Really_False;

private
   type Wrong is null record;

end;
