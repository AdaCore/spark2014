package body No_Return is

   X : Integer := 0;

   procedure Aborting is
   begin
      if X /= 0 then
         X := 1;
      end if;
      raise Program_Error;
   end Aborting;

   procedure P is
   begin
      Aborting;
   end P;

end No_Return;
