package body No_Return_Illegal
is

   X : Integer := 0;

   procedure Aborting is
   begin
      if X /= 0 then
         X := 1;
      end if;
      raise Program_Error;
   end Aborting;

   procedure P2 is
   begin
      if X = 1 then
         Aborting;
         X := X + 2;
      end if;
   end P2;

   procedure P3 is
   begin
      if X = 1 then
         Aborting;
      elsif X = 2 then
         X := X + 1;
      end if;
   end P3;

   procedure P4 is
   begin
      if X = 1 then
         Aborting;
      else
         X := X + 1;
      end if;
   end P4;

   procedure P5 is
   begin
      X := X + 1;
      Aborting;
   end P5;

end No_Return_Illegal;
