package body No_Return is

   X : Integer := 0;

   --  Placement of calls to non-returning procedures
   --
   --  Legal cases

   procedure Aborting is
   begin
      if X /= 0 then
         X := 1;
      end if;
      raise Program_Error; -- legal
   end Aborting;

   procedure P is
   begin
      if X = 1 then
         Aborting; -- legal placement
      end if;
   end P;

end No_Return;
