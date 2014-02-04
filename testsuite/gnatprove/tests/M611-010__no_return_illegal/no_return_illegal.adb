package body No_Return_Illegal
is

   X : Integer := 0;

   --  Placement of calls to non-returning procedures
   --
   --  Illegal cases

   -- TU: 1. For a call to a nonreturning procedure to be in |SPARK|, it must
   -- be either
   --  * immediately enclosed by an if statement which encloses no other
   --    statement; or
   --  * the last statement of a subprogram.

   procedure Aborting is
   begin
      if X /= 0 then
         X := 1;
      end if;
      raise Program_Error; -- legal
   end Aborting;

   procedure P2 is
   begin
      if X = 1 then
         Aborting; -- illegal
         X := X + 2;
      end if;
   end P2;

   procedure P3 is
   begin
      if X = 1 then
         Aborting; -- illegal
      elsif X = 2 then
         X := X + 1;
      end if;
   end P3;

   procedure P4 is
   begin
      if X = 1 then
         Aborting; -- illegal
      else
         X := X + 1;
      end if;
   end P4;

   procedure P5 is
   begin
      X := X + 1;
      Aborting; -- illegal
   end P5;

end No_Return_Illegal;
