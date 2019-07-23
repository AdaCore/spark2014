package body Lib is

   procedure Empty is
   begin
#if SNEAK_EFFECT
      X := 1;
#end if;
      null;
   end Empty;

end Lib;
