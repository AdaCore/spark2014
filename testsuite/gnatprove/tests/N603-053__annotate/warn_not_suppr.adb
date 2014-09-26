package body Warn_Not_Suppr is

   procedure P (C : Boolean; X : out Integer) is
   begin
      if C then
         X := 1;
      end if;
   end P;

end Warn_Not_Suppr;

