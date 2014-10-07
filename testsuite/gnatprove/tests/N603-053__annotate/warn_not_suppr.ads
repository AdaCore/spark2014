package Warn_Not_Suppr is

   --  a pragma Warnings(Off) should not suprress this check
   pragma Warnings (Off);
   procedure P (C : Boolean; X : out Integer);
   pragma Warnings (On);

end Warn_Not_Suppr;
