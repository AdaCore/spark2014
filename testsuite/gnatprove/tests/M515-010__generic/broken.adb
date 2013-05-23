package body Broken is
   package body External_Generic
   is
      procedure Fill_Empty_Slots is
      begin
         if Is_Empty then
            null;
         end if;
      end Fill_Empty_Slots;
   end External_Generic;

   function Found_None return Boolean
   is
   begin
      return True;
   end Found_None;

   package Fruit_Crates is new External_Generic (Is_Empty => Found_None);
end Broken;
