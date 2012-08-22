package body Reader is

   Counter : Natural := 4;

   function Common_Reader return Segway.Input is
   begin
      if Counter = 0 then
         Counter := 4;
      end if;
      Counter := Counter - 1;
      return Segway.Input'Val (Counter);
   end Common_Reader;
end Reader;
