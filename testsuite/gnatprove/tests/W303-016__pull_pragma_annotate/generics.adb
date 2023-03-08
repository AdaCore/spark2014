package body Generics with SPARK_Mode => Off is

   procedure Terminating_Generic is
   begin
      while X > -36 loop
         if Y >= 0 or else X < 0 then
            X := X - 42;
         else
            X := X + Y;
         end if;
      end loop;
   end Terminating_Generic;
   
   procedure Terminating_Instance_Builder is
   begin
      while X < -41 loop
         if Y <= 0 then
            X := X + 1;
         else
            X := X + Y;
         end if;
      end loop;
   end Terminating_Instance_Builder;

end Generics;
