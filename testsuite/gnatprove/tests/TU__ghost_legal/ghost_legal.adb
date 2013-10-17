package body Ghost_Legal is
   function Is_Even (X : Natural) return Boolean is
      (X mod 2 = 0);


   function Is_Prime (X : Natural) return Boolean is
      Temp : Natural;
   begin
      if (X mod 2) = 0 then
         pragma Assert_And_Cut (Is_Even (X));
         return False;
      end if;

      Temp := 2;
      while Temp < X loop
         pragma Loop_Invariant (Temp >= 2);

         if (X mod Temp) = 0 then
            return False;
         end if;

         Temp := Temp + 1;
      end loop;
      return True;
   end Is_Prime;
end Ghost_Legal;