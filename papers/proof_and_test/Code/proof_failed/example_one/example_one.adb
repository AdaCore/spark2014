package body Example_One is
   function Exponentiation (Var : Integer ; N : Natural) return Integer is
      Temp : Integer := Var;
   begin
      if N = 0 then
         return 1;
      end if;

      for I in 2 .. N loop
         Temp := Var * Temp;  --  overflow check not proved

         pragma Loop_Invariant (Temp = Var ** I);
      end loop;
      return Temp;
   end Exponentiation;
end Example_One;
