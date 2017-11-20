package body Example with SPARK_Mode is

   subtype S_T is Long_Float range 0.0 .. 1.0;

   procedure Test is
      R : S_T := 0.5;
   begin
      for Jj in 1 .. 24 loop
         pragma Loop_Invariant (R = 0.5**Jj);

         R := 0.5 * R;
         pragma Assert (0.5*(0.5**Jj) = 0.5**(Jj + 1));
      end loop;
   end Test;

end Example;
