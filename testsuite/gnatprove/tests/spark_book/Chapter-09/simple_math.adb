pragma SPARK_Mode;

package body Simple_Math is

   function Square_Root(N : Square_Root_Domain) return Square_Root_Range is
      Q : Square_Root_Domain;
      R : Square_Root_Domain;
   begin
      Q := N;
      if Q > 0 then
         loop
            R := N/Q;
            exit when Q <= R;
            Q := (Q + R)/2;
         end loop;
      end if;
      return Q;
   end Square_Root;

end Simple_Math;
