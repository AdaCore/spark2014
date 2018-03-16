package body Math_Utils is

   ---------
   -- Max --
   ---------

   function Max (V : Vector) return Integer
     with SPARK_Mode
   is
      Result : Integer := Integer'First;
   begin
      pragma Assert (V'Length > 0);

      for I in V'Range loop
         if V (I) > Result then
            Result := V (I);
         end if;

         pragma Assert (I in V'Range);
         pragma Loop_Variant (Increases => I);
         pragma Loop_Invariant
           (for all K in V'First .. I => Result >= V (K));
         pragma Loop_Invariant
           (for some K in V'First .. I => Result = V (K));
      end loop;

      pragma Assert (for Some E of V => Result = E);

      return Result;
   end Max;

end Math_Utils;
