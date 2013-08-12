package body Proven is
   --------------
   -- Is_Prime --
   --------------
   function Is_Prime (N : Natural) return Boolean is
   begin
      for I in 2 .. N / 2 loop
         if not (N mod I /= 0) then
            return False;
         end if;

         pragma Loop_Invariant (for all J in 2 .. I => N mod J /= 0);
      end loop;

      return True;
   end Is_Prime;

   -----------------
   -- Are_Coprime --
   -----------------
   function Are_Coprime (X, Y : Natural) return Boolean is
   begin
      for I in 2 .. Integer'Min (X, Y) loop
         if not (X mod I /= 0 and Y mod I /= 0) then
            return False;
         end if;

         pragma Loop_Invariant (for all J in 2 .. I =>
                                  X mod J /= 0 and Y mod J /= 0);
      end loop;

      return True;
   end Are_Coprime;

   ---------------
   -- Factorial --
   ---------------
   function Factorial (N : Natural) return Non_Zero_Natural is
   begin
      if N = 0 or N = 1 then
         return 1;
      else
         pragma Assume (Factorial (N - 1) <= 362880);  --  9! = 362880
         return N * Factorial (N - 1);
      end if;
   end Factorial;
end Proven;
