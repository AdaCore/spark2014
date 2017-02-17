package body Find is
   function Find (T : A; R : Integer) return Integer is
      Res : Integer := 0;
   begin
      for I in T'Range loop
         pragma Loop_Invariant (Res = 0);
         if T (I) = R then
            Res := I;
            exit;
         end if;
      end loop;
      return Res;
   end Find;
end Find;
