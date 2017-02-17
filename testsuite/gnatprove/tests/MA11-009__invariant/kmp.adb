package body Kmp
   with SPARK_Mode
is

   function Init_Next (P : A) return A is
      Next : A (P'Range) := (others => 0);
      I : Integer := P'First;
      J : Integer;
   begin
      if P'Length > 1 then
         J := P'First + 1;
         while I in P'First .. P'Last - 1 loop
            pragma Loop_Invariant
               (J in P'Range and I < J);
            pragma Loop_Invariant
               (P (I - J .. J) = P (0 .. J - 1));
            if P (I) = P (J) then
               I := I + 1;
               J := J + 1;
               Next (I) := J;
            elsif J = P'First then
               I := I + 1;
               Next (I) := 0;
            else
               J := Next (J);
            end if;
         end loop;
      end if;
      return Next;
   end Init_Next;

end Kmp;
