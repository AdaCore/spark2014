with Types; use Types;

function LCP (A : Text; X, Y : Integer) return Integer is
   L : Natural := 0;
begin
   for J in A'Range loop
      if X + L not in A'Range
        or else Y + L not in A'Range
      then
         return L;
      end if;

      if A (X + L) /= A (Y + L) then
         return L;
      end if;

      L := L + 1;
   end loop;

   return L;
end LCP;
