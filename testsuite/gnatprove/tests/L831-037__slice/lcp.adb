with Types; use Types;

function LCP (A : Text; X, Y : Integer) return Natural
  with SPARK_Mode
is
   L : Natural;
begin
   L := 0;
   while X + L <= A'Last
     and then Y + L <= A'Last
     and then A (X + L) = A (Y + L)
   loop
      pragma Loop_Invariant (A (X .. X + L - 1) = A (Y .. Y + L - 1));
      pragma Loop_Variant (Increases => L);

      L := L + 1;
   end loop;

   return L;
end LCP;
