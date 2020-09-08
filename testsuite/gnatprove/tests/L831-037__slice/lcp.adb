with Types; use Types;

function LCP (A : Text; X, Y : Integer) return Natural
  with SPARK_Mode
is
   L : Natural;
begin
   L := 0;
   while X <= A'Last - L
     and then Y <= A'Last - L
     and then A (X + L) = A (Y + L)
   loop
      pragma Loop_Invariant (X <= A'Last - L);
      pragma Loop_Invariant (Y <= A'Last - L);
      pragma Loop_Invariant (A (X .. X + L) = A (Y .. Y + L));
      pragma Loop_Variant (Increases => L);

      L := L + 1;
   end loop;

   return L;
end LCP;
