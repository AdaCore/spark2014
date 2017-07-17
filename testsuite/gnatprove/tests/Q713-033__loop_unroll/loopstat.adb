procedure Loopstat with SPARK_Mode is
   K : Integer;
   type T is array (1 .. 10) of Integer;
   A : T;

begin
   K := 0;
   for J in 1 .. 10 loop
      K := K + 1;
   end loop;
   pragma Assert (K = 10);

   K := 0;
   for I in 1 .. 10 loop
      for J in 1 .. 10 loop
         K := K + 1;
      end loop;
   end loop;
   pragma Assert (K = 100);

   for J in A'Range loop
      A(J) := J;
   end loop;
   pragma Assert (for all K in A'Range => A(K) = K);
end Loopstat;
