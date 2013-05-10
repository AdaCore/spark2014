procedure P (X, Y : Integer) is


   subtype S1 is Integer range 1 .. 10;
   type A1 is array (Integer range 1 .. 10) of Integer range 1 .. 10;
   Tmp1 : A1;

   type S2 is new Integer range 1 .. 10;

   Tmp3 : array (Integer range 1 .. 5) of Integer range 1 .. 5;
   Tmp4 : array (S1 range 1 .. 5) of S1 range 1 .. 5;
   Tmp5 : array (S2 range 1 .. 5) of S2 range 1 .. 5;

begin
   Tmp1 (1) := X;

   Tmp3 (1) := 5;
   Tmp4 (1) := 5;
   Tmp5 (1) := 5;

   for K in Integer range 1 .. 10 loop
      Tmp1 (1) := K;
   end loop;
end;
