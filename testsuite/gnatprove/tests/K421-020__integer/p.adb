procedure P (X, Y : Integer) is
   -- pragma Annotate (gnatprove, Force);

   subtype S1 is Integer range 1 .. 10;
   Tmp1 : S1;

   type S2 is new Integer range 1 .. 10;
   Tmp2 : S2;

   Tmp3 : Integer range 1 .. 5;
   Tmp4 : S1 range 1 .. 5;
   Tmp5 : S2 range 1 .. 5;

begin
   Tmp1 := X;
   Tmp2 := S2(Y);

   Tmp3 := 5;
   Tmp4 := 5;
   Tmp5 := 5;

   for K in Integer range 1 .. 10 loop
      Tmp1 := K;
   end loop;
end;
