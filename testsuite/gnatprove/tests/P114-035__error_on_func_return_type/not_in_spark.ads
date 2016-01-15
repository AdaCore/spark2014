package Not_In_SPARK
  with SPARK_Mode => Off
is
   type T is new Integer;

   type Ind1 is new Integer range 1 .. 3;
   type Ind2 is new Integer range 1 .. 3;
   type Ind3 is new Integer range 1 .. 3;
end;
