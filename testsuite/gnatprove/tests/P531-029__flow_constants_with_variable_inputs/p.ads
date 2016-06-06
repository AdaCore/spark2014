package P
with SPARK_Mode => On is

   procedure any (a : in integer; b : out integer) with Depends => (B => A);

end P;
