pragma SPARK_Mode;

with T;

procedure M is
   type U64 is mod 2**64;
   function Extract_U64 is new T.Extract_Mod (U64);
begin
   null;
end M;
