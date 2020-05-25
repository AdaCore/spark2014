pragma SPARK_Mode;

with Types;

procedure Test is
   type U64 is mod 2**64;
   function Extract_U64 is new Types.Extract_Mod (U64);
begin
   null;
end Test;
