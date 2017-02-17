with Q;
with T;

use type T.Input_T;
use type T.Output_T;

procedure Test
is
   pragma SPARK_Mode (On);
   Value : T.Output_T;
begin
   Q.Convert (
      0,
      0.75,
      Value);
   pragma Assert (Value in -0.0001 .. +0.0001);

   Q.Convert (
      2 ** 16 - 1,
      0.25,
      Value);
   pragma Assert (Value in -0.0015 .. -0.001);

   Q.Convert (
      32766,
      0.3,
      Value);
   pragma Assert (Value >= 31.999);  -- and <= 32.0, or 32.001, say?
end Test;

