with Interfaces; use Interfaces;
function Saturate (Val : Unsigned_16) return Unsigned_16
  with SPARK_Mode,
       Post => Saturate'Result < 256
is
   Mask : constant Unsigned_16 := 16#0FFF#;
begin
   return Val and Mask;
end Saturate;
