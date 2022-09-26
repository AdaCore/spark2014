with Ada.Numerics.Elementary_Functions;
procedure Repr with SPARK_Mode is

  subtype nn_float is Float range 0.0 .. Float'Last;

  function norm(v: nn_float) return nn_float is
    (Ada.Numerics.Elementary_Functions.Sqrt(v)); --@RANGE_CHECK:PASS

begin
   null;
end Repr;
