with Interfaces; use Interfaces;

procedure U
   with SPARK_Mode
is
    function V (B : Boolean) return Float is
       (if B then 0.1 else -0.1);

    X : Float := V(True);
    Y : Float := V(False);
begin
    pragma Assert (X = 0.1);
    pragma Assert (Y = -0.1);
end U;
