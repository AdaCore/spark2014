package body T1Q6
is

  procedure Raise_To_Power(X: in Integer; Y: in Natural; Z: out Integer)
  is
    A, C: Integer;
    B: Natural;
  begin
    A := X;
    B := Y;
    C := 1;
    while B > 0
    --# assert C*(A**B) = X**Y and
    --#   X**Y in Integer;
    loop
      pragma Loop_Invariant ((C*(A**B) = X**Y) and
                       (X**Y in Integer));
      if B mod 2 = 0 then
        B := B / 2;
        A := A * A;
      else
        B := B - 1;
        C := C * A;
      end if;
    end loop;
    Z := C;
  end Raise_To_Power;

end T1Q6;
