package body T1Q5
is

  procedure Bounded_Add(X,Y: in Integer; Z: out Integer)
  is
  begin
    if X < 0 and Y < 0 then -- both negative

      if X < Integer'First - Y then
        Z := Integer'First;
      else
        Z := X + Y;
      end if;

    elsif X > 0 and Y > 0 then -- both positive

      if X > Integer'Last - Y then
        Z := Integer'Last;
      else
        Z := X + Y;
      end if;

    else -- one +ve, one -ve: must be safe to add them

      Z := X + Y;

    end if;
  end Bounded_Add;

end T1Q5;
