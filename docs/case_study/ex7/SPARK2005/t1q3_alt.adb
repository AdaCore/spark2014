package body T1Q3_Alt
is

  procedure Swap(X,Y: in out Integer)
  is
    Temp: Integer;
  begin
    Temp := X;
    X := Y;
    Y := Temp;
  end Swap;

  procedure NandGate(P,Q: in Boolean; R: out Boolean)
  is
  begin
    if P and Q then
      R := false;
    else
      R := true;
    end if;
  end NandGate;

  procedure NextDay_A(Today: in Day; Tomorrow: out Day)
  -- This is implementation (a) of NextDay, in which Day'Succ is used
  is
  begin
    if Today = Sun then
      Tomorrow := Mon;
    else
      Tomorrow := Day'Succ(Today);
    end if;
  end NextDay_A;

  procedure NextDay_B(Today: in Day; Tomorrow: out Day)
  -- This is implementation (b) of NextDay, in which a case-statement is used
  is
  begin
    case Today is
      when Mon => Tomorrow := Tue;
      when Tue => Tomorrow := Wed;
      when Wed => Tomorrow := Thu;
      when Thu => Tomorrow := Fri;
      when Fri => Tomorrow := Sat;
      when Sat => Tomorrow := Sun;
      when Sun => Tomorrow := Mon;
    end case;
  end NextDay_B;

end T1Q3_Alt;
