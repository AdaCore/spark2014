procedure P is
  type A is array (Integer range <>) of Integer;

  type B is array (Positive range <>) of Integer;

  procedure Q (X : A) is
    Y : B := B (X);
  begin
    null;
  end Q;

  T : A (-10 .. 1000) := (others => 0);
begin
  Q (T);
end P;
