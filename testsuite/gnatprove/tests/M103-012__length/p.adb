procedure P is

  type A is array (Integer range <>) of Integer;

  subtype B is A(1..10);

  procedure Q (X : A) is
    Y : B := B (X);
  begin
    null;
  end Q;

begin
  null;
end P;
