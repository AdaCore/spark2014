package Test is

  Y : Integer;

  procedure P1
    with Pre => (Y > 0);

  procedure P2
    with Pre => (Y > 2);
end Test;
