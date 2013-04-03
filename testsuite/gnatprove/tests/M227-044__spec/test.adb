package body Test is

  X : Integer := 0;

  procedure P1 is
  begin
    X := 1;
  end P1;

  procedure P2 is
  begin
    X := 0;
    P1;
    pragma Assert (X = 0);
  end P2;

end Test;
