package body Gen2 is

  procedure My_Incr (X : in out T) is
  begin
    G1.Incr (X);
    X := X - 1;
  end My_Incr;

end Gen2;
