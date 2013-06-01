package Test is

  procedure Set_Zero (X : in out Integer)
    with Post => X = 0;

end Test;
