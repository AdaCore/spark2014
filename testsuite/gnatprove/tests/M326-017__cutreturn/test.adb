package body Test is

  procedure Set_Zero (X : in out Integer) is
  begin
    if X = 0 then
      return;
    end if;
    pragma Assert_And_Cut (X /= 0);
    X := 0;
    return;
  end Set_Zero;

end Test;
