package body Test is

  function Test (X : Integer) return Integer
  is
  begin
    if X = 0 then
      return 0;
    else
      return 1;
    end if;
  end Test;

end Test;
