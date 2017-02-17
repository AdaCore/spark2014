package body Test2 is

  function Test (X : Integer) return Integer
  is
    Result : Integer := 0;
  begin
    if X = 0 then
      Result := 0;
    else
      Result := 1;
    end if;
    return Result;
  end Test;

end Test2;
