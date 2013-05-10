package body Const is
  procedure Simple (X : T) is
    Z : Integer;
  begin
    if X.K > 0 then
      Z := X.Arr (1);
    end if;
  end Simple;

  procedure Change (X : in out T) is
  begin
    X.Som := 3;
  end Change;

  procedure Modify (X : in out T) is
    Z : Integer;
  begin
    if X.K <= 0 then
      null;
    else
      Change (X);
      Z := X.Arr (1);
    end if;
  end Modify;

end Const;
