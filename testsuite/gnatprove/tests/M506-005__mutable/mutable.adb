package body Mutable is
  procedure Simple (X : T) is
    Z : Integer;
  begin
    if X.K > 0 then
      Z := X.Arr (1);
    end if;
  end Simple;

  procedure Change (X : in out T) is
  begin
      X := (5, 3, (others => 0));
  end Change;

  procedure Modify (X : in out T) is
    Z : Integer;
  begin
    if X.K > 0 then
      null;
    else
      Change (X);
    end if;
    Z := X.Arr (1);
  end Modify;

end Mutable;
