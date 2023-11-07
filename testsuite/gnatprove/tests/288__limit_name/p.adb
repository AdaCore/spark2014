package body P is

  procedure Proc (X : in out Integer) is
  begin
    X := X + 1;
  end Proc;

  procedure Unique (X : in out Integer) is
  begin
    X := X + 1;
  end Unique;
end P;
