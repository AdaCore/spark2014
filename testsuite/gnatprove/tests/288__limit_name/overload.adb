package body Overload is

  procedure Over (X : in out T) is
  begin
    X := X + 1;
  end Over;

  procedure Over (X : in out U) is
  begin
    X := X + 1;
  end Over;
end Overload;
