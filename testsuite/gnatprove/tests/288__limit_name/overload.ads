package Overload is

  type T is range 1 .. 100;
  type U is range 1 .. 200;

  procedure Over (X : in out T);
  procedure Over (X : in out U);
end Overload;
