package R is
    type Arr is array (Integer range <>) of Integer;

    procedure Half (A : in out Arr) with
      Pre => A'First = 1 and A'Last >= 1;
end R;
