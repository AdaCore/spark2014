package P is

    type u1 is mod 2 ** 8;
    type u2 is mod 2 ** 16;
    type u4 is mod 2 ** 32;
    type f8 is new Long_Float;

    -- Shift Left For u4
    function Shift_Left (value : u4; amount : Natural) return u4
      with Import => True,
      Convention => Intrinsic,
      Static;

    -- Shift Right For u4
    function Shift_Right (value : u4; amount : Natural) return u4
      with Import => True,
      Convention => Intrinsic,
      Static;

    type u1array_u1 is array(u1 range<>) of u1;

    function Sft2Dbl (x: u1) return f8 is
      (f8 (u4'(1) * Shift_Left (2, Natural (x)))) with Static;

    function Func1 (x: u1) return u1 is (x and 16#44#) with Static;

    F : F8 := Sft2Dbl (2);
    X : U1 := Func1 (36);

    N : constant := Shift_Left (2, 7);

    CONST_1 : Constant f8 := 10.0 * 1.5 * f8 (Shift_Left (u4 (1), Natural (8)));

end P;
