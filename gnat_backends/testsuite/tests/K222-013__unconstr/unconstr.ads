package Unconstr is
   type MyInt is range 0 .. 10;
   type Vec is array(Integer range <>) of MyInt;
   type Vec_10 is new Vec (0 .. 10);

end Unconstr;
