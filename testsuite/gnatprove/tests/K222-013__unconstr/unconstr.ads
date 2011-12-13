package Unconstr is
   type MyInt is range 0 .. 10;
   type Vec is array(Integer range <>) of MyInt;
   type Vec_10 is new Vec (0 .. 10);
   subtype Vec_10_Sub is Vec (0 .. 10);

   procedure P (X : out Vec)
      with Pre => (X'Length > 0),
           Post => (X (X'First) = 0);
end Unconstr;
