package body Foo
is

   type Index_T is mod 2 ** 64;
   type Byte_T  is mod 2 ** 8;
   type Array_T is array (Index_T range <>) of Byte_T;

   --  Simple test showing an inefficient array length comparison if the
   --  index type is modular. If we convert everything to int this is very
   --  slow, but if we stay in the bv theory then this can be very fast.
   procedure Test_01 (X : out Array_T)
   with Global => null
   is
   begin
      X := (others => 0);
   end Test_01;

end Foo;
