with System;

package P is
  type Array_from_C is array (Integer range <>) of Integer;

  function F return System.Address with Import;

  Address_from_C : System.Address := F;
  v : Array_from_C(0 .. 5) with Address => Address_from_C;
end P;
