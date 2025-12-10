with Ada.Unchecked_Conversion;

package UC_Align is

  type U8 is mod 2 ** 8;
  type Ar is array (1 .. 4) of U8;

  type U32 is mod 2 ** 32 with Alignment => 0;

  function My_UC is new Ada.Unchecked_Conversion (Ar, U32);
end UC_Align;
