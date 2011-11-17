package P1 is
   subtype Index is Integer range 0 .. 1_000_000;
   type Arr is array (Index range <>) of Boolean;
   procedure Two_Way_Sort (A : in out Arr);
end P1;
