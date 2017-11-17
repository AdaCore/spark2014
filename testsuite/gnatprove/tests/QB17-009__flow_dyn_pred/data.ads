package Data
is
   type Value_Array is array (1 .. 10) of Integer range 0 .. 10;

   Values : Value_Array := (others => 0);

end Data;
