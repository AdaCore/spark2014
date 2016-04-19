package Aggr is

   type Word32 is mod 2**32;
   subtype Big_Int_Range is Integer range 0 .. 100;
   Max_Coord_Length : constant := 42;

   type Big_Int is array (Big_Int_Range range <>) of Word32;

   subtype Coord_Index is Natural range 0 .. Max_Coord_Length - 1;
   subtype Coord is Big_Int (Coord_Index);

   One : constant Coord := Coord'(1, others => 0);

end Aggr;
