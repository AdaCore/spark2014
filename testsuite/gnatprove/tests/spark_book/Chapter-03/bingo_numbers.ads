package Bingo_Numbers is

-- This package defines BINGO numbers and their associated letters

   -- The range of numbers on a Bingo Card
   type Bingo_Number is range 0 .. 75;

   -- 0 can't be called, it is only for the Free Play square
   subtype Callable_Number is Bingo_Number range 1 .. 75;

   -- Associations between Bingo numbers and letters
   subtype B_Range is Bingo_Number range  1 .. 15;
   subtype I_Range is Bingo_Number range 16 .. 30;
   subtype N_Range is Bingo_Number range 31 .. 45;
   subtype G_Range is Bingo_Number range 46 .. 60;
   subtype O_Range is Bingo_Number range 61 .. 75;

   -- The 5 Bingo letters
   type Bingo_Letter is (B, I, N, G, O);

end Bingo_Numbers;
