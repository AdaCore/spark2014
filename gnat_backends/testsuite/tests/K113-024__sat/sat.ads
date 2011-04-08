package Sat is

   type My_Int_Base is range 0 .. 20_000;
   subtype My_Int is My_Int_Base range 0 .. 10_000;

   function Add (X , Y : My_Int) return My_Int
      with Post =>
         ((X + Y < 10_000 and then Add'Result = X + Y) or else
         (X + Y >= 10_000 and then Add'Result = 10_000));

end Sat;
