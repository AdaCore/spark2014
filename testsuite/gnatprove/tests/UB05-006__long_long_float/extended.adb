procedure Extended is
   X : Long_Long_Float := 0.0;
   Y : Integer := 1;

   F  : Float := 0.0;
   LF : Long_Float := 0.0;

   type U8 is mod 2**8;
   X8 : U8 := 0;

   type U16 is mod 2**16;
   X16 : U16 := 0;

   type U32 is mod 2**32;
   X32 : U32 := 0;

   type U64 is mod 2**64;
   X64 : U64 := 0;

begin
   pragma Assert (X = 0.0);
   pragma Assert (Long_Long_Float'Pred (X) < 0.0);
   pragma Assert (Long_Long_Float'Succ (X) > 0.0);

   pragma Assert (X /= Long_Long_Float (Y));
   pragma Assert (X = Long_Long_Float (Y) - 1.0);

   pragma Assert (LF = Long_Float (F));
   pragma Assert (X = Long_Long_Float (F));
   pragma Assert (X = Long_Long_Float (LF));

   pragma Assert (Float (LF) = F);
   pragma Assert (Float (X) = F);
   pragma Assert (Long_Float (X) = LF);

   pragma Assert (X = Long_Long_Float (X8));
   pragma Assert (X = Long_Long_Float (X16));
   pragma Assert (X = Long_Long_Float (X32));
   pragma Assert (X = Long_Long_Float (X64));

   pragma Assert (U8 (X) = X8);
   pragma Assert (U16 (X) = X16);
   pragma Assert (U32 (X) = X32);
   pragma Assert (U64 (X) = X64);
end Extended;
