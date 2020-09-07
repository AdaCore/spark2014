procedure Conv is

   subtype I128 is Long_Long_Long_Integer;
   type U128 is mod 2**128;

   I : I128 := 0;
   U : U128 := 0;
   F : Float := 0.0;
   D : Long_Float := 0.0;

begin
   pragma Assert (I = 0);
   pragma Assert (U = 0);
   pragma Assert (F = 0.0);
   pragma Assert (D = 0.0);

   I := I128(F);
   U := U128(D);
   F := Float(U);
   D := Long_Float(I);

   pragma Assert (I = 0);
   pragma Assert (U = 0);
   pragma Assert (F = 0.0);
   pragma Assert (D = 0.0);

end Conv;
